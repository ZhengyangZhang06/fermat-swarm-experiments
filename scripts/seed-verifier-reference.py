#!/usr/bin/env python3
"""Seed an EMPTY node-local reference volume from an operator-pinned plain tar.

The expected manifest digest must come from trusted controller configuration,
not from an archive, issue, worker, or the mirror being seeded. Failure leaves a
nonempty, explicitly incomplete volume: do not blindly retry it. This script
never overwrites an existing reference cache or reseals its manifest.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import tarfile


TREES = {"packages", "lean-4.33.1-linux"}
MARKER = ".reference-seed-receipt.json"


def digest_value(value):
    if not isinstance(value, str) or not re.fullmatch(r"[a-f0-9]{64}", value):
        raise ValueError("expected an operator-supplied SHA-256 digest")
    return value


def clean_path(value, *, directory=False):
    if not isinstance(value, str) or any(c in value for c in ("\0", "\n", "\r", "\\")):
        raise ValueError("unsafe archive path")
    while value.startswith("./"):
        value = value[2:]
    if directory:
        value = value.rstrip("/")
        if value in {"", "."}:
            return ""
    parts = value.split("/")
    if not value or value.startswith("/") or any(p in {"", ".", ".."} for p in parts):
        raise ValueError("unsafe archive path")
    if parts[0] not in TREES and value != "reference.json":
        raise ValueError("archive entry is outside the two reference trees")
    return value


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate reference manifest key")
        result[key] = value
    return result


def lexical_target(name, target):
    if not target or target.startswith("/") or any(c in target for c in ("\0", "\n", "\r", "\\")):
        raise ValueError("reference symlink target must be internal and relative")
    parts = list(PurePosixPath(name).parent.parts)
    for part in target.split("/"):
        if part in {"", "."}:
            continue
        if part == "..":
            if not parts:
                raise ValueError("reference symlink escapes the volume")
            parts.pop()
        else:
            parts.append(part)
    if not parts or parts[0] not in TREES:
        raise ValueError("reference symlink targets an uninventoried path")
    return "/".join(parts)


def validate_links(entries, directories=()):
    links = {name: info["link"] for name, info in entries.items() if "link" in info}
    existing = set(entries) | TREES | set(directories)
    for name in entries:
        existing.update(str(p) for p in PurePosixPath(name).parents if str(p) != ".")
        if any(str(parent) in links for parent in PurePosixPath(name).parents):
            raise ValueError("archive writes beneath a symlink")
    for name, target in links.items():
        current = lexical_target(name, target)
        visited = set()
        while True:
            pieces = current.split("/")
            prefix = next(("/".join(pieces[:i]) for i in range(1, len(pieces) + 1)
                           if "/".join(pieces[:i]) in links), None)
            if prefix is None:
                break
            if prefix in visited:
                raise ValueError("reference symlink cycle")
            visited.add(prefix)
            suffix = current[len(prefix):]
            current = lexical_target(prefix, links[prefix]) + suffix
        if current not in existing or current.split("/")[0] not in TREES:
            raise ValueError("reference symlink target is missing or uninventoried")


def preflight(archive, expected):
    """Inspect every header before extraction; trust only the pinned manifest."""
    members = {}
    with tarfile.open(archive, mode="r:") as source:
        for member in source:
            name = clean_path(member.name, directory=member.isdir())
            if not name:
                continue
            if name in members:
                raise ValueError("duplicate archive entry")
            if member.islnk() or not (member.isdir() or member.issym() or member.isreg()) or member.sparse is not None:
                raise ValueError("archive hardlinks, sparse files, and special files are forbidden")
            if member.mode & 0o7000:
                raise ValueError("special permission bits are forbidden")
            members[name] = member
        manifest = members.get("reference.json")
        if manifest is None or not manifest.isreg() or manifest.size > 128 * 1024 * 1024:
            raise ValueError("missing or invalid reference manifest")
        encoded = source.extractfile(manifest).read()
    if hashlib.sha256(encoded).hexdigest() != expected:
        raise ValueError("reference manifest differs from operator digest")
    record = json.loads(encoded, object_pairs_hook=unique_object)
    if record.get("schema") != 1 or record.get("toolchain") != "v4.33.1" or not isinstance(record.get("files"), dict):
        raise ValueError("unsupported reference manifest")
    entries = record["files"]
    for name, info in entries.items():
        if clean_path(name) != name or name.split("/")[0] not in TREES or not isinstance(info, dict):
            raise ValueError("invalid reference manifest entry")
        if set(info) == {"sha256", "mode"}:
            digest_value(info["sha256"])
            if type(info["mode"]) is not int or not 0 <= info["mode"] <= 0o777:
                raise ValueError("invalid reference file mode")
        elif set(info) == {"link"} and isinstance(info["link"], str):
            lexical_target(name, info["link"])
        else:
            raise ValueError("invalid reference file record")
    validate_links(entries, (name for name, member in members.items() if member.isdir()))
    observed = {}
    for name, member in members.items():
        if name == "reference.json":
            continue
        if member.isdir():
            if name in entries:
                raise ValueError("archive directory replaces a reference file")
            continue
        info = entries.get(name)
        if info is None:
            raise ValueError("archive contains an uninventoried file")
        if member.issym():
            if info != {"link": member.linkname}:
                raise ValueError("archive symlink differs from pinned inventory")
        elif "sha256" not in info or member.mode != info["mode"]:
            raise ValueError("archive file type or mode differs from pinned inventory")
        observed[name] = info
    if observed != entries:
        raise ValueError("archive is missing inventoried files")
    # Directories are not inventoried, but still must not traverse a symlink or
    # replace one of the two required real tree roots.
    for name, member in members.items():
        if name in TREES and not member.isdir():
            raise ValueError("reference tree root must be a real directory")
        if any(str(parent) in entries and "link" in entries[str(parent)] for parent in PurePosixPath(name).parents):
            raise ValueError("archive entry is beneath a symlink")
    headers = {name: (member.type, member.mode, member.size, member.linkname)
               for name, member in members.items()}
    return encoded, entries, headers


class HashingReader:
    def __init__(self, source):
        self.source, self.digest = source, hashlib.sha256()

    def read(self, size=-1):
        value = self.source.read(size)
        self.digest.update(value)
        return value


def inventory(root):
    result = {}
    directories = set()
    for tree in sorted(TREES):
        base = root / tree
        if base.is_symlink() or not base.is_dir():
            raise ValueError("seeded reference tree is missing or a symlink")
        for directory, dirs, files in os.walk(base, followlinks=False):
            for leaf in [*dirs, *files]:
                path = Path(directory) / leaf
                name = path.relative_to(root).as_posix()
                info = path.lstat()
                if stat.S_ISLNK(info.st_mode):
                    result[name] = {"link": os.readlink(path)}
                elif stat.S_ISREG(info.st_mode):
                    with path.open("rb") as source:
                        digest = hashlib.file_digest(source, "sha256").hexdigest()
                    result[name] = {"sha256": digest, "mode": stat.S_IMODE(info.st_mode)}
                elif stat.S_ISDIR(info.st_mode):
                    directories.add(name)
                elif not stat.S_ISDIR(info.st_mode):
                    raise ValueError("seeded reference contains a special file")
    validate_links(result, directories)
    return result


def seed(archive, root, digest, owner):
    digest_value(digest)
    archive, root = Path(archive), Path(root)
    if type(owner) is not int or not 1 <= owner < 2**31:
        raise ValueError("owner must be an explicit positive worker UID/GID")
    if (not archive.is_absolute() or archive.resolve() != archive or archive.is_symlink()
            or not archive.is_file()):
        raise ValueError("archive must be an absolute regular file without symlink ancestors")
    if (not root.is_absolute() or root.resolve() != root or root == Path("/")
            or root.is_symlink() or not root.is_dir()):
        raise ValueError("reference root must be an existing absolute real volume directory")
    if root.stat().st_uid != os.geteuid():
        raise ValueError("empty reference volume must be owned by the seeding operator")
    if archive.is_relative_to(root):
        raise ValueError("archive cannot be inside the destination volume")
    if any(root.iterdir()):
        raise ValueError("reference volume is nonempty; refusing overwrite or blind retry")
    source_stat = archive.stat()
    encoded, expected, headers = preflight(archive, digest)
    # Persist intent exclusively before the first mutation. Even a failed seed
    # stays nonempty and requires an operator to reconcile/discard the volume.
    descriptor = os.open(root / MARKER, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(descriptor, "w") as marker:
        json.dump({"state": "incomplete", "archive": str(archive), "reference_digest": digest}, marker)
        marker.flush()
        os.fsync(marker.fileno())
    if set(p.name for p in root.iterdir()) != {MARKER}:
        raise ValueError("reference volume changed during seeding claim")
    os.chmod(root, 0o700)
    with archive.open("rb") as source:
        reader = HashingReader(source)
        extracted = set()
        with tarfile.open(fileobj=reader, mode="r|") as stream:
            for member in stream:
                name = clean_path(member.name, directory=member.isdir())
                if not name:
                    continue
                if (name in extracted or headers.get(name) != (member.type, member.mode, member.size, member.linkname)
                        or member.sparse is not None):
                    raise ValueError("archive headers changed after validation")
                extracted.add(name)
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
                if member.isdir():
                    path.mkdir(exist_ok=True, mode=0o700)
                elif member.issym():
                    os.symlink(member.linkname, path)
                elif member.isreg():
                    digest_file = hashlib.sha256()
                    with stream.extractfile(member) as contents, path.open("xb") as destination:
                        while chunk := contents.read(1024 * 1024):
                            destination.write(chunk)
                            digest_file.update(chunk)
                        destination.flush()
                        os.fsync(destination.fileno())
                    if name == "reference.json":
                        if digest_file.hexdigest() != digest:
                            raise ValueError("archive manifest changed during extraction")
                        os.chmod(path, 0o600)
                    else:
                        if digest_file.hexdigest() != expected[name]["sha256"]:
                            raise ValueError("archive file bytes differ from pinned inventory")
                        os.chmod(path, expected[name]["mode"])
                else:
                    raise ValueError("archive changed to an unsupported type")
        while reader.read(1024 * 1024):
            pass
        archive_digest = reader.digest.hexdigest()
    if extracted != set(headers):
        raise ValueError("archive entries changed during extraction")
    final_stat = archive.stat()
    if (source_stat.st_dev, source_stat.st_ino, source_stat.st_size, source_stat.st_mtime_ns) != (
            final_stat.st_dev, final_stat.st_ino, final_stat.st_size, final_stat.st_mtime_ns):
        raise ValueError("source archive changed during seeding")
    if (root / "reference.json").read_bytes() != encoded or inventory(root) != expected:
        raise ValueError("seeded destination differs from the pinned complete inventory")
    for directory, dirs, files in os.walk(root, followlinks=False):
        for name in [*dirs, *files]:
            path = Path(directory) / name
            os.chown(path, owner, owner, follow_symlinks=False)
            if path.is_dir() and not path.is_symlink():
                os.chmod(path, 0o700)
    os.chown(root, owner, owner)
    result = {"status": "seeded", "archive_sha256": archive_digest, "reference_cache_digest": digest,
              "inventory_entries": len(expected), "inventory_verified": True, "root": str(root),
              "owner": owner, "mode": "0700"}
    # Retain the exclusive claim even after success. A competing seeder can
    # never acquire it after completing a stale preflight on an initially empty
    # volume. The receipt is outside the inventoried dependency trees.
    receipt_path = root / (MARKER + ".complete.tmp")
    with receipt_path.open("x") as receipt:
        json.dump(result, receipt, sort_keys=True)
        receipt.flush()
        os.fsync(receipt.fileno())
    os.chmod(receipt_path, 0o600)
    os.chown(receipt_path, owner, owner)
    receipt_path.replace(root / MARKER)
    descriptor = os.open(root, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--digest", required=True, type=digest_value)
    parser.add_argument("--owner", required=True, type=int)
    args = parser.parse_args()
    os.umask(0o077)
    print(json.dumps(seed(args.archive, args.root, args.digest, args.owner), sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
