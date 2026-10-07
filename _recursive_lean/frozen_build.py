"""Disabled-by-default preparation of a derived frozen-contract build copy.

This pure helper has no runtime callers. It never writes the original source.
Enabling the proposed simplifier-directive repair remains an operator decision;
statement equality, dependency checks and axiom checking remain separate gates.
"""
from __future__ import annotations

import hashlib
import re


NAME = r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*"
ERASURE = re.compile(r"attribute\s+\[-simp\]\s+" + NAME + r"(?:\s+" + NAME + r")*")


def prepare_build_copy(source: str, expected_sha256: str, *, omit_simp_erasures=False):
    """Remove only standalone header simp erasures after exact-source validation.

    The complete original bytes must match the controller's frozen digest. The
    audit records every removed line. Comments, string literals, declarations,
    assumptions, imports, options and all proof text are preserved byte-for-byte.
    An unrecognized command is a header boundary, not permission to rewrite it.
    """
    original_hash = hashlib.sha256(source.encode()).hexdigest()
    if original_hash != expected_sha256:
        raise ValueError("source does not match the frozen contract digest")
    output, removed = [], []
    comment_depth, in_string, header = 0, False, True
    for number, line in enumerate(source.splitlines(keepends=True), 1):
        visible, at = [], 0
        while at < len(line):
            pair = line[at:at + 2]
            if comment_depth:
                if pair == '/-':
                    comment_depth += 1
                    at += 2
                elif pair == '-/':
                    comment_depth -= 1
                    at += 2
                else:
                    at += 1
                visible.append(' ')
            elif in_string:
                if line[at] == '\\':
                    at += 2
                elif line[at] == '"':
                    in_string = False
                    at += 1
                else:
                    at += 1
                visible.append(' ')
            elif pair == '--':
                break
            elif pair == '/-':
                comment_depth = 1
                at += 2
                visible.append(' ')
            elif line[at] == '"':
                in_string = True
                at += 1
                visible.append(' ')
            else:
                visible.append(line[at])
                at += 1
        command = ''.join(visible).strip()
        standalone_erasure = (command == line.strip() and ERASURE.fullmatch(command))
        if omit_simp_erasures and header and standalone_erasure:
            removed.append({'line': number, 'text': line.rstrip('\r\n')})
            continue
        output.append(line)
        # Only these top-level metadata forms can precede an erasure. In
        # particular, never rewrite a quoted command inside a declaration.
        if command and not re.match(r'^(import|set_option|universe|open|attribute)\b', command):
            header = False
    derived = ''.join(output)
    return {
        'source': derived,
        'original_sha256': original_hash,
        'build_sha256': hashlib.sha256(derived.encode()).hexdigest(),
        'omitted_simp_erasures': removed,
        'policy': 'omit-header-simp-erasures' if omit_simp_erasures else 'unchanged',
    }
