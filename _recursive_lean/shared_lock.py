"""Reentrant process/shared-filesystem locks with stable lock-file inodes.

Cluster deployments must validate flock semantics on their shared filesystem.
Never unlink these files: replacing an inode would create two independent locks.
Processes using these locks must use spawn/exec, not fork while locks are held.
Forking a multithreaded Python worker can inherit locked mutexes/file descriptors.
"""
from __future__ import annotations

import fcntl
import os
from pathlib import Path
import threading


class _LockState:
    def __init__(self):
        self.thread = threading.RLock()
        self.depth = 0
        self.fd = None


_registry_guard = threading.Lock()
_registry: dict[tuple[int, str], _LockState] = {}


class SharedLock:
    """Context-manager lock shared by threads, instances and processes."""

    def __init__(self, path: Path):
        self.path = path.resolve()

    def _state(self):
        # Include PID so a newly constructed lock after fork cannot reuse the
        # parent's reentrancy count or open-file description.
        key = (os.getpid(), str(self.path))
        with _registry_guard:
            return _registry.setdefault(key, _LockState())

    def __enter__(self):
        state = self._state()
        state.thread.acquire()
        try:
            if state.depth == 0:
                self.path.parent.mkdir(parents=True, exist_ok=True)
                fd = os.open(self.path, os.O_CREAT | os.O_RDWR | os.O_CLOEXEC, 0o600)
                try:
                    fcntl.flock(fd, fcntl.LOCK_EX)
                except BaseException:
                    os.close(fd)
                    raise
                state.fd = fd
            state.depth += 1
            return self
        except BaseException:
            state.thread.release()
            raise

    def __exit__(self, *exc):
        state = self._state()
        try:
            state.depth -= 1
            if state.depth == 0:
                try:
                    fcntl.flock(state.fd, fcntl.LOCK_UN)
                finally:
                    os.close(state.fd)
                    state.fd = None
        finally:
            state.thread.release()
