"""Shared issue-runtime protocol and short state-refresh critical sections."""
from __future__ import annotations

PROTOCOL = 'shared-theorem-issues-v1'


def enabled(config):
    return getattr(config, 'github_shared_issue_runtime', False) is True


def selected(config, node):
    if not enabled(config):
        return True
    if node.id == 'root' and not node.github_issue_url:
        return config.github_selected_issue == config.github_root_issue_number
    return node.github_issue_url == (
        f'https://github.com/{config.github_repository}/issues/{config.github_selected_issue}'
    )


class RefreshLock:
    """Serialize an operation and refresh its graph before inspecting aliases."""

    def __init__(self, lock, store):
        self.lock, self.store = lock, store

    def __enter__(self):
        self.lock.__enter__()
        try:
            self.store.refresh()
            return self
        except BaseException:
            self.lock.__exit__(None, None, None)
            raise

    def __exit__(self, *exc):
        return self.lock.__exit__(*exc)
