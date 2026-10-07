#!/usr/bin/env python3
"""Controller-local dispatcher for already registered verification requests.

Run against the existing LOCAL ledger only. This cannot grant issue ownership,
register new requests, release workers, or restart running/uncertain checks.
The program path must name an immutable operator-controlled verifier deployment.
"""
import argparse
import json
import os
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from _recursive_lean.distributed_claims import ClaimLedger
from _recursive_lean.remote_verification import VerificationService


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database', required=True, type=Path)
    parser.add_argument('--catalog', required=True, type=Path)
    parser.add_argument('--program', required=True, type=Path)
    parser.add_argument('--once', action='store_true')
    parser.add_argument('--request', help='Explicit queued request to prioritize in --once mode')
    args = parser.parse_args()
    if args.request and not args.once:
        parser.error('--request requires --once')
    if not args.database.is_file() or not args.program.is_file():
        parser.error('the registered ledger and immutable verifier must already exist')
    os.umask(0o077)
    service = VerificationService(ClaimLedger(args.database), args.database.parent / 'verification',
                                  args.program.resolve(), sys.executable, recover_existing=False,
                                  max_workers=1, uncertain_exit_codes=(75,))
    try:
        while True:
            ready = json.loads(args.catalog.read_text()).get('verifier_ready') is True
            if args.request:
                if not ready:
                    raise RuntimeError('verification readiness gate is closed')
                service.execute(args.request)
            else:
                started = service.dispatch_queued(ready=ready)
                if started:
                    print(f'Dispatched registered verification {started[0]}', flush=True)
            if args.once:
                break
            time.sleep(10)
    finally:
        # Do not orphan a local controller process on a routine clean exit.
        service.pool.shutdown(wait=True)


if __name__ == '__main__':
    main()
