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
from _recursive_lean.remote_dispatch_slot import RemoteDispatchSlot


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database', required=True, type=Path)
    parser.add_argument('--catalog', required=True, type=Path)
    parser.add_argument('--program', required=True, type=Path)
    parser.add_argument('--once', action='store_true')
    parser.add_argument('--request', help='Explicit queued request to prioritize in --once mode')
    parser.add_argument('--remote-node', help='Reserve one durable remote verifier capacity slot')
    parser.add_argument('--remote-directory', type=Path, help='Private operator packet directory')
    args = parser.parse_args()
    if args.request and not args.once:
        parser.error('--request requires --once')
    if bool(args.remote_node) != bool(args.remote_directory):
        parser.error('--remote-node and --remote-directory must be provided together')
    remote_environment = os.environ.get('FERMAT_SWARM_VERIFIER_NODE') or os.environ.get('FERMAT_SWARM_VERIFIER_DIRECTORY')
    if remote_environment and not args.remote_node:
        parser.error('remote adapter configuration requires the durable --remote-node slot')
    if args.remote_node:
        for key, value in (('FERMAT_SWARM_VERIFIER_NODE', args.remote_node),
                           ('FERMAT_SWARM_VERIFIER_DIRECTORY', str(args.remote_directory.absolute()))):
            if key in os.environ and os.environ[key] != value:
                parser.error(f'{key} differs from remote slot configuration')
            os.environ[key] = value
    if not args.database.is_file() or not args.program.is_file():
        parser.error('the registered ledger and immutable verifier must already exist')
    os.umask(0o077)
    service = VerificationService(ClaimLedger(args.database), args.database.parent / 'verification',
                                  args.program.resolve(), sys.executable, recover_existing=False,
                                  max_workers=1, uncertain_exit_codes=(75,))
    try:
        if args.remote_node:
            with RemoteDispatchSlot(service.ledger, args.remote_node, args.remote_directory) as slot:
                while True:
                    ready = json.loads(args.catalog.read_text()).get('verifier_ready') is True
                    if args.request and not ready:
                        raise RuntimeError('verification readiness gate is closed')
                    started = slot.execute_next(service, ready=ready, request_id=args.request)
                    if started:
                        print(f'Dispatched registered remote verification {started}', flush=True)
                    if args.once:
                        break
                    time.sleep(10)
            return
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
