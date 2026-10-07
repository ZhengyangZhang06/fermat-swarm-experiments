"""Correlation gates for controller-created Swarm verification jobs.

Neither a container's presence nor an exit code is proof evidence by itself.
The controller retains the exact service/task, packet and candidate identities.
"""
import hashlib
import json


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def bind_service(service, request_id, packet_digest, *, service_id=None, spec_digest=None):
    if service_id is not None and service.get('ID') != service_id:
        raise RuntimeError('verification service identity changed')
    spec = service['Spec']
    labels = spec.get('Labels', {})
    if labels.get('fermat.request') != request_id or labels.get('fermat.packet') != packet_digest:
        raise RuntimeError('verification service labels differ from controller request')
    actual = digest(spec)
    if spec_digest is not None and actual != spec_digest:
        raise RuntimeError('verification service specification changed')
    return actual


def terminal_result(task, service_id, *, task_id=None):
    """Return None for live work, an exit code for confirmed terminal work.

    Node loss, shutdown and inconsistent identities require reconciliation;
    they are not authorization to retry a possibly-live process.
    """
    if task.get('ServiceID') != service_id or (task_id is not None and task.get('ID') != task_id):
        raise RuntimeError('verification task identity changed')
    status = task['Status']
    state = status['State']
    if state in {'new', 'allocated', 'pending', 'assigned', 'accepted', 'preparing', 'ready', 'starting', 'running'}:
        return None
    if state not in {'complete', 'failed'}:
        raise RuntimeError(f'verification task requires reconciliation: {state}')
    container = status.get('ContainerStatus', {})
    code = container.get('ExitCode')
    if type(code) is not int or container.get('PID', 0) != 0:
        raise RuntimeError('verification task lacks terminal container evidence')
    if state == 'failed' and code == 0:
        raise RuntimeError('failed verification task cannot report success')
    if state == 'complete' and code != 0:
        raise RuntimeError('complete verification task has inconsistent exit status')
    return code


def verify_result_evidence(evidence, prepared_evidence):
    expected = {**prepared_evidence, 'status': 'verified'}
    if evidence != expected:
        raise RuntimeError('remote verification evidence differs from controller packet')
