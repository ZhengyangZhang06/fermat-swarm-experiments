"""Collect local, read-only observations; never call the broker or verifier."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
from urllib.parse import urlsplit

ROUND = Path(__file__).resolve().parent
ROOT = Path.cwd()
REQUEST = 'dd68dd8a2e544dc896fe934231484345'
SHA = '5ac520c36a3e8629d2403b56926f2f4b50c1f85c'
RUNTIME = Path('/runtime/flows/math-lean-flow')
WRAPPER = RUNTIME / 'scripts/swarm-compare.py'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def git(path, *args):
    return subprocess.check_output(['git', '--no-optional-locks', '-C', str(path), *args])

current_wrapper = WRAPPER.read_bytes()
matches = []
for path in sorted(Path('/runtime/flows').glob('*/scripts/swarm-compare.py')):
    if path != WRAPPER and path.read_bytes() == current_wrapper:
        matches.append(str(path))

endpoint = os.environ.get('HUMANIZE_SWARM_ENDPOINT')
endpoint_observation = {'override_present': endpoint is not None}
if endpoint:
    parsed = urlsplit(endpoint)
    endpoint_observation.update(
        sha256=digest(endpoint.encode()),
        scheme=parsed.scheme,
        contains_credentials=bool(parsed.username or parsed.password),
        contains_query=bool(parsed.query or parsed.fragment),
    )
    if not (parsed.username or parsed.password or parsed.query or parsed.fragment):
        endpoint_observation['origin'] = parsed.scheme + '://' + parsed.netloc

mount_observations = []
for line in Path('/proc/self/mountinfo').read_text().splitlines():
    fields = line.split()
    if fields[4] in {str(WRAPPER), '/runtime', '/runtime/review-evidence', str(RUNTIME)}:
        mount_observations.append({
            'source_subpath': fields[3], 'mountpoint': fields[4],
            'mount_options': fields[5], 'readonly': 'ro' in fields[5].split(',')
        })

archive = Path('/runtime/review-evidence')
matching_archived_requests = []
for receipt in sorted(archive.glob('*/review-export.json')):
    data = json.loads(receipt.read_text())
    if data.get('request_id') == REQUEST or data.get('candidate_commit') == SHA:
        matching_archived_requests.append(str(receipt))

source_revision = '956e8c600d8b95b46948ae5e37b13930b5f3d06b'
frozen_submission = git(ROOT, 'show', source_revision + ':Submission.lean')
contract = ROOT / 'Fermat/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean'
candidate_commit = git(ROOT, 'rev-parse', 'HEAD').decode().strip()
report = {
    'request_id': REQUEST,
    'candidate_commit': candidate_commit,
    'candidate_expected_commit_matches': candidate_commit == SHA,
    'candidate_clean': not git(ROOT, 'status', '--porcelain').strip(),
    'wrapper': {
        'path': str(WRAPPER),
        'runtime_checkout': git(RUNTIME, 'rev-parse', 'HEAD').decode().strip(),
        'sha256': digest(current_wrapper),
        'git_head_wrapper_sha256': digest(git(RUNTIME, 'show', 'HEAD:scripts/swarm-compare.py')),
        'runtime_status': git(RUNTIME, 'status', '--short').decode().splitlines(),
        'identical_mounted_archive_files': matches,
        'endpoint': endpoint_observation,
    },
    'mounts': mount_observations,
    'existing_review_archive': {
        'path': str(archive),
        'request_directory_present': (archive / REQUEST).exists(),
        'matching_request_or_candidate_receipts': matching_archived_requests,
        'exporters': {
            str(path): digest(path.read_bytes())
            for path in sorted(Path('/runtime').glob('operator-review-evidence-*/export-review-evidence.py'))
        },
        'limitation': 'Inspected exporters select only finished requests with returncode zero and verified operation receipts.'
    },
    'local_frozen_sources': {
        'original_submission_sha256': digest(frozen_submission),
        'protected_contract_sha256': digest(contract.read_bytes()),
        'protected_contract_matches_original_submission': contract.read_bytes() == frozen_submission,
        'candidate_submission_sha256': digest((ROOT / 'Submission.lean').read_bytes()),
        'limitation': 'Local source hashes are not a substitute for the unavailable actual remote packet.'
    },
    'unresolved': [
        'Existing failed request operation.json and prepared packet with full source_sha256 map',
        'Actual deployed /verifier code bytes/hashes and request-bound deployment receipt',
        'Operator authorization record for the observed wrapper mount and endpoint origin',
        'Controller-authorized executable challenge correction and successful exact comparator evidence'
    ],
    'network_requests': 0,
    'verifier_runs': 0,
    'acceptance': False
}
destination = ROUND / 'round-1-provenance-audit.json'
destination.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
