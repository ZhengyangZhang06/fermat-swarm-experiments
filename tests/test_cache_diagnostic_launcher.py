import copy
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

SPEC = importlib.util.spec_from_file_location('cache_diagnostic_launcher',
    Path(__file__).resolve().parents[1] / 'scripts/launch-seeded-cache-diagnostics.py')
launcher = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(launcher)


class DiagnosticLauncherTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.directory = Path(self.tmp.name)
        self.node = dict(node='hoa1', node_id='n'*25, seed_service='seed-one',
            seed_service_id='s'*25, diagnostic_service='diagnostic-one')
        self.receipt = dict(status='seeded', archive_sha256='a'*64, reference_cache_digest='b'*64,
            inventory_entries=123, inventory_verified=True, root='/reference', owner=1000, mode='0700')
        self.config = dict(nodes=[self.node], archive_sha256='a'*64, reference_digest='b'*64,
            inventory_entries=123, volume='reference-volume', authorization_label='experiment',
            code_sha256={'/verifier/verify-frozen-node.py':'c'*64})
        self.template = dict(Name='template', Labels={'experiment':'test'}, Mode={'Replicated': {'Replicas':1}},
            TaskTemplate=dict(Runtime='container', Placement={'Constraints':['node.id=='+'z'*25]},
                RestartPolicy={'Condition':'none'}, Resources={'Limits':dict(NanoCPUs=2000000000,
                    MemoryBytes=12884901888, Pids=256)}, ContainerSpec=dict(User='1000:1000', ReadOnly=True,
                    CapabilityDrop=['ALL'], Image='python@sha256:'+'a'*64,
                    Args=['python3','/canary/cache-selftest.py'], Env=[], Mounts=[dict(Type='volume',
                        Source='reference-volume', Target='/reference', ReadOnly=True, VolumeOptions={'NoCopy':True})])))
        self.spec = launcher.diagnostic_spec(self.template, self.node)
        self.service = dict(ID='d'*25, Spec=self.spec)
        self.task = dict(ID='t'*25, ServiceID='d'*25, NodeID='n'*25, Spec=self.spec['TaskTemplate'],
                         Status=dict(State='running', ContainerStatus={'ExitCode':0}))
        self.observed = dict(ID='n'*25, Description={'Hostname':'hoa1'}, Status={'State':'ready'},
                             Spec=dict(Availability='active',Labels={'experiment':'true'}))
        self.seed = dict(service_id='s'*25, task_id='q'*25, receipt=self.receipt)
        self.ledger = Mock()
        self.ledger.reserve_node.return_value = {'state':'reserved'}
        self.good_receipts = [dict(stage='readonly-reference-inventory-passed',uid=1000,reference_cache_digest='b'*64),
            dict(stage='diagnostic-start',uid=1000,verifier_sha256='c'*64),dict(stage='isolation-denied'),
            dict(stage='diagnostic-passed',comparator_cases=10,production_acceptance_enabled=False),
            dict(stage='cache-selftest-passed',reference_cache_digest='b'*64,
                post_test_inventory_verified=True,production_enabled=False)]

    def launch(self, apply=False, existing='', task=None, seed=True, readiness=None):
        def inspect(kind, identity):
            return self.observed if kind == 'node' else self.service
        with patch.object(launcher, 'check_configuration', return_value=self.template), \
             patch.object(launcher, 'inspect', side_effect=inspect), \
             patch.object(launcher, 'verify_seed', return_value=self.seed if seed else None), \
             patch.object(launcher, 'docker', return_value=existing) as docker, \
             patch.object(launcher, 'exact_task', return_value=task or self.task):
            result = launcher.run(self.config, self.directory, apply=apply, ledger=self.ledger,
                                  max_active=1, readiness_directory=readiness)
        return result, docker

    def test_running_seed_never_diagnostic(self):
        result, docker = self.launch(apply=True, seed=False)
        self.assertEqual(result[0]['state'], 'seed-not-successfully-terminal')
        self.ledger.reserve_node.assert_not_called()
        docker.assert_not_called()

    def test_dry_run_does_not_reserve_or_create(self):
        result, docker = self.launch()
        self.assertEqual(result[0]['state'], 'ready-for-reservation')
        self.ledger.reserve_node.assert_not_called()
        self.assertTrue(all(call.args[:2] == ('service','ls') for call in docker.call_args_list))
        self.assertEqual(list(self.directory.iterdir()), [])

    def test_intent_precedes_create_and_replay_never_duplicates(self):
        result, docker = self.launch(apply=True)
        self.assertEqual(result[0]['state'], 'submitted')
        record = launcher.read_record(self.directory / 'hoa1.json')
        self.assertEqual(record['state'], 'submitting')
        self.assertEqual(docker.call_args.args[:2], ('service','create'))
        result, docker = self.launch(apply=True, existing='diagnostic-one')
        self.assertEqual(result[0]['state'], 'submitting')
        self.assertEqual(docker.call_count, 1)
        self.ledger.release_node.assert_not_called()

    def test_proof_owner_wins_capacity_without_create(self):
        self.ledger.reserve_node.return_value = None
        result, docker = self.launch(apply=True)
        self.assertEqual(result[0]['state'], 'waiting-capacity')
        self.assertEqual(docker.call_count, 1)

    def test_uncertain_missing_service_does_not_retry(self):
        self.launch(apply=True)
        result, docker = self.launch(apply=True)
        self.assertEqual(result[0]['state'], 'needs-reconciliation')
        self.assertEqual(docker.call_count, 1)
        self.ledger.release_node.assert_not_called()

    def test_existing_untracked_service_not_adopted(self):
        result, _ = self.launch(apply=True, existing='diagnostic-one')
        self.assertEqual(result[0]['state'], 'needs-reconciliation')
        self.ledger.reserve_node.assert_not_called()

    def test_terminal_pass_requires_matching_post_inventory_receipt(self):
        self.launch(apply=True)
        task = copy.deepcopy(self.task)
        task['Status']['State'] = 'complete'
        with patch.object(launcher, 'json_receipts', return_value=self.good_receipts):
            result, docker = self.launch(apply=True, existing='diagnostic-one', task=task)
        self.assertEqual(result[0]['state'], 'passed')
        self.ledger.release_node.assert_called_once()
        self.assertEqual(docker.call_count, 1)

    def test_every_diagnostic_receipt_is_required_exactly_once(self):
        self.assertTrue(launcher.diagnostic_passed(self.config, self.good_receipts))
        for index in range(len(self.good_receipts)):
            receipts = self.good_receipts[:index] + self.good_receipts[index+1:]
            self.assertFalse(launcher.diagnostic_passed(self.config, receipts))
        self.assertFalse(launcher.diagnostic_passed(self.config, self.good_receipts+[self.good_receipts[0]]))

    def test_readiness_is_written_before_terminal_reservation_release(self):
        readiness = self.directory / 'readiness'
        readiness.mkdir(mode=0o700)
        self.launch(apply=True, readiness=readiness)
        self.assertFalse(launcher.read_record(readiness/'hoa1.json')['verifier_ready'])
        task = copy.deepcopy(self.task)
        task['Status']['State'] = 'complete'
        def release(**kwargs):
            self.assertTrue(launcher.read_record(readiness/'hoa1.json')['verifier_ready'])
        self.ledger.release_node.side_effect = release
        with patch.object(launcher, 'json_receipts', return_value=self.good_receipts):
            result, _ = self.launch(apply=True, existing='diagnostic-one', task=task, readiness=readiness)
        self.assertEqual(result[0]['state'], 'passed')
        self.assertEqual(launcher.read_record(readiness/'hoa1.json')['diagnostic_task_id'], 't'*25)

    def test_lost_readiness_is_rebuilt_only_from_exact_terminal_evidence(self):
        readiness = self.directory / 'readiness'
        readiness.mkdir(mode=0o700)
        self.launch(apply=True, readiness=readiness)
        task = copy.deepcopy(self.task)
        task['Status']['State'] = 'complete'
        with patch.object(launcher,'json_receipts',return_value=self.good_receipts):
            self.launch(apply=True,existing='diagnostic-one',task=task,readiness=readiness)
        (readiness/'hoa1.json').unlink()
        with patch.object(launcher,'json_receipts',return_value=self.good_receipts):
            result,docker=self.launch(apply=True,existing='diagnostic-one',task=task,readiness=readiness)
        self.assertEqual(result[0]['state'],'passed')
        self.assertTrue(launcher.read_record(readiness/'hoa1.json')['verifier_ready'])
        self.assertEqual(docker.call_count,1)
        (readiness/'hoa1.json').unlink()
        result,docker=self.launch(apply=True,existing='',readiness=readiness)
        self.assertEqual(result[0]['state'],'needs-reconciliation')
        self.assertFalse(launcher.read_record(readiness/'hoa1.json')['verifier_ready'])

    def test_inconsistent_terminal_or_rejected_task_never_releases(self):
        self.launch(apply=True)
        for state, code, pid in [('complete',0,99),('failed',1,99),('failed',0,0),('rejected',1,0)]:
            task = copy.deepcopy(self.task)
            task['Status'] = dict(State=state,ContainerStatus=dict(ExitCode=code,PID=pid))
            result, _ = self.launch(apply=True, existing='diagnostic-one', task=task)
            self.assertEqual(result[0]['state'], 'needs-reconciliation')
            self.ledger.release_node.assert_not_called()

    def test_terminal_without_receipt_is_failed_not_production_ready(self):
        self.launch(apply=True)
        task = copy.deepcopy(self.task)
        task['Status']['State'] = 'complete'
        with patch.object(launcher, 'json_receipts', return_value=[]):
            result, _ = self.launch(apply=True, existing='diagnostic-one', task=task)
        self.assertEqual(result[0]['state'], 'failed')
        self.ledger.release_node.assert_called_once()

    def test_seed_receipt_and_spec_are_pinned(self):
        service = copy.deepcopy(self.service)
        service['ID'] = self.node['seed_service_id']
        service['Spec']['Name'] = 'seed-one'
        self.node['seed_spec_sha256'] = launcher.digest(service['Spec'])
        task = copy.deepcopy(self.task)
        task['Status']['State'] = 'complete'
        with patch.object(launcher,'inspect',return_value=service), \
             patch.object(launcher,'exact_task',return_value=task), \
             patch.object(launcher,'json_receipts',return_value=[self.receipt]):
            self.assertEqual(launcher.verify_seed(self.config,self.node)['receipt'],self.receipt)
            self.receipt['inventory_verified'] = False
            with self.assertRaisesRegex(ValueError,'full inventory'):
                launcher.verify_seed(self.config,self.node)

    def test_exact_task_rejects_replacement_wrong_node_or_spec(self):
        with patch.object(launcher,'docker',return_value='t'*25), \
             patch.object(launcher,'inspect',return_value=self.task):
            self.assertEqual(launcher.exact_task(self.service,'n'*25),self.task)
            del self.task['Spec']['Runtime']
            # Service and task do not share mutable dictionaries in real Docker output.
            self.service['Spec']['TaskTemplate'] = dict(self.task['Spec'], Runtime='container')
            self.assertEqual(launcher.exact_task(self.service,'n'*25),self.task)
            self.task['NodeID'] = 'x'*25
            with self.assertRaisesRegex(ValueError,'physical node'):
                launcher.exact_task(self.service,'n'*25)

    def test_unsafe_template_rejected(self):
        command = launcher.create_command(self.spec)
        self.assertIn('--no-resolve-image', command)
        self.assertIn('type=volume,source=reference-volume,destination=/reference,readonly,volume-nocopy', command)
        self.spec['TaskTemplate']['ContainerSpec']['User'] = '0:0'
        with self.assertRaisesRegex(ValueError,'restricted shape'):
            launcher.create_command(self.spec)

    def test_one_node_observation_failure_does_not_block_independent_nodes(self):
        second = dict(self.node,node='hoa2',node_id='m'*25,diagnostic_service='diagnostic-two')
        self.config['nodes'].append(second)
        def inspect(kind, identity):
            if identity == 'n'*25:
                raise OSError('transient node observation failure')
            return dict(self.observed,ID='m'*25,Description={'Hostname':'hoa2'})
        with patch.object(launcher,'check_configuration',return_value=self.template), \
             patch.object(launcher,'inspect',side_effect=inspect), \
             patch.object(launcher,'verify_seed',return_value=self.seed), \
             patch.object(launcher,'docker',return_value=''):
            result=launcher.run(self.config,self.directory,apply=True,ledger=self.ledger,max_active=2)
        self.assertEqual([r['state'] for r in result],['needs-reconciliation','submitted'])

    def test_ambiguous_create_retains_bounded_slot_and_blocks_second_launch(self):
        second = dict(self.node,node='hoa2',node_id='m'*25,diagnostic_service='diagnostic-two')
        self.config['nodes'].append(second)
        def inspect(kind, identity):
            return dict(self.observed,ID=identity,Description={'Hostname':'hoa1' if identity=='n'*25 else 'hoa2'})
        def docker(*args):
            if args[:2] == ('service','create'):
                raise OSError('create response lost')
            return ''
        with patch.object(launcher,'check_configuration',return_value=self.template), \
             patch.object(launcher,'inspect',side_effect=inspect), \
             patch.object(launcher,'verify_seed',return_value=self.seed), \
             patch.object(launcher,'docker',side_effect=docker):
            result=launcher.run(self.config,self.directory,apply=True,ledger=self.ledger,max_active=1)
        self.assertEqual([r['state'] for r in result],['needs-reconciliation','waiting-diagnostic-slot'])
        self.ledger.reserve_node.assert_called_once()
        self.ledger.release_node.assert_not_called()

    def tmpfs(self):
        mount = dict(Type='tmpfs', Target='/tmp', TmpfsOptions=dict(SizeBytes=536870912,Mode=0o1777))
        self.template['TaskTemplate']['ContainerSpec']['Mounts'].append(copy.deepcopy(mount))
        self.spec = launcher.diagnostic_spec(self.template,self.node)
        self.service = dict(ID='d'*25,Spec=copy.deepcopy(self.spec))
        self.task['Spec'] = copy.deepcopy(self.spec['TaskTemplate'])

    def test_omitted_default_tmpfs_mode_reconciles_without_respawn_and_hashes_raw_spec(self):
        self.tmpfs()
        self.launch(apply=True)
        del self.service['Spec']['TaskTemplate']['ContainerSpec']['Mounts'][-1]['TmpfsOptions']['Mode']
        del self.task['Spec']['ContainerSpec']['Mounts'][-1]['TmpfsOptions']['Mode']
        raw_digest = launcher.digest(self.service['Spec'])
        self.assertNotEqual(raw_digest,launcher.digest(self.spec))
        readiness=self.directory/'readiness'
        readiness.mkdir(mode=0o700)
        task=copy.deepcopy(self.task)
        task['Status']['State']='complete'
        with patch.object(launcher,'json_receipts',return_value=self.good_receipts):
            result,docker=self.launch(apply=True,existing='diagnostic-one',task=task,readiness=readiness)
        self.assertEqual(result[0]['state'],'passed')
        self.assertEqual(docker.call_count,1)
        self.assertEqual(launcher.read_record(readiness/'hoa1.json')['diagnostic_spec_sha256'],raw_digest)
        self.assertNotIn('Mode',self.service['Spec']['TaskTemplate']['ContainerSpec']['Mounts'][-1]['TmpfsOptions'])

    def test_explicit_changed_tmpfs_mode_or_other_mount_property_is_rejected(self):
        self.tmpfs()
        self.launch(apply=True)
        options=self.service['Spec']['TaskTemplate']['ContainerSpec']['Mounts'][-1]['TmpfsOptions']
        for key,value in [('Mode',0o755),('SizeBytes',123)]:
            original=options[key]
            options[key]=value
            result,docker=self.launch(apply=True,existing='diagnostic-one')
            self.assertEqual(result[0]['state'],'needs-reconciliation')
            self.ledger.release_node.assert_not_called()
            self.assertEqual(docker.call_count,1)
            options[key]=original

    def test_new_create_emits_explicit_octal_default_mode(self):
        self.tmpfs()
        command=launcher.create_command(self.spec)
        self.assertIn('type=tmpfs,destination=/tmp,tmpfs-mode=1777,tmpfs-size=536870912',command)
        self.spec['TaskTemplate']['ContainerSpec']['Mounts'][-1]['TmpfsOptions']['Mode']=0o755
        with self.assertRaisesRegex(ValueError,'tmpfs mode'):
            launcher.create_command(self.spec)

    def test_task_tmpfs_normalizes_omission_but_not_an_explicit_change(self):
        self.tmpfs()
        options=self.task['Spec']['ContainerSpec']['Mounts'][-1]['TmpfsOptions']
        del options['Mode']
        with patch.object(launcher,'docker',return_value='t'*25), \
             patch.object(launcher,'inspect',return_value=self.task):
            self.assertEqual(launcher.exact_task(self.service,'n'*25),self.task)
            options['Mode']=0o755
            with self.assertRaisesRegex(ValueError,'specification'):
                launcher.exact_task(self.service,'n'*25)


if __name__ == '__main__':
    unittest.main()
