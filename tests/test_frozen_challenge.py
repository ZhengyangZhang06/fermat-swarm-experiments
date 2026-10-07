import importlib.util
import os
from pathlib import Path
import unittest
from unittest.mock import patch


class FrozenChallengeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).resolve().parents[1] / 'scripts/verify-frozen-node.py'
        spec = importlib.util.spec_from_file_location('frozen_checker', path)
        cls.checker = importlib.util.module_from_spec(spec)
        with patch.dict(os.environ, FERMAT_VERIFIER_PROJECT=str(path.parent)):
            spec.loader.exec_module(cls.checker)

    def test_child_restores_frozen_universes_without_replaying_assumptions(self):
        contract = ('import Mathlib\nuniverse u v w\nopen Example\n'
                    'variable (h : False)\ntheorem Root : True := by sorry\n')
        statement = '∀ {V : Type u}, True'
        source = self.checker.child_challenge(contract, 'Submission.Child', statement)
        self.assertEqual(source, 'import Submission\nuniverse u v w\n'
                         'theorem Submission.Child : ∀ {V : Type u}, True := by\n  sorry')
        self.assertNotIn('variable', source)
        self.assertNotIn('open Example', source)

    def test_no_universes_preserves_existing_child_scaffold(self):
        self.assertEqual(self.checker.child_challenge('theorem Root : True := by sorry',
                         'Submission.Child', 'True'),
                         'import Submission\ntheorem Submission.Child : True := by\n  sorry')

    def test_universe_command_cannot_inject_other_commands(self):
        with self.assertRaisesRegex(RuntimeError, 'universe declaration'):
            self.checker.child_challenge('universe u; axiom bad : False', 'Child', 'True')


if __name__ == '__main__':
    unittest.main()
