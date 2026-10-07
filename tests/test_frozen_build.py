import hashlib
import unittest

from _recursive_lean.frozen_build import prepare_build_copy


def prepare(source, enabled=True):
    return prepare_build_copy(source, hashlib.sha256(source.encode()).hexdigest(),
                              omit_simp_erasures=enabled)


class FrozenBuildTests(unittest.TestCase):
    def test_default_is_byte_exact_and_does_not_enable_repair(self):
        source = 'import Mathlib\nattribute [-simp] Missing.name\ntheorem root : True := by sorry\n'
        result = prepare(source, False)
        self.assertEqual(result['source'], source)
        self.assertEqual(result['original_sha256'], result['build_sha256'])
        self.assertEqual(result['omitted_simp_erasures'], [])

    def test_only_exact_header_erasures_are_removed_and_audited(self):
        before = '/- copyright -/\r\nimport Mathlib\r\n'
        directive = 'attribute [-simp] Rep.coe_tateδneg2_apply compl₂EDSAux_zero\r\n'
        after = 'set_option autoImplicit false\r\nuniverse u\r\ntheorem root : True := by sorry\r\n'
        result = prepare(before + directive + after)
        self.assertEqual(result['source'], before + after)
        self.assertEqual(result['omitted_simp_erasures'], [dict(line=3, text=directive.rstrip())])

    def test_changed_frozen_source_is_rejected_even_if_disabled(self):
        source = 'theorem root : True := by sorry\n'
        digest = hashlib.sha256(source.encode()).hexdigest()
        for enabled in (False, True):
            with self.assertRaisesRegex(ValueError, 'frozen contract digest'):
                prepare_build_copy(source.replace('True', 'False'), digest, omit_simp_erasures=enabled)

    def test_comments_strings_and_proof_text_are_preserved(self):
        source = ('/- outer /- nested -/\nattribute [-simp] Comment.fake\n-/\n'
                  'import Mathlib\nattribute [-simp] Real.name\n'
                  'def text := "hello\nattribute [-simp] String.fake\n"\n'
                  'theorem root : True := by trivial\nattribute [-simp] After.name\n')
        self.assertEqual(prepare(source)['source'], source.replace('attribute [-simp] Real.name\n', ''))

    def test_other_attributes_and_mixed_commands_remain_unchanged(self):
        for command in ('attribute [simp] Some.name', 'attribute [-simp, reducible] Some.name',
                        'attribute [-simp] Some.name -- retained comment',
                        'attribute [-simp] Some.name; axiom bad : False'):
            source = 'import Mathlib\n' + command + '\ntheorem root : True := by sorry\n'
            self.assertEqual(prepare(source)['source'], source)


if __name__ == '__main__':
    unittest.main()
