"""Only certified signal-memory defaults may be restated in a Code update."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import source_view as sv
import test_whole_ledger_export as fixtures


class SignalMemoryDefaultTests(unittest.TestCase):
    BASE = ('abbrev code : Code Bool Unit Unit Unit Unit where\n'
            '  signals := 1\n  initialSignal := 0\n\n')
    ORIGINAL = ('abbrev stale : Code Bool Unit Unit Unit Unit :=\n'
                '  { code with\n    signals := 2\n    initialSignal := 0\n'
                '    readLocal := fun _ snapshot => if 0 < snapshot.stock () then 1 else 0 }\n')
    INSERTION = ('    memoryReady := fun _ => true\n'
                 '    afterSend := fun _ _ old _ => old\n'
                 '    afterDelivery := fun _ _ _ reading => reading\n'
                 '    afterAction := fun _ old _ => old\n')
    TARGET = ORIGINAL.replace('    signals := 2\n', '    signals := 2\n' + INSERTION)

    def rules(self):
        return [{'source_declaration':self.ORIGINAL,'target_declaration':self.TARGET}]

    def test_only_four_default_lines_are_added_and_exact_inverse_recovers_all_bytes(self):
        source = self.BASE + self.ORIGINAL + '\ntheorem downstream : True := True.intro\n'
        expected = self.BASE + self.TARGET + '\ntheorem downstream : True := True.intro\n'
        public = sv.rebind_signal_memory_defaults(source,self.rules())
        self.assertEqual(public,expected)
        self.assertEqual(sv.rebind_signal_memory_defaults(public,self.rules(),reverse=True),source)
        self.assertEqual(sv.rebind_signal_memory_defaults(source,None),source)
        self.assertEqual(sv.rebind_signal_memory_defaults(public,None,reverse=True),public)

    def test_target_cannot_change_head_other_fields_or_certified_default_values(self):
        source = self.BASE + self.ORIGINAL
        for target in [self.TARGET.replace('abbrev stale','def stale'),
                       self.TARGET.replace('initialSignal := 0','initialSignal := 1'),
                       self.TARGET.replace('memoryReady := fun _ => true','memoryReady := fun _ => false'),
                       self.TARGET.replace('afterAction := fun _ old _ => old','afterAction := fun _ _ _ => 0'),
                       self.TARGET.replace('    afterSend := fun _ _ old _ => old\n','')]:
            with self.subTest(target=target),self.assertRaises(sv.ViewError):
                sv.rebind_signal_memory_defaults(source,[dict(self.rules()[0],target_declaration=target)])

    def test_original_base_must_omit_memory_overrides_and_keep_signal_one(self):
        for base in [self.BASE.replace('signals := 1','signals := 2'),
                     self.BASE+'  memoryReady := fun _ => false\n',
                     self.BASE.replace('code :','other :'),self.BASE+self.BASE]:
            with self.subTest(base=base),self.assertRaises(sv.ViewError):
                sv.rebind_signal_memory_defaults(base+self.ORIGINAL,self.rules())

    def test_anchors_must_be_real_unique_commands_not_comments_strings_or_other_defs(self):
        for source in [self.BASE+'/-\n'+self.ORIGINAL+'-/\n',
                       self.BASE+'def message := r#"'+self.ORIGINAL+'"#\n',
                       self.BASE+self.ORIGINAL+self.ORIGINAL,
                       self.BASE+self.ORIGINAL.replace('signals := 2','signals := 3')]:
            with self.subTest(source=source),self.assertRaises(sv.ViewError):
                sv.rebind_signal_memory_defaults(source,self.rules())
        for rule in [{'source_declaration':'def arbitrary : False := by sorry\n','target_declaration':self.TARGET},
                     dict(self.rules()[0],extra='unregistered')]:
            with self.subTest(rule=rule),self.assertRaises(sv.ViewError):
                sv.rebind_signal_memory_defaults(self.BASE+self.ORIGINAL,[rule])
        with self.assertRaises(sv.ViewError):
            sv.rebind_signal_memory_defaults(self.BASE+self.ORIGINAL,self.rules()+self.rules())

    def test_inverse_rejects_missing_mutated_or_duplicate_target(self):
        for source in [self.BASE+self.ORIGINAL,self.BASE+self.TARGET+self.TARGET,
                       self.BASE+self.TARGET.replace('afterDelivery := fun _ _ _ reading => reading','afterDelivery := fun _ _ old _ => old')]:
            with self.subTest(source=source),self.assertRaises(sv.ViewError):
                sv.rebind_signal_memory_defaults(source,self.rules(),reverse=True)

    def test_public_source_view_keeps_repair_while_exact_restores_original(self):
        original=(self.BASE+self.ORIGINAL).encode();public=(self.BASE+self.TARGET).encode()
        with tempfile.TemporaryDirectory() as name:
            root=Path(name);(root/'Example.lean').write_bytes(public)
            row={'path':'Example.lean','source_path':'Lean/Example.lean','source_sha256':sv.sha(original),
                 'target_sha256':sv.sha(public),'view_sha256':sv.sha(public),
                 'signal_memory_default_rebindings':self.rules()}
            with patch.object(sv,'ROOT',root):
                self.assertEqual(sv.module_views(row,{}),(public,original))
                with self.assertRaises(sv.ViewError):sv.module_views({**row,'signal_memory_default_rebindings':[]},{})


class SignalMemoryDefaultExportTests(unittest.TestCase):
    def test_new_dependency_environment_inherits_only_the_exact_registered_default_repair(self):
        f=fixtures.ExportTests('test_complete_import_resource_closure_and_exact_inverse');f.setUp();self.addCleanup(f.tearDown)
        dependency=b'def dependency : Nat := 1\n'
        source=('import A\n'+SignalMemoryDefaultTests.BASE+SignalMemoryDefaultTests.ORIGINAL).encode()
        f.write(f.source,'Lean/A.lean',dependency);f.write(f.source,'Lean/Example.lean',source)
        first=f.commit(f.source);f.existing('Lean/A.lean',dependency,first)
        row=f.existing('Lean/Example.lean',source,first,target='H0mework.Example',imports={'A':'H0mework.A'})
        rules=[{'source_declaration':SignalMemoryDefaultTests.ORIGINAL,'target_declaration':SignalMemoryDefaultTests.TARGET}]
        public=sv.rebind_signal_memory_defaults((f.public/row['path']).read_text(),rules).encode()
        view=sv.rebind_signal_memory_defaults(source.decode(),rules).encode()
        row.update(signal_memory_default_rebindings=rules,target_sha256=sv.sha(public),view_sha256=sv.sha(view))
        f.write(f.public,row['path'],public);f.write_map()
        f.write(f.source,'Lean/A.lean',b'def dependency : Nat := 2\n');second=f.commit(f.source)
        plan=f.run_stage([{'source_commit':second,'roots':['Lean/Example.lean']}])
        added=next(r for r in plan['additions'] if r['source_path']=='Lean/Example.lean')
        self.assertEqual(added['signal_memory_default_rebindings'],rules)
        with patch.object(sv,'ROOT',f.directory/'stage/stage'):
            self.assertEqual(sv.module_views(added,{})[1],source)
        self.assertEqual((f.public/row['path']).read_bytes(),public)


if __name__=='__main__':unittest.main()
