"""Observe original anonymous consumers without changing their mathematical bodies."""
import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import source_view as sv
import test_whole_ledger_export as fixtures


class AnonymousConsumerTests(unittest.TestCase):
    MODULE = "H0mework.Fixture.Consumer"

    def rules(self, count=2):
        return [{"ordinal": n, "target_name": sv.anonymous_consumer_name(self.MODULE, n)}
                for n in range(1, count + 1)]

    def test_all_types_and_values_survive_explicit_inverse(self):
        original = ("namespace Original\nnoncomputable section\nvariable (n : Nat)\n"
                    "example : n = n := rfl\n"
                    "example : Nat := Classical.choice (show Nonempty Nat from ⟨n⟩)\nend\nend Original\n")
        public = sv.name_anonymous_consumers(original, self.rules())
        self.assertEqual(public,
            "namespace Original\nnoncomputable section\nvariable (n : Nat)\n"
            "noncomputable def _root_." + self.rules()[0]["target_name"] + " : n = n := rfl\n"
            "noncomputable def _root_." + self.rules()[1]["target_name"] +
            " : Nat := Classical.choice (show Nonempty Nat from ⟨n⟩)\nend\nend Original\n")
        self.assertEqual(sv.name_anonymous_consumers(public, self.rules(), reverse=True), original)
        self.assertEqual(sv.name_anonymous_consumers(original, None), original)
        self.assertEqual(sv.name_anonymous_consumers(original, None, reverse=True), original)

    def test_only_real_example_commands_count(self):
        lookalikes = ('-- example : False := by contradiction\n'
                      '/- outer /- example : False := by contradiction -/ comment -/\n'
                      'def message := "example : False := by contradiction"\n'
                      'def raw := r#"example : False := by contradiction"#\n'
                      'def «example» := 1\ndef exampleLike := 2\n')
        source = lookalikes + '/- leading comment -/ example\n    : True := True.intro\n'
        public = sv.name_anonymous_consumers(source, self.rules(1))
        self.assertTrue(public.startswith(lookalikes))
        self.assertIn('/- leading comment -/ noncomputable def _root_.' + self.rules(1)[0]['target_name'], public)
        self.assertEqual(sv.name_anonymous_consumers(public, self.rules(1), reverse=True), source)
        for text in [lookalikes, 'exampleLike : True := True.intro\n', 'example? : True := True.intro\n',
                     'macro "fixture" : command => `(command|\n  example : True := True.intro)\n']:
            with self.subTest(text=text), self.assertRaises(sv.ViewError):
                sv.name_anonymous_consumers(text, self.rules(1))

    def test_original_noncomputable_example_head_is_explicit_and_reversible(self):
        source = 'example : True := True.intro\nnoncomputable\t example (n : Nat) : Nat := n\n'
        rules = self.rules()
        rules[1]['source_head'] = 'noncomputable\t example'
        public = sv.name_anonymous_consumers(source, rules)
        self.assertNotIn('noncomputable\t noncomputable', public)
        self.assertEqual(public.count('noncomputable def _root_.'), 2)
        self.assertEqual(sv.name_anonymous_consumers(public, rules, reverse=True), source)
        for changed in [self.rules(), [rules[0],dict(rules[1],source_head='noncomputable example')],
                        [rules[0],dict(rules[1],source_head='unsafe example')]]:
            with self.subTest(rules=changed), self.assertRaises(sv.ViewError):
                sv.name_anonymous_consumers(source, changed)
        multiline = 'noncomputable\n  example : Nat := 0\n'
        multiline_rules = self.rules(1)
        multiline_rules[0]['source_head'] = 'noncomputable\n  example'
        self.assertEqual(sv.name_anonymous_consumers(
            sv.name_anonymous_consumers(multiline,multiline_rules),multiline_rules,reverse=True),multiline)

    def test_modified_example_source_view_recovers_the_original_modifier(self):
        original = b'noncomputable example : Nat := Classical.choice (show Nonempty Nat from \xe2\x9f\xa80\xe2\x9f\xa9)\n'
        rules = self.rules(1)
        rules[0]['source_head'] = 'noncomputable example'
        named = sv.name_anonymous_consumers(original.decode(), rules).encode()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory);(root/'Consumer.lean').write_bytes(named)
            row = {'path':'Consumer.lean','source_path':'Lean/Consumer.lean','source_sha256':sv.sha(original),
                   'target':self.MODULE,'target_sha256':sv.sha(named),'view_sha256':sv.sha(named),
                   'anonymous_consumer_names':rules}
            with patch.object(sv,'ROOT',root):
                self.assertEqual(sv.module_views(row,{}),(named,original))

    def test_instance_reducible_is_explicit_and_preserves_the_original_type_and_value(self):
        source = 'class Witness where\n  value : Nat\nexample : Witness := ⟨7⟩\nexample : True := True.intro\n'
        rules = self.rules()
        rules[0]['instance_reducible'] = True
        public = sv.name_anonymous_consumers(source,rules)
        self.assertIn('@[instance_reducible] noncomputable def _root_.' + rules[0]['target_name'] +
                      ' : Witness := ⟨7⟩\n',public)
        self.assertEqual(public.count('@[instance_reducible]'),1)
        self.assertEqual(sv.name_anonymous_consumers(public,rules,reverse=True),source)
        for changed in [public.replace('@[instance_reducible] ',''),
                        public.replace('@[instance_reducible]','@[reducible]'),
                        public.replace('@[instance_reducible]','@[instance_reducible, reducible]'),
                        public.replace('@[instance_reducible]','@[instance_reducible] @[instance_reducible]')]:
            with self.subTest(public=changed), self.assertRaises(sv.ViewError):
                sv.name_anonymous_consumers(changed,rules,reverse=True)
        for value in [False,None,0,1,'true',['instance_reducible']]:
            with self.subTest(value=value), self.assertRaises(sv.ViewError):
                sv.name_anonymous_consumers(source,[dict(rules[0],instance_reducible=value),rules[1]])
        with self.assertRaises(sv.ViewError):
            sv.name_anonymous_consumers(source,[dict(rules[0],attributes=['instance_reducible']),rules[1]])

    def test_instance_reducible_public_view_retains_only_the_registered_attribute(self):
        original='class Witness where\n  value : Nat\nnoncomputable example : Witness := ⟨7⟩\n'.encode()
        rules=self.rules(1)
        rules[0].update(source_head='noncomputable example',instance_reducible=True)
        named=sv.name_anonymous_consumers(original.decode(),rules).encode()
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'Consumer.lean').write_bytes(named)
            row={'path':'Consumer.lean','source_path':'Lean/Consumer.lean','source_sha256':sv.sha(original),
                 'target':self.MODULE,'target_sha256':sv.sha(named),'view_sha256':sv.sha(named),
                 'anonymous_consumer_names':rules}
            with patch.object(sv,'ROOT',root):
                self.assertEqual(sv.module_views(row,{}),(named,original))
                with self.assertRaises(sv.ViewError):
                    sv.module_views({**row,'anonymous_consumer_names':self.rules(1)}, {})

    def test_missing_wrong_duplicate_and_cross_module_rules_fail(self):
        source = 'example : True := True.intro\nexample : Nat := 0\n'
        rules = self.rules()
        bad = [rules[:1], rules + self.rules(3)[2:], {}, [dict(rules[0], ordinal=True), rules[1]],
               [dict(rules[0], ordinal=0), rules[1]], [rules[0], rules[0]],
               [rules[0], dict(rules[1], target_name=rules[0]['target_name'])],
               [dict(rules[0], extra='unregistered'), rules[1]],
               [dict(rules[0], target_name='Other.case001'), rules[1]],
               [dict(rules[0], target_name=sv.anonymous_consumer_name('H0mework.Other.Module', 1)), rules[1]],
               [dict(rules[0], target_name=rules[0]['target_name'] + 'x'), rules[1]]]
        for changed in bad:
            with self.subTest(rules=changed), self.assertRaises(sv.ViewError):
                sv.name_anonymous_consumers(source, changed)

    def test_existing_fully_qualified_and_scoped_names_collide(self):
        name = self.rules(1)[0]['target_name']
        for declaration in [f'def {name} : Nat := 0\n', f'noncomputable def _root_.{name} : Nat := 0\n',
                            'namespace H0mework\nnamespace OriginalConsumerChecks.Fixture.Consumer\n'
                            'def case001 : Nat := 0\nend OriginalConsumerChecks.Fixture.Consumer\nend H0mework\n']:
            with self.subTest(declaration=declaration), self.assertRaises(sv.ViewError):
                sv.name_anonymous_consumers(declaration + 'example : True := True.intro\n', self.rules(1))
        source = 'namespace Different\ndef case001 : Nat := 0\nend Different\nexample : True := True.intro\n'
        self.assertIn('noncomputable def _root_.' + name, sv.name_anonymous_consumers(source, self.rules(1)))

    def test_observation_prefix_uses_the_actual_owner_root_only_once(self):
        for module in [self.MODULE,'H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.Consumer']:
            name=sv.anonymous_consumer_name(module,1)
            self.assertEqual(name.split('.').count('H0mework'),1)
            self.assertEqual(name,'H0mework.OriginalConsumerChecks.'+module.removeprefix('H0mework.')+'.case001')
        with self.assertRaises(sv.ViewError):sv.anonymous_consumer_name('Fixture.Consumer',1)
        old=self.rules(1)
        old[0]['target_name']='H0mework.OriginalConsumerChecks.'+self.MODULE+'.case001'
        previous='noncomputable def _root_.'+old[0]['target_name']+' : True := True.intro\n'
        self.assertEqual(sv.name_anonymous_consumers(previous,old,reverse=True),'example : True := True.intro\n')
        with self.assertRaises(sv.ViewError):
            sv.name_anonymous_consumers('example : True := True.intro\n',old)

    def test_inverse_rejects_wrong_head_missing_duplicate_and_reordered_names(self):
        source = 'example : True := True.intro\nexample : Nat := 0\n'
        public = sv.name_anonymous_consumers(source, self.rules())
        first, second = public.splitlines(keepends=True)
        for changed in [source, public.replace('noncomputable def', 'def', 1), public + first,
                        public + 'def _root_.' + self.rules()[0]['target_name'] + ' : Nat := 0\n',
                        second + first, public.replace(self.rules()[1]['target_name'], 'Other.missing')]:
            with self.subTest(source=changed), self.assertRaises(sv.ViewError):
                sv.name_anonymous_consumers(changed, self.rules(), reverse=True)

    def test_source_view_retains_names_and_recovers_exact_original_bytes(self):
        original = b'noncomputable section\nexample : Nat := Classical.choice (show Nonempty Nat from \xe2\x9f\xa80\xe2\x9f\xa9)\nend\n'
        rules = self.rules(1)
        named = sv.name_anonymous_consumers(original.decode(), rules).encode()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory);path = root/'Consumer.lean';path.write_bytes(named)
            row = {'path':'Consumer.lean','source_path':'Lean/Consumer.lean','source_sha256':sv.sha(original),
                   'target':self.MODULE,'target_sha256':sv.sha(named),'view_sha256':sv.sha(named),
                   'anonymous_consumer_names':rules}
            with patch.object(sv,'ROOT',root):
                self.assertEqual(sv.module_views(row,{}),(named,original))
                for change in [{'anonymous_consumer_names':[]}, {'target':'H0mework.Other'}, {'view_sha256':sv.sha(original)}]:
                    with self.subTest(change=change), self.assertRaises(sv.ViewError):
                        sv.module_views({**row,**change},{})

    def test_old_failed_duplicate_root_view_remains_exactly_recoverable(self):
        original=b'example : True := True.intro\n'
        old_name='H0mework.OriginalConsumerChecks.'+self.MODULE+'.case001'
        previous=('noncomputable def _root_.'+old_name+' : True := True.intro\n').encode()
        rules=[{'ordinal':1,'target_name':old_name}]
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'Consumer.lean').write_bytes(previous)
            row={'path':'Consumer.lean','source_path':'Lean/Consumer.lean','source_sha256':sv.sha(original),
                 'target':self.MODULE,'target_sha256':sv.sha(previous),'view_sha256':sv.sha(previous),
                 'anonymous_consumer_names':rules}
            with patch.object(sv,'ROOT',root):
                self.assertEqual(sv.module_views(row,{}),(previous,original))


class AnonymousConsumerExportTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixtures.ExportTests('test_complete_import_resource_closure_and_exact_inverse')
        self.fixture.setUp()
        self.addCleanup(self.fixture.tearDown)

    def named_owner(self, source_head='example', *, instance_reducible=False):
        f = self.fixture
        dependency = b'def value : Nat := 1\n'
        source = (b'import A\nclass Witness where\n  value : Nat\n' + source_head.encode() +
                  b' : Witness := \xe2\x9f\xa8value\xe2\x9f\xa9\n') if instance_reducible else \
                 b'import A\n' + source_head.encode() + b' : Nat := value\n'
        f.write(f.source,'Lean/A.lean',dependency)
        f.write(f.source,'Lean/Consumer.lean',source)
        epoch = f.commit(f.source)
        f.existing('Lean/A.lean',dependency,epoch)
        row = f.existing('Lean/Consumer.lean',source,epoch,target='H0mework.Consumer',imports={'A':'H0mework.A'})
        rules = [{'ordinal':1,'target_name':sv.anonymous_consumer_name(row['target'],1)}]
        if source_head != 'example':
            rules[0]['source_head'] = source_head
        if instance_reducible:
            rules[0]['instance_reducible'] = True
        public = sv.name_anonymous_consumers((f.public/row['path']).read_text(),rules).encode()
        view = sv.name_anonymous_consumers(source.decode(),rules).encode()
        row.update(anonymous_consumer_names=rules,target_sha256=sv.sha(public),view_sha256=sv.sha(view))
        f.write(f.public,row['path'],public);f.write_map()
        return source,epoch,row,public

    def test_unchanged_recursive_owner_reuses_existing_named_consumer(self):
        source,epoch,owner,public = self.named_owner()
        plan = self.fixture.run_stage([{'source_commit':epoch,'roots':['Lean/Consumer.lean']}])
        self.assertEqual(plan['summary']['added_owners'],0)
        self.assertEqual(len(plan['reuse']),2)
        self.assertEqual((self.fixture.public/owner['path']).read_bytes(),public)

    def test_new_dependency_owner_inherits_rules_rebound_to_its_actual_module(self):
        source,epoch,owner,public = self.named_owner()
        f = self.fixture
        f.write(f.source,'Lean/A.lean',b'def value : Nat := 2\n')
        changed = f.commit(f.source)
        plan = f.run_stage([{'source_commit':changed,'roots':['Lean/Consumer.lean']}])
        row = next(r for r in plan['additions'] if r['source_path']=='Lean/Consumer.lean')
        self.assertNotEqual(row['target'],owner['target'])
        self.assertEqual(row['anonymous_consumer_names'],[
            {'ordinal':1,'target_name':sv.anonymous_consumer_name(row['target'],1)}])
        with patch.object(sv,'ROOT',f.directory/'stage/stage'):
            view,exact = sv.module_views(row,{})
        self.assertEqual(exact,source)
        self.assertIn(row['anonymous_consumer_names'][0]['target_name'].encode(),view)
        self.assertEqual((f.public/owner['path']).read_bytes(),public)

    def test_multiple_historical_owner_prefixes_do_not_conflict_in_a_new_environment(self):
        source,epoch,owner,public = self.named_owner()
        f = self.fixture
        f.write(f.source,'Lean/A.lean',b'def value : Nat := 2\n')
        second = f.commit(f.source)
        plan = f.run_stage([{'source_commit':second,'roots':['Lean/Consumer.lean']}])
        for row in plan['additions']:
            f.export['modules'].append(copy.deepcopy(row))
            f.write(f.public,row['path'],(f.directory/'stage/stage'/row['path']).read_bytes())
        f.write_map()
        f.write(f.source,'Lean/A.lean',b'def value : Nat := 3\n')
        third = f.commit(f.source)
        final = f.run_stage([{'source_commit':third,'roots':['Lean/Consumer.lean']}],name='third')
        row = next(r for r in final['additions'] if r['source_path']=='Lean/Consumer.lean')
        self.assertEqual(row['anonymous_consumer_names'],[
            {'ordinal':1,'target_name':sv.anonymous_consumer_name(row['target'],1)}])
        with patch.object(sv,'ROOT',f.directory/'third/stage'):
            self.assertEqual(sv.module_views(row,{})[1],source)
        self.assertEqual((f.public/owner['path']).read_bytes(),public)

    def test_original_modifier_survives_inheritance_to_a_new_dependency_environment(self):
        source,epoch,owner,public = self.named_owner('noncomputable\texample')
        f = self.fixture
        f.write(f.source,'Lean/A.lean',b'def value : Nat := 2\n')
        changed = f.commit(f.source)
        plan = f.run_stage([{'source_commit':changed,'roots':['Lean/Consumer.lean']}])
        row = next(r for r in plan['additions'] if r['source_path']=='Lean/Consumer.lean')
        self.assertEqual(row['anonymous_consumer_names'][0]['source_head'],'noncomputable\texample')
        with patch.object(sv,'ROOT',f.directory/'stage/stage'):
            view,exact = sv.module_views(row,{})
        self.assertEqual(exact,source)
        self.assertNotIn(b'noncomputable\tnoncomputable',view)
        self.assertEqual((f.public/owner['path']).read_bytes(),public)

    def test_instance_reducible_survives_inheritance_to_a_new_dependency_environment(self):
        source,epoch,owner,public=self.named_owner('noncomputable example',instance_reducible=True)
        f=self.fixture
        f.write(f.source,'Lean/A.lean',b'def value : Nat := 2\n')
        changed=f.commit(f.source)
        plan=f.run_stage([{'source_commit':changed,'roots':['Lean/Consumer.lean']}])
        row=next(r for r in plan['additions'] if r['source_path']=='Lean/Consumer.lean')
        self.assertEqual(row['anonymous_consumer_names'],[
            {'ordinal':1,'target_name':sv.anonymous_consumer_name(row['target'],1),
             'source_head':'noncomputable example','instance_reducible':True}])
        with patch.object(sv,'ROOT',f.directory/'stage/stage'):
            view,exact=sv.module_views(row,{})
        self.assertEqual(exact,source)
        self.assertIn(b'@[instance_reducible] noncomputable def _root_.',view)
        self.assertEqual((f.public/owner['path']).read_bytes(),public)


if __name__ == '__main__':
    unittest.main()
