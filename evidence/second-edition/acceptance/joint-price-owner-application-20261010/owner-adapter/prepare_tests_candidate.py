from pathlib import Path
import ast,difflib,hashlib,json
ROOT=Path(__file__).resolve().parents[3];BASE=Path(__file__).resolve().parent
extra=r'''

class PrivateOwnerTupleBindingTests(unittest.TestCase):
    def rules(self):
        return [{"source_owner": "_private.SourceSpatial", "target_owner": "_private.H0mework.SourceSpatial"},
                {"source_owner": "_private.SourcePrice", "target_owner": "_private.H0mework.SourcePrice"}]

    def lookup(self, spatial="_private.SourceSpatial", price="_private.SourcePrice"):
        return ('elab "paidGeometry% " id:ident : term => do\n'
                '  let member:=id.getId\n'
                '  let (owner,namespaceName)←\n'
                f'    if member==`spatial_positive then pure ("{spatial}.",`World.Geometry)\n'
                f'    else if member==`physical_price_shape then pure ("{price}.",`World.Geometry)\n'
                '    else throwError "Only original spatial and price are accepted"\n'
                '  let wanted:=namespaceName ++ member\n'
                '  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>name.toString.startsWith owner && privateToUserName name==wanted\n'
                '  match candidates with\n'
                '  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name\n'
                '  | _=>throwError "Expected unique original payer {wanted}"\n')

    def test_registered_tuple_lookup_round_trip_and_explicit_subset(self):
        original=self.lookup()
        public=self.lookup("_private.H0mework.SourceSpatial", "_private.H0mework.SourcePrice")
        self.assertEqual(s.rewrite_private_owner_strings(original,self.rules()),public)
        self.assertEqual(s.rewrite_private_owner_strings(public,self.rules(),reverse=True),original)
        self.assertEqual(s.rewrite_private_owner_strings(original,None),original)
        self.assertEqual(s.rewrite_private_owner_strings(original,[]),original)
        self.assertEqual(s.rewrite_private_owner_strings(original,self.rules()[:1]),
                         self.lookup("_private.H0mework.SourceSpatial"))

    def test_unrelated_literal_comments_raw_strings_and_longer_owner_are_unchanged(self):
        untouched=('def ordinary := "_private.SourceSpatial."\n'
                   'def raw := r##"_private.SourceSpatial."##\n'
                   '-- '+self.lookup().replace('\n','\n-- ')+'\n'
                   '/- '+self.lookup()+'-/\n'
                   +self.lookup("_private.SourceSpatialLonger","_private.SourcePriceLonger"))
        original=untouched+self.lookup()
        public=untouched+self.lookup("_private.H0mework.SourceSpatial", "_private.H0mework.SourcePrice")
        self.assertEqual(s.rewrite_private_owner_strings(original,self.rules()),public)
        self.assertEqual(s.rewrite_private_owner_strings(public,self.rules(),reverse=True),original)

    def test_modified_binding_filter_namespace_guard_and_duplicate_reject(self):
        valid=self.lookup()
        bad=(valid.replace('startsWith owner','startsWith other'),
             valid.replace('namespaceName ++ member','namespaceName ++ other'),
             valid.replace('privateToUserName name==wanted','privateToUserName name==other'),
             valid.replace('`World.Geometry)', '`World.Other)',1),
             valid.replace('physical_price_shape','spatial_positive'),
             valid.replace('return mkConst name','return mkConst other'),
             valid.replace('| [(name,_)]','| (name,_)::_'),
             valid.replace('"_private.SourceSpatial."','r##"_private.SourceSpatial."##'),
             valid.replace('"_private.SourceSpatial."','"_private.SourceSpatialLonger."'),
             valid+valid,
             valid+'name.startsWith "_private.SourceSpatial."\n',
             'def ordinary := "_private.SourceSpatial."\n',
             '-- '+valid.replace('\n','\n-- '))
        for text in bad:
            with self.subTest(text=text),self.assertRaises(s.ViewError):
                s.rewrite_private_owner_strings(text,self.rules())

    def test_original_direct_and_family_modes_coexist_with_tuple_bindings(self):
        rule={"source_owner":"_private.Direct","target_owner":"_private.H0mework.Direct"}
        original='name.startsWith "_private.Direct."\n'+self.lookup()
        public='name.startsWith "_private.H0mework.Direct."\n'+self.lookup("_private.H0mework.SourceSpatial","_private.H0mework.SourcePrice")
        self.assertEqual(s.rewrite_private_owner_strings(original,[rule]+self.rules()),public)
        self.assertEqual(s.rewrite_private_owner_strings(public,[rule]+self.rules(),reverse=True),original)
        self.assertEqual(s.rewrite_private_owner_strings('name.startsWith "_private.Direct"\n',[rule]),
                         'name.startsWith "_private.H0mework.Direct"\n')

    def test_source_view_restores_exact_source_and_rejects_changed_namespace_or_math(self):
        original='import SourceProducer\n'+self.lookup()+'theorem paid : True := by trivial\n'
        public=s.rewrite_private_owner_strings(original,self.rules())
        public=s.transform(public,s.import_tokens(public),{'SourceProducer':'H0mework.SourceProducer'})
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);path=root/'Consumer.lean';path.write_bytes(public)
            row={'path':'Consumer.lean','source_path':'Original.lean','target_sha256':p.sha(public),
                 'source_sha256':p.sha(original.encode()),'private_owner_string_rewrites':self.rules(),
                 'import_map':{'H0mework.SourceProducer':'SourceProducer'}}
            with patch.object(s,'ROOT',root):
                self.assertEqual(s.module_views(row,{}),(original.encode(),original.encode()))
                for changed in (public.replace(b': True :=',b': False :='),
                                public.replace(b'`World.Geometry',b'`World.Other')):
                    path.write_bytes(changed)
                    with self.subTest(changed=changed),self.assertRaises(s.ViewError):
                        s.module_views({**row,'target_sha256':p.sha(changed)}, {})
'''
source=ROOT/'tools/test_publication.py';raw=source.read_text();marker='\nclass PrivateOwnerFamilyPrefixTests(unittest.TestCase):'
assert raw.count(marker)==1
candidate=raw.replace(marker,extra+marker)
ast.parse(candidate)
(BASE/'test_publication-candidate.py').write_text(candidate)
(BASE/'test_publication.diff').write_text(''.join(difflib.unified_diff(raw.splitlines(keepends=True),candidate.splitlines(keepends=True),fromfile='a/tools/test_publication.py',tofile='b/tools/test_publication.py')))
print(json.dumps({'base_sha256':hashlib.sha256(raw.encode()).hexdigest(),'candidate_sha256':hashlib.sha256(candidate.encode()).hexdigest()}))
