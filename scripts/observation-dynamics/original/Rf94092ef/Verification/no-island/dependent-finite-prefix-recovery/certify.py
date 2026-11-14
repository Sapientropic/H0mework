#!/usr/bin/env python3
"""Verify finite original observation prefixes and the dependent and Fock consumers."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import struct
import subprocess
import time

FLAGS = ['--trust=0', '-DElab.async=false', '-DwarningAsError=true', '-DmaxErrors=1',
         '-j1', '-M32000', '-DstderrAsMessages=false']
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


_digest_cache = {}
_json_cache = {}


def identity(path):
    stat = Path(path).stat()
    return stat.st_dev,stat.st_ino,stat.st_size,stat.st_mtime_ns


def sha(path):
    key = identity(path)
    if key not in _digest_cache:
        with Path(path).open('rb') as stream:
            _digest_cache[key] = hashlib.file_digest(stream, 'sha256').hexdigest()
    return _digest_cache[key]


def exact(record, root=Path('.')):
    path = root/record['path']
    require(('bytes' not in record or path.stat().st_size==record['bytes']) and sha(path)==record['sha256'],'exact file drift '+str(path))
    return path


def read(path):
    return json.loads(Path(path).read_text())


def save(path, value):
    with Path(path).open('w') as stream:
        json.dump(value, stream, indent=2, ensure_ascii=False)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())


_tracked_source_digests = {}


def tracked_source_sha(repo, revision, path):
    relative = path.relative_to(repo).as_posix()
    key = (repo, revision, relative)
    if key not in _tracked_source_digests:
        blob = subprocess.check_output(['git','--no-optional-locks','cat-file','blob',
            revision+':'+relative],cwd=repo)
        _tracked_source_digests[key] = hashlib.sha256(blob).hexdigest()
    return _tracked_source_digests[key]


_commit_ancestry = {}


def is_tracked_ancestor(repo, revision, foundation):
    key = (repo, foundation)
    if key not in _commit_ancestry:
        reachable = subprocess.check_output(
            ['git','--no-optional-locks','rev-list',foundation], cwd=repo)
        _commit_ancestry[key] = set(reachable.split())
    return revision.encode() in _commit_ancestry[key]


def tracked_blobs(repo, revision, paths):
    requests=''.join(f'{revision}:{path}\n' for path in paths).encode()
    result=subprocess.check_output(['git','--no-optional-locks','cat-file','--batch'],
                                  input=requests,cwd=repo)
    position=0
    digests={}
    for path in paths:
        end=result.index(b'\n',position)
        header=result[position:end].split()
        require(len(header)==3 and header[1]==b'blob','missing tracked source '+path)
        size=int(header[2])
        content=result[end+1:end+1+size]
        position=end+size+2
        require(len(content)==size and result[position-1:position]==b'\n','invalid Git batch response '+path)
        digests[path]=hashlib.sha256(content).hexdigest()
    require(position==len(result),'trailing Git source data')
    return digests


def lake_digest(data):
    # Lean 4.33 hash_str uses MurmurHash64A with seed 11. Lake mixes it with Hash.nil.
    multiplier=0xc6a4a7935bd1e995
    mask=(1<<64)-1
    state=11 ^ ((len(data)*multiplier)&mask)
    whole=len(data)&~7
    for word, in struct.iter_unpack('<Q',memoryview(data)[:whole]):
        mixed=(word*multiplier)&mask
        mixed=((mixed^(mixed>>47))*multiplier)&mask
        state=((state^mixed)*multiplier)&mask
    if whole<len(data):
        state=((state^int.from_bytes(data[whole:],'little'))*multiplier)&mask
    state=((state^(state>>47))*multiplier)&mask
    value=state^(state>>47)
    mixed=(value*multiplier)&mask
    return f'{((1723^mixed^(mixed>>47)^multiplier)*multiplier)&mask:016x}'


def verify_paid_generic(repo, row, select, foundation, checkpoint, slug, ending, attempt, scope, publication_sha):
    module=row['module']
    manifest_path,cert_path,promotion_path,stage_path,receipt_path=map(exact,row['bindings'])
    manifest,cert,promotion,stage,receipt=map(read,(manifest_path,cert_path,promotion_path,stage_path,receipt_path))
    package=repo/'Verification/no-island'/slug
    inputs_path=package/'inputs.json'
    inputs=read(inputs_path)
    source=repo/row['main']
    publication_path=stage_path.parent/'publication-commit.json'
    publication=read(publication_path)
    revision=row['tracked_source_commit']
    require(row['binding_kind']=='exact-certified-source-reuse' and module.endswith(ending) and
            manifest_path==package/'manifest.json' and cert_path==package/'certificate.json' and
            manifest['checkpoint']==cert['checkpoint']==publication['checkpoint']==checkpoint and
            cert['verdict']=='certified' and set(cert['axioms'])==AXIOMS and
            sha(publication_path)==publication_sha and publication['commit']==revision and
            is_tracked_ancestor(repo,revision,foundation) and
            all(str(p.relative_to(repo)) in publication['paths'] for p in (manifest_path,cert_path,inputs_path,source)),
            'exact generic certificate or owned publication drift '+module)
    for path in (manifest_path,cert_path,inputs_path,source):
        require(tracked_source_sha(repo,revision,path)==sha(path)==tracked_source_sha(repo,foundation,path),
                'tracked generic source or evidence drift '+str(path))
    for path in (cert_path,inputs_path):
        member,=[entry for entry in manifest['members'] if entry['path']==path.name]
        require(exact(member,package)==path,'generic signed manifest member drift '+str(path))
    require(exact({**cert['inputs'],'path':str(inputs_path)})==inputs_path and
            exact({**cert['main_promotion'],'path':str(promotion_path)})==promotion_path and
            publication['manifest_sha256']==sha(manifest_path) and
            inputs['frozen_inputs']['stage-map.json']==publication['stage_map_sha256']==sha(stage_path)==promotion['stage_map_sha256'] and
            stage['frozen'] and promotion['exact'] and promotion['old_compilations']==0,
            'exact generic stage or promotion drift '+module)
    owner,=[entry for entry in stage['inputs'] if entry['module']==module]
    promoted,=[entry for entry in promotion['inputs'] if entry['module']==module]
    science,=[entry for entry in inputs['science'] if entry['module']==module]
    raw,=[entry for entry in read(exact(stage['raw_ci_inventory']))['rows'] if entry['object']==owner['object']['path']]
    extras=json.dumps(raw['compiler_extra_names'],ensure_ascii=False,separators=(',',':')).encode()
    require((raw['raw'],raw['private'],len(raw['compiler_extra_names']))==scope and raw['unsafe']==raw['partial']==0 and
            (science['logical_CIs'],science['logical_private_CIs'],science['compiler_extras'])==scope and
            science['compiler_extra_names_sha256']==hashlib.sha256(extras).hexdigest() and
            cert['counts']['safe']==cert['counts']['kernel_calls'] and cert['counts']['unsafe']==cert['counts']['logical_partial']==0,
            'exact generic certified CI scope drift '+module)
    original=Path(owner['source'])
    require(row['source_evidence']=={'kind':'retained-source','path':str(original)} and
            owner['main']==promoted['main']==row['main'] and
            sha(source)==sha(original)==sha(receipt['source_snapshot'])==receipt['source_sha256']==
                row['source_sha256']==owner['source_sha256']==promoted['source_sha256'] and
            exact(owner['receipt'])==receipt_path and promoted['receipt_sha256']==sha(receipt_path) and
            Path(receipt['source'])==original and owner['final_attempt']==receipt['attempt']==attempt and
            owner['strict_command']==receipt['command'] and set(FLAGS[:3])<=set(receipt['command']) and
            receipt['exit_code']==receipt['old_compilations']==0 and receipt['source_unchanged'],
            'exact generic source or strict receipt drift '+module)
    artifact=exact(row['authority_object'])
    hit=select(module)
    require(all(hit.samefile(p) for p in (artifact,row['object'],row['provider'],exact(owner['object']),exact(receipt['object']))) and
            sha(hit)==row['object_sha256']==science['artifact_sha256']==promoted['object_sha256'],
            'exact generic first-hit artifact drift '+module)
    pin=read(exact(stage['context']))['mathlib_bindings']
    require(sha(exact(pin))==inputs['frozen_inputs']['mathlib-bindings.json'],'generic pinned Mathlib evidence drift '+module)
    return pin


def verify_mathlib(repo, select, foundation, records):
    checkout=(repo/'Lean/.lake/packages/mathlib').resolve(strict=True)
    revision='db584cd6d46c92f209a44c0f1c829460d327499d'
    lock=read(repo/'Lean/lake-manifest.json')
    frozen_lock=json.loads(subprocess.check_output(['git','--no-optional-locks','cat-file','blob',
        foundation+':Lean/lake-manifest.json'],cwd=repo))
    frozen,=[item for item in frozen_lock['packages'] if item['name']=='mathlib']
    live,=[item for item in lock['packages'] if item['name']=='mathlib']
    actual=subprocess.check_output(['git','--no-optional-locks','rev-parse','HEAD'],cwd=checkout,text=True).strip()
    require(frozen['rev']==live['rev']==actual==revision and
            frozen['url']==live['url']=='https://github.com/leanprover-community/mathlib4','exact Mathlib lock drift')
    scopes=(
        ('r-prime-three-born-mixed-graph-mathlib/v1','Mathlib.Analysis.InnerProductSpace.Adjoint'),
        ('r-prime-three-born-mixed-iteration-mathlib/v1','Mathlib.Analysis.InnerProductSpace.MeanErgodic'),
        ('dependent-finite-prefix-recovery-mathlib/v1','Mathlib.Analysis.SpecificLimits.Normed'),
    )
    verified=[]
    for record,(schema,module) in zip(records,scopes,strict=True):
        binding=read(exact(record))
        require(binding['schema']==schema and [r['module'] for r in binding['rows']]==[module],
                'exact Mathlib selected scope drift '+module)
        row,=binding['rows']
        relative=Path(*module.split('.'))
        tracked=checkout/relative.with_suffix('.lean')
        source,artifact=exact(row['source']),exact(row['object'])
        require(row['tracked_source_commit']==revision and source.samefile(tracked) and
                sha(source)==tracked_source_sha(checkout,revision,tracked) and
                artifact.samefile(checkout/'.lake/build/lib/lean'/relative.with_suffix('.olean')) and
                all(select(module).samefile(p) for p in (artifact,row['provider'])),
                'exact Mathlib selected source/object drift '+module)
        verified.append(module)
    return verified


def verify_lake_closure(repo, rows, select, foundation, context):
    plan=read(exact(context['legacy_plan']))
    readback=read(exact(context['legacy_readback']))
    planned={entry['module']:entry for entry in plan['rows']}
    observed={entry['module']:entry for entry in readback}
    frozen={entry['module']:entry for entry in rows}
    require(len(rows)==len(plan['rows'])==len(readback)==len(frozen)==207 and
            frozen.keys()==planned.keys()==observed.keys(),'exact Fock and dependent Lake scope drift')
    heads=plan['heads']
    require(len(heads)==len(set(heads))==5,'exact Lake direct subject scope drift')
    pending=list(heads)
    reachable=set()
    while pending:
        module=pending.pop()
        if module in reachable:
            continue
        require(module in planned,'missing original project import '+module)
        reachable.add(module)
        pending.extend(dep for dep in planned[module]['imports'] if dep.startswith('SaturationMonoid.'))
    require(reachable==frozen.keys(),'Lake rows exceed the actual five-head project closure')

    paths=[row['main'] for row in rows]
    tracked=tracked_blobs(repo,foundation,paths)
    import_line=re.compile(r'^(?:(?:public|private|meta) +)*import +([^\r\n]+)$',re.M)
    module_name=re.compile(r'^[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)+$')
    for row in rows:
        module=row['module']
        expected=planned[module]
        metadata=observed[module]
        require(row['binding_kind']=='exact-lake-trace-reuse' and row['tracked_source_commit']==foundation and
                row['main']=='Lean/'+module.replace('.','/')+'.lean' and expected['rel']==module.replace('.','/'),
                'exact tracked Lake owner scope drift '+module)
        source=repo/row['main']
        contents=source.read_bytes()
        declared={name for line in import_line.findall(contents.decode())
                  for name in line.split('--',1)[0].split() if module_name.fullmatch(name)}
        require(source==Path(expected['source']) and hashlib.sha256(contents).hexdigest()==
                tracked[row['main']]==row['source_sha256'] and declared==set(expected['imports']) and
                declared==set(metadata['imports'])-{'Init'}, 'exact source and original imports drift '+module)
        selected=select(module)
        authority=row['authority_object']
        original=Path(authority['path'])
        original_bytes=original.read_bytes()
        digest=hashlib.sha256(original_bytes).hexdigest()
        require(original==Path(expected['object']) and len(original_bytes)==authority['bytes'] and
                digest==authority['sha256']==row['object_sha256'] and
                all(selected.samefile(p) for p in (row['object'],row['provider'],expected['selected_provider'])) and
                (selected.samefile(original) or sha(selected)==digest),
                'exact Lake artifact bytes or first hit drift '+module)
        trace_path,=map(exact,row['bindings'])
        trace=read(trace_path)
        source_hash=lake_digest(contents.replace(b'\r\n',b'\n'))
        object_hash=lake_digest(original_bytes)
        require(trace_path==Path(expected['trace']) and trace_path==original.with_suffix('.trace') and
                trace['synthetic'] is False and trace['schemaVersion']=='2025-09-10' and
                dict(trace['inputs']).get(str(source))==source_hash and object_hash+'.olean' in trace['outputs']['o'] and
                'Module.name: '+module in dict(trace['inputs']) and
                expected['lake_source_hash']==metadata['lake_source_hash']==source_hash and
                expected['lake_object_hash']==metadata['lake_object_hash']==object_hash and
                metadata['source_exact'] and metadata['object_exact'] and metadata['raw']>=0 and
                row['source_evidence']=={'kind':'lake-checked-source-and-object','lake_source_hash':source_hash,
                                         'lake_object_hash':object_hash,'raw':metadata['raw']},
                'exact independently recomputed Lake trace or raw metadata drift '+module)
    return heads


def verify_provider_scope(repo, parents, select, foundation, context):
    require(len(parents)==len({row['module'] for row in parents})==209,'CP701 exact project parent scope drift')
    generic=(
        ('CP700','riemann-r-prime-three-born-mixed-graph','.Hilbert.LandweberRecovery','002',(22,12,0),
         '9d10e153ef1a7038923e4b4676e4a96de77b6bca5da8179b3f5908e41177936e'),
        ('CP699','riemann-r-prime-three-born-mixed-iteration','.Hilbert.ContractiveRecovery','005',(14,3,6),
         'eedbebcd1abc96936b013904b8e120a0f096261abae0c0d440fa616a31d0bcf1'),
    )
    pins=[verify_paid_generic(repo,row,select,foundation,*scope)
          for row,scope in zip(parents[:2],generic,strict=True)]
    mathlib=verify_mathlib(repo,select,foundation,[*pins,context['mathlib_bindings']])
    heads=verify_lake_closure(repo,parents[2:],select,foundation,context)
    return {parents[0]['module'],mathlib[-1],*heads}


def verify_compact_view(view, context):
    authority=exact(context['lean_path_compaction'])
    compact=read(authority)
    require(compact['compact_roots']==31 and compact['library_copies']==0 and
            len(view.read_text().strip().split(os.pathsep))==31,
            'CP701 compact selected view or copied library drift')
    return {'authority':context['lean_path_compaction'],'current_view':context['selected_lean_path']}


def selected(module, roots):
    package = module.split('.')[0]
    relative = Path(*module.split('.')).with_suffix('.olean')
    for index, root in enumerate(roots):
        if (root/package).is_dir() or (root/(package+'.olean')).is_file():
            path = root/relative
            require(path.is_file(),'selected package root lacks '+module)
            return path,index
    raise RuntimeError('missing '+module)


def verify_inputs(package, args):
    inputs = read(package/'inputs.json')
    roots = list(map(Path,args.base_lean_path_file.read_text().strip().split(os.pathsep)))
    require(args.compiled_root.resolve()==roots[0].resolve(),'complete compiled root must be first')
    require((args.repo/'Lean/lean-toolchain').read_text().strip()==inputs['lean_toolchain'],'toolchain drift')
    for name,digest in inputs['local_evidence_sha256'].items():
        require(sha(package/name)==digest,'checker/evidence drift '+name)
    base = roots[0].parent
    for name in ('stage-map.json','context.json'):
        require(sha(base/name)==inputs['frozen_inputs'][name],'frozen input drift '+name)
    require(sha(args.base_lean_path_file)==inputs['frozen_inputs']['lean-path.txt'],'compiled view drift')
    stage,context = read(base/'stage-map.json'),read(base/'context.json')
    require(stage['frozen'] and stage['foundation_commit']==inputs['foundation_commit'],
            'frozen foundation drift')
    for key, filename in (('raw_ci_inventory','raw-inventory.json'),('construction_cost','construction-cost.json'),
                          ('paid_parent_bindings','paid-parent-bindings.json'),('context','context.json'),
                          ('compiler_companions','compiler-companions.json'),('output_location','output-location.json'),
                          ('raw_inventory_receipt','receipts/RawInventory-001.receipt.json')):
        require(stage[key]['sha256']==inputs['frozen_inputs'][filename] and exact(stage[key]).samefile(base/filename),'frozen stage binding drift '+filename)
    frozen = {r['module']:r for r in stage['inputs']}
    science = {r['module']:r for r in inputs['science']}
    strict = {r['module']:r for r in read(package/'evidence/science-compiles.json')['rows']}
    require(len(science)==4 and frozen.keys()==science.keys()==strict.keys(),'science owner drift')
    science_actual = []
    for module,row in science.items():
        source = (args.source_root or args.repo/'Lean')/(module.replace('.','/')+'.lean')
        artifact,index = selected(module,roots)
        require(sha(source)==row['source_sha256']==frozen[module]['source_sha256'] and
                artifact.samefile(frozen[module]['object']['path']) and sha(artifact)==row['artifact_sha256']==frozen[module]['object']['sha256'] and
                artifact.stat().st_size==row['artifact_bytes'],'science source/body drift '+module)
        imports = re.findall(r'^import\s+(\S+)',source.read_text(),re.M)
        require(module.startswith('SaturationMonoid.') and module.rsplit('.',1)[-1] in {'Gram','Iteration','FinitePrefixRecovery','FinitePrefix'} and
                row['intended_formal_path']=='Lean/'+module.replace('.','/')+'.lean' and
                imports==row['base'] and not any(name.startswith('scratch.') for name in imports),
                'production source import drift '+module)
        receipt = strict[module]
        actual_receipt = read(exact(frozen[module]['receipt']))
        require(receipt['receipt_sha256']==row['strict_receipt_sha256']==frozen[module]['receipt']['sha256'] and
                receipt['source_sha256']==row['source_sha256'] and receipt['object_sha256']==row['artifact_sha256'] and
                receipt['exit_code']==actual_receipt['exit_code']==0 and
                receipt['trust']==0 and receipt['werror'] and not receipt['elab_async'] and
                actual_receipt['source_sha256']==row['source_sha256'] and
                actual_receipt['object']['sha256']==row['artifact_sha256'] and actual_receipt['source_unchanged'] and
                artifact.samefile(exact(actual_receipt['object'])) and
                actual_receipt['command']==frozen[module]['strict_command'] and
                sha(actual_receipt['source_snapshot'])==row['source_sha256'] and
                set(FLAGS[:3]) <= set(actual_receipt['command']) and actual_receipt['old_compilations']==0,
                'strict source/body receipt drift '+module)
        science_actual.append({**row,'selected_olean':str(artifact),'search_path_index':index})

    require(inputs['paid_parent_evidence']['path']=='evidence/paid-parents.json', 'parent evidence member drift')
    paid_path = exact(inputs['paid_parent_evidence'],package)
    paid = read(paid_path)
    parents = paid['rows']
    imports = {m for row in science.values() for m in row['base']} - science.keys()
    require(paid['schema']=='dependent-finite-prefix-recovery-paid-parents/v1' and
            len(parents)==209 and parents==context['exact_paid_bodies'] and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            context['old_objects_copied']==paid['copies']==paid['old_compilations']==0 and
            imports==set(inputs['audit_base']), 'paid scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['payload'])
    parent_view=base.parent/'iqa-r-prime-three-born-mixed-graph/lean-path.txt'
    parent_roots=list(map(Path,parent_view.read_text().strip().split(os.pathsep)))
    require(Path(output['control'])==base and output['copied_parent_objects']==0 and
            output['lean_path_roots']==len(roots)==31 and roots==[base/'lib',*parent_roots[1:]] and
            physical.is_relative_to('runtime/ and
            Path(stage['lean_root']).resolve()==physical/'source-root/main' and
            all((base/name).is_symlink() and (base/name).resolve()==physical/name
                for name in ('objects','receipts','source-root')) and
            all(Path(row['object']['path']).resolve().parent==physical/'objects' for row in frozen.values()),
            'second SSD output binding drift')
    mathlib = exact(context['mathlib_bindings'])
    require(mathlib.samefile(base/'mathlib-bindings.json') and sha(mathlib)==inputs['frozen_inputs']['mathlib-bindings.json'],
        'frozen Mathlib provider list drift')
    for key,name in (('legacy_plan','legacy-proof/legacy-plan.json'),
                     ('legacy_readback','legacy-proof/legacy-readback.json')):
        authority=exact(context[key])
        require(authority.samefile(base/name) and sha(authority)==inputs['frozen_inputs'][name],
                'frozen original Lake evidence drift '+name)
    provider_imports=verify_provider_scope(args.repo,parents,lambda module: selected(module,roots)[0],
        stage['foundation_commit'],context)
    require(imports==provider_imports,'actual direct and inherited project authority drift')
    companions = read(exact(stage['compiler_companions']))
    require(companions['schema']=='dependent-finite-prefix-recovery-compiler-companions/v1' and
        companions['companions']==inputs['compiler_companions']==[], 'unexpected fresh compiler runtime companion')
    compaction = verify_compact_view(args.base_lean_path_file,context)
    require(compaction==inputs['lean_path_compaction'],
        'independently checked inherited path compaction drift')
    return inputs,roots,science_actual


def validate_report(path, inputs, actual):
    report = read(path)
    stage, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and stage['label']==inputs['audit_label'] and stage['duplicates'] == 0 and
            stage['inherited'] == counts['inherited'] == report['inherited_generated_full_CI_matches'] and
            stage['fresh_replayed'] == counts['safe'] == report['fresh_safe_replayed_CIs'] and
            stage['fresh_replayed']+stage['inherited']+len(stage['compiler_runtime'])==stage['raw']==counts['raw'] and
            not stage['base_has_unverified_sources'] and
            report['fresh_raw_regions'] == 4 and report['paid_base_environment_imports'] == 1 and
            report['full_candidate_environment_imports'] == 0, 'replay escaped its subject-free base')
    require(inputs['compiler_companions']==stage['compiler_runtime']==[] and counts['compiler_runtime']==0,
        'unexpected fresh runtime companion')
    require(counts['raw_private']==counts['private']==57, 'private logical scope drift')
    owners = {r['module']:r for r in actual}
    for owner in stage['modules']:
        selected_owner = owners.pop(owner['module'])
        require(sha(owner['selected_olean']) == selected_owner['artifact_sha256'] and
                owner['raw'] == selected_owner['raw_CIs'] and owner['imports'] == selected_owner['raw_imports'] and
                owner['compiler_extras'] == selected_owner['compiler_extras'] and
                hashlib.sha256(json.dumps(owner['compiler_extra_names'],ensure_ascii=False,separators=(',',':')).encode()).hexdigest() ==
                    selected_owner['compiler_extra_names_sha256'],
                'wrong audited owner '+owner['module'])
    require([r['name'] for r in stage['inherited_generated_full_CIs']]==inputs['inherited_generated_CIs'] and
            all(r['same_full_constant_info'] and not r['kernel_replayed']
                for r in stage['inherited_generated_full_CIs']), 'inherited CI qualification drift')
    require(not owners and report['safe_private_original_CIs'] == stage['safe_private'] == counts['safe'] and
            stage['kernel_calls'] == counts['kernel_calls'] and stage['compiler_extras'] == counts['extras'] and
            sum(r['name'].startswith('_private.') for r in stage['declarations']) == counts['private'] and
            len(report['public_mouths']) == counts['public_mouths'] and
            len(report['source_body_bindings']) == counts['body_bindings'] and
            len(report['source_type_bindings']) == counts['type_bindings'] and
            report['source_target_reads'] == [] and set(report['axioms']) == AXIOMS,
            'incomplete SCI or source provenance')
    public = {'SourceGeneratedActionObservationHistory.PrefixRecovery.scale': (['𝕜',
                                                                       'H',
                                                                       'F',
                                                                       '_',
                                                                       '_',
                                                                       '_',
                                                                       '_',
                                                                       '_',
                                                                       'read',
                                                                       'j'],
                                                                      0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.row': (['𝕜',
                                                                     'H',
                                                                     'F',
                                                                     '_',
                                                                     '_',
                                                                     '_',
                                                                     '_',
                                                                     '_',
                                                                     'read',
                                                                     'j'],
                                                                    0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.finiteAction': (['𝕜',
                                                                              'H',
                                                                              'F',
                                                                              '_',
                                                                              '_',
                                                                              '_',
                                                                              '_',
                                                                              '_',
                                                                              '_',
                                                                              '_',
                                                                              'read',
                                                                              'n'],
                                                                             0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.limitAction': (['𝕜',
                                                                             'H',
                                                                             'F',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             'read'],
                                                                            0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.finite_gap': (['𝕜',
                                                                            'H',
                                                                            'F',
                                                                            '_',
                                                                            '_',
                                                                            '_',
                                                                            '_',
                                                                            '_',
                                                                            '_',
                                                                            '_',
                                                                            'read',
                                                                            'n'],
                                                                           0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.finite_residual': (['𝕜',
                                                                                 'H',
                                                                                 'F',
                                                                                 '_',
                                                                                 '_',
                                                                                 '_',
                                                                                 '_',
                                                                                 '_',
                                                                                 '_',
                                                                                 '_',
                                                                                 'read',
                                                                                 'n',
                                                                                 'x'],
                                                                                0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.limit_fixed': (['𝕜',
                                                                             'H',
                                                                             'F',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             'read',
                                                                             'x'],
                                                                            0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.prefixDrive': (['𝕜',
                                                                             'H',
                                                                             'F',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             'read',
                                                                             'n',
                                                                             'data'],
                                                                            0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.prefix_drive_source': (['𝕜',
                                                                                     'H',
                                                                                     'F',
                                                                                     '_',
                                                                                     '_',
                                                                                     '_',
                                                                                     '_',
                                                                                     '_',
                                                                                     '_',
                                                                                     '_',
                                                                                     'read',
                                                                                     'x',
                                                                                     'n'],
                                                                                    0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.approximate': (['𝕜',
                                                                             'H',
                                                                             'F',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             '_',
                                                                             'read',
                                                                             'n',
                                                                             'data'],
                                                                            0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.prefix_data_error': (['𝕜',
                                                                                   'H',
                                                                                   'F',
                                                                                   '_',
                                                                                   '_',
                                                                                   '_',
                                                                                   '_',
                                                                                   '_',
                                                                                   '_',
                                                                                   '_',
                                                                                   'read',
                                                                                   'n',
                                                                                   'x',
                                                                                   'y'],
                                                                                  0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.prefix_limit_error': (['𝕜',
                                                                                    'H',
                                                                                    'F',
                                                                                    '_',
                                                                                    '_',
                                                                                    '_',
                                                                                    '_',
                                                                                    '_',
                                                                                    '_',
                                                                                    '_',
                                                                                    'read',
                                                                                    'x',
                                                                                    'n'],
                                                                                   0),
     'SourceGeneratedActionObservationHistory.PrefixRecovery.recover': (['𝕜',
                                                                         'H',
                                                                         'F',
                                                                         '_',
                                                                         '_',
                                                                         '_',
                                                                         '_',
                                                                         '_',
                                                                         '_',
                                                                         '_',
                                                                         'read',
                                                                         'x'],
                                                                        0),
     'SourceGeneratedActionObservationHistory.Dependent.finite_prefix_current': (['State',
                                                                                  'step',
                                                                                  'C',
                                                                                  'B',
                                                                                  '_',
                                                                                  '_',
                                                                                  '_',
                                                                                  '_',
                                                                                  '_',
                                                                                  '_',
                                                                                  'action',
                                                                                  'observe',
                                                                                  'state',
                                                                                  'value'],
                                                                                 0),
     'SourceGeneratedActionObservationHistory.Dependent.finite_prefix_next': (['State',
                                                                               'step',
                                                                               'C',
                                                                               'B',
                                                                               '_',
                                                                               '_',
                                                                               '_',
                                                                               '_',
                                                                               '_',
                                                                               '_',
                                                                               'action',
                                                                               'observe',
                                                                               'state',
                                                                               'value'],
                                                                              0),
     'SourceGeneratedActionObservationHistory.Dependent.finite_prefix_next_read': (['State',
                                                                                    'step',
                                                                                    'C',
                                                                                    'B',
                                                                                    '_',
                                                                                    '_',
                                                                                    '_',
                                                                                    '_',
                                                                                    '_',
                                                                                    '_',
                                                                                    'action',
                                                                                    'observe',
                                                                                    'state',
                                                                                    'value'],
                                                                                   0),
     'SourceGeneratedActionObservationHistory.Dependent.Pulse.finiteNext': (['n'],
                                                                            0),
     'SourceGeneratedActionObservationHistory.Dependent.Pulse.finite_prefix_actual_next': ([],
                                                                                           0),
     'SourceGeneratedActionObservationHistory.Dependent.Pulse.finite_prefix_atomic_half': ([],
                                                                                           0),
     'SourceGeneratedActionObservationHistory.Dependent.Pulse.finite_prefix_time_loss': (['n'],
                                                                                         0),
     'SourceGeneratedActionObservationHistory.Dependent.Pulse.finite_prefix_original_receipt': (['n'],
                                                                                                0)}
    binders = {}
    for row in report['public_mouths']:
        ending, = [name for name in public if row['name']==name or row['name'].endswith('.'+name)]
        require(ending not in binders,'duplicate public producer mouth '+ending)
        binders[ending] = (row['input_binders'],row['result_arrows'])
    require(binders==public, 'actual finite Gram, dependent state and original Fock pulse telescope drift')
    require(stage['kernel_calls']==counts['kernel_calls']==stage['fresh_replayed']==counts['safe']==108 and
        stage['inductive_generated_CIs']==inputs['inductive_generated_CIs']==[] and counts['inductive_generated_CIs']==0,
        'full fresh logical CI coverage drift')
    ancestry = report['dependent_finite_prefix_recovery_data_ancestry']
    require(ancestry==inputs['dependent_finite_prefix_recovery_data_ancestry'] and all(ancestry.values()) and len(ancestry)==6,
            'original finite prefix, dependent shifted next and Fock whole receipt ancestry drift')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ('repo','compiled-root','base-lean-path-file','output'):
        parser.add_argument('--'+option,type=Path,required=True)
    parser.add_argument('--source-root',type=Path)
    parser.add_argument('--lean',type=Path)
    parser.add_argument('--verify-inputs-only',action='store_true')
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    inputs, roots, actual = verify_inputs(package,args)
    output = args.output.resolve()
    output.mkdir(parents=True,exist_ok=True)
    save(output/'provenance.json',{'schema':'cp701-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
        'paid_direct_imports':7,'paid_project_imports':6,'pinned_mathlib_imports':1,'inherited_generic_mathlib_bindings':2,'paid_reused_project_bodies':203,'signed_generic_bindings':2,'exact_lake_trace_reuses':207,'verification_overlay_objects':0,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None,'paid_direct_imports':7,'paid_project_imports':6,'pinned_mathlib_imports':1,'inherited_generic_mathlib_bindings':2,'paid_reused_project_bodies':203,'signed_generic_bindings':2,'exact_lake_trace_reuses':207,'verification_overlay_objects':0,'lean_calls':0}))
        return

    lean = args.lean or Path(subprocess.check_output(['elan','which','lean'],cwd=args.repo/'Lean',text=True).strip())
    env = {**os.environ,'LEAN_PATH':os.pathsep.join(map(str,roots)),'LEAN_SYSROOT':str(lean.parent.parent)}
    cost = output/'cost.json'
    require(not cost.exists(),'use an empty output directory for a fresh run')
    calls = []

    def run(label, filename, command, scope_env):
        source = package/filename
        log = output/(label+'.log')
        start = time.monotonic()
        with log.open('wb') as stream:
            child = subprocess.Popen(command,cwd=package,env=scope_env,stdout=stream,stderr=subprocess.STDOUT)
            print(json.dumps({'label':label,'pid':child.pid}),flush=True)
            code = child.wait()
        row = {'label':label,'exit_code':code,'elapsed_seconds':time.monotonic()-start,
               'source_sha256':sha(source),'log_sha256':sha(log)}
        calls.append(row)
        save(output/(label+'.receipt.json'),row)
        save(cost,{'schema':'cp701-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP701_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':inputs['audit_label'],'base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'physical':str(Path(r['selected_olean']).resolve(strict=True)),
            'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp701-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'compiler_runtime':report['stages'][0]['compiler_runtime'],'inductive_generated_CIs':report['stages'][0]['inductive_generated_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
