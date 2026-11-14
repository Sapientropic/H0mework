#!/usr/bin/env python3
"""Verify the original integer successor on the cofinal tower and its installed inverse and actor reads."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
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
    key = identity(path)
    if key not in _json_cache:
        _json_cache[key] = json.loads(Path(path).read_text())
    return _json_cache[key]


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


def verify_cp267_topology_support(repo, revision, rows, roots):
    verdict_path, manifest_path, previous_path, previous_verdict = map(exact,rows[0]['bindings'])
    verdict, manifest, previous, earlier = map(read,(verdict_path,manifest_path,previous_path,previous_verdict))
    require(verdict['checkpoint']=='CP267' and earlier['checkpoint']=='CP266' and
            verdict['verdict']==earlier['verdict']=='certified' and
            exact(verdict['manifest'])==manifest_path and exact(earlier['manifest'])==previous_path and
            verdict['fixed_head']==manifest['head'] and earlier['fixed_head']==previous['head'] and
            all(set(v['verification']['axioms'])==AXIOMS for v in (verdict,earlier)) and
            all({'-t','0','-DwarningAsError=true'}<=set(m['flags']) for m in (manifest,previous)),
            'CP267 and CP266 signed topology closure drift')
    signed_root = manifest_path.parent/'lib'
    direct_imports = set()
    for row in rows:
        module = row['module']
        original = manifest['closure'][module]
        earlier_source = previous['closure'][module]
        reuse = manifest['prior_completed_evidence'][module]
        copy, = manifest['reuse_artifacts'][module]
        prior_copy, = previous['reuse_artifacts'][module]
        source = repo/row['main']
        current = selected(module,roots)[0]
        authority = exact(row['authority_object'])
        retained = Path(row['source_evidence']['path'])
        require(list(map(exact,row['bindings']))==[verdict_path,manifest_path,previous_path,previous_verdict] and
                row['binding_kind']=='exact-signed-inherited-source-reuse' and
                row['tracked_source_commit']==manifest['head'] and
                is_tracked_ancestor(repo,manifest['head'],revision) and
                row['source_evidence']['kind']=='retained-source' and retained==Path(original['source']) and
                row['main']==original['file']==earlier_source['file'] and
                original['imports']==earlier_source['imports']==re.findall(r'^import\s+(\S+)',retained.read_text(),re.M) and
                sha(source)==sha(retained)==row['source_sha256']==original['sha256']==earlier_source['sha256']==
                    tracked_source_sha(repo,manifest['head'],source)==tracked_source_sha(repo,revision,source) and
                reuse['kind']=='signed-reuse' and reuse['prior_manifest']==str(previous_path) and
                reuse['prior_verdict']==str(previous_verdict) and
                reuse['prior_manifest_sha256']==sha(previous_path) and reuse['prior_verdict_sha256']==sha(previous_verdict) and
                reuse['source_closure_sha256']==previous['source_closure_sha256'][module] and
                copy['source']==reuse['olean']==prior_copy['snapshot'] and copy['snapshot']==str(authority) and
                current.samefile(authority) and current.samefile(row['object']) and current.samefile(row['provider']) and
                sha(current)==row['object_sha256']==reuse['olean_sha256']==copy['sha256']==prior_copy['sha256']==sha(reuse['olean']),
                'CP267 exact signed source, ABI or CP266 predecessor drift '+module)
        direct_imports.update(original['imports'])
    signed_roots = [signed_root,*map(Path,manifest['external_lean_path'])]
    for module in direct_imports:
        prior = selected(module,signed_roots)[0]
        require(selected(module,roots)[0].samefile(prior), 'CP267 direct compatible provider drift '+module)
        if module in manifest['closure']:
            reused, = manifest['reuse_artifacts'][module]
            require(sha(prior)==reused['sha256'], 'CP267 direct signed object drift '+module)
        else:
            require(module in manifest['external'], 'CP267 direct external import drift '+module)


def cache_tracked_sources(repo, revision, paths):
    # Batch the fixed Git tree read. The signed CP74 graph is still checked member by member.
    relatives = [Path(path).relative_to(repo).as_posix() for path in paths]
    pending = sorted(set(relatives)-{p for r,v,p in _tracked_source_digests if (r,v)==(repo,revision)})
    if pending:
        raw = subprocess.check_output(['git','--no-optional-locks','cat-file','--batch'], cwd=repo,
            input=''.join(f'{revision}:{path}\n' for path in pending).encode())
        offset = 0
        for path in pending:
            newline = raw.index(b'\n',offset)
            parts = raw[offset:newline].split()
            require(len(parts)==3 and parts[1]==b'blob','missing pinned tracked source '+path)
            end = newline+1+int(parts[2])
            _tracked_source_digests[(repo,revision,path)] = hashlib.sha256(memoryview(raw)[newline+1:end]).hexdigest()
            require(raw[end:end+1]==b'\n','invalid Git batch framing '+path)
            offset = end+1
        require(offset==len(raw),'unused Git batch data')


def verify_cp74_native_support(repo, revision, rows, context, inputs, roots):
    native = rows[0]
    actor = native['module']
    verdict_path, manifest_path, reconcile_path, graft_path, signed_actor, cp72_manifest, cp72_reconcile, cp72_actor = map(exact,native['bindings'])
    verdict, manifest, reconcile, graft = map(read,(verdict_path,manifest_path,reconcile_path,graft_path))
    signed_root = manifest_path.parent
    old_root = Path(manifest['overlay'])
    require(verdict['checkpoint']=='CP74' and verdict['verdict']=='certified' and
            verdict['fixed_head']==manifest['head']=='eb5168b7d73160f2ee2f79bc7c1dfe5de30b74f5' and
            is_tracked_ancestor(repo,manifest['head'],revision) and
            verdict['trust']['manifest']=={'path':str(old_root/'manifest.json'),'sha256':sha(manifest_path)} and
            {'-t','0','-DwarningAsError=true'}<=set(verdict['trust']['flags']) and
            set(verdict['axioms']['allowed_only'])==AXIOMS and
            verdict['prior_binding']['final_shared_source_import_and_artifact_equal'] and
            reconcile['current_nonowned_source_mismatches']==reconcile['formal_cp73_artifact_mismatches']==[] and
            graft_path==exact(context['goldbach_closure_graft']) and sha(graft_path)==inputs['frozen_inputs']['goldbach-closure-graft.json'] and
            graft['signed_manifest']==str(manifest_path) and graft['manifest_sha256']==sha(manifest_path),
            'CP74 exact signed graph authority drift')
    previous, receipt = map(read,(cp72_manifest,cp72_reconcile))
    original, = [row for row in receipt['fresh'] if row['module']==actor]
    earlier_record = manifest['cp72_verdict']
    earlier_revision = native['tracked_source_commit']
    cp72_old_root = Path(previous['overlay'])
    cp72_path = lambda path: cp72_manifest.parent/Path(path).relative_to(cp72_old_root)
    require(earlier_record['commit']==earlier_revision=='61038acb9f0958c12ebab344f48471d115e7296a' and
            {k:earlier_record[k] for k in ('path','sha256')} in verdict['prior_signed_checkpoints'] and
            is_tracked_ancestor(repo,earlier_revision,revision) and
            original['exit_code']==0 and {'-t','0','-DwarningAsError=true'}<=set(original['command']) and
            sha(cp72_path(original['log']))==original['log_sha256'] and cp72_path(original['olean'])==cp72_actor and
            sha(cp72_actor)==sha(signed_actor)==original['olean_sha256']==native['object_sha256'] and
            previous['closure'][actor]['imports']==manifest['closure'][actor]['imports'] and
            sha(cp72_path(previous['closure'][actor]['source']))==previous['closure'][actor]['sha256']==
                original['source_sha256']==native['source_sha256'] and
            exact(native['signed_ancestor_object'])==signed_actor,
            'CP72 direct actor inverse source and exact strict receipt drift')

    graph = manifest['closure']
    local, external, frontier = set(),set(),[actor]
    while frontier:
        module = frontier.pop()
        if module in local or module in external:
            continue
        if module in graph:
            local.add(module)
            frontier.extend(graph[module]['imports'])
        else:
            external.add(module)
    grafted = {r['module']:r for r in graft['rows']}
    require(len(local)==graft['closure_count']==335 and len(grafted)==len(graft['rows'])==92 and
            len(local-grafted.keys())==graft['same_byte_existing']==243 and grafted.keys()<=local and
            external<=set(manifest['external']), 'CP74 actual Goldbach graft closure drift')
    signed_sources = {r['module']:r for r in reconcile['sources']}
    source_paths = {module:repo/graph[module]['repository_path'] for module in local}
    cache_tracked_sources(repo,revision,source_paths.values())
    changed_sources = []
    for module, source in sorted(source_paths.items()):
        item = graph[module]
        snapshot = signed_root/Path(item['source']).relative_to(old_root)
        artifact, = manifest['reuse_artifacts'][module]
        signed_object = signed_root/Path(artifact['snapshot']).relative_to(old_root)
        current = selected(module,roots)[0]
        require(sha(snapshot)==item['sha256']==signed_sources[module]['source_sha256'] and
                item['owner']==signed_sources[module]['owner'] and sha(current)==sha(signed_object)==artifact['sha256'],
                'CP74 Goldbach signed source or installed bytes drift '+module)
        if module in grafted:
            grafted_row = grafted[module]
            require(Path(grafted_row['path'])==current and current.is_symlink() and current.samefile(signed_object) and
                    Path(grafted_row['signed_path'])==signed_object and grafted_row['copied_bytes']==0 and
                    grafted_row['source_sha256']==item['sha256'] and grafted_row['object_sha256']==artifact['sha256'],
                    'CP74 Goldbach graft same-inode drift '+module)
        if tracked_source_sha(repo,revision,source)!=item['sha256']:
            changed_sources.append(module)
            change = 'a62efbca475792f2222d21fa960603fa0e1f8a3d'
            before = snapshot.read_bytes()
            after = before
            for name in (b'mappingCocone_fst_f',b'mappingCocone_snd_v'):
                marker = b'private theorem '+name+b'\n'
                require(after.count(marker)==1, 'CP74 MappingCocone pinned visibility marker drift')
                after = after.replace(marker,b'theorem '+name+b'\n')
            require(module=='SaturationMonoid.CochainMappingCoconeFunctoriality' and
                    item['sha256']=='c7b2f07ade3c1258982feda8fdd8e0ec2fe349c5d0842959ceae06115fe34a6b' and
                    is_tracked_ancestor(repo,change,revision) and
                    tracked_source_sha(repo,change+'^',source)==item['sha256'] and
                    tracked_source_sha(repo,change,source)==tracked_source_sha(repo,revision,source)==hashlib.sha256(after).hexdigest() and
                    item['imports']==['Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone'],
                    'CP74 pinned transitive visibility change drift '+module)
    require(changed_sources==['SaturationMonoid.CochainMappingCoconeFunctoriality'],
        'CP74 historical source exception scope drift')
    old_roots = [signed_root/'lib',*map(Path,manifest['lean_path'].split(os.pathsep)[1:])]
    require(all(selected(module,roots)[0].samefile(selected(module,old_roots)[0]) for module in external),
        'CP74 exact external ABI drift')

    for row in rows:
        module = row['module']
        item = graph[module]
        source = repo/row['main']
        current = selected(module,roots)[0]
        refs = list(map(exact,row['bindings']))
        snapshot = signed_root/Path(item['source']).relative_to(old_root)
        require(refs[:4]==[verdict_path,manifest_path,reconcile_path,graft_path] and
                len(refs)==(8 if module==actor else 5) and
                row['binding_kind']=='exact-signed-inherited-source-reuse' and row['tracked_source_commit']==earlier_revision and
                row['source_evidence']=={'kind':'retained-source','path':str(snapshot)} and
                row['main']==item['repository_path'] and
                sha(source)==row['source_sha256']==item['sha256']==tracked_source_sha(repo,earlier_revision,source)==tracked_source_sha(repo,revision,source) and
                refs[4]==exact(row['signed_ancestor_object']) and sha(current)==row['object_sha256']==sha(refs[4]) and
                all(current.samefile(path) for path in (row['object'],row['provider'],exact(row['authority_object']))),
                'CP74 exact signed Goldbach parent drift '+module)


def verify_cofinal_topology_actual_successor_parents(repo, package, inputs, stage, context, roots):
    compact = read(exact(inputs['paid_parent_evidence'],package))
    require(compact['schema']=='cofinal-topology-actual-successor-paid-parent-evidence/v1','CP730 compact parent evidence drift')
    revision = stage['foundation_commit']
    prior = repo/'Verification/no-island/riemann-r-counted-full-moving-limit'
    inherited = compact['inherited_authority']
    evidence = exact(inherited['evidence'],repo)
    require(inherited['rows']==210 and inherited['commit']==revision=='d66b06159ef6cbb2fe90bad01692cc3b943193c4' and
            evidence==prior/'evidence/paid-parents.json','CP729 original compensated count parent evidence drift')
    paths = [prior/name for name in ('manifest.json','certificate.json','inputs.json','certify.py')]
    for path in (*paths,evidence):
        require(sha(path)==tracked_source_sha(repo,revision,path),'CP729 tracked authority drift '+str(path))
    manifest_path,cert_path,prior_inputs_path,verifier_path = paths
    manifest,cert,prior_inputs = map(read,paths[:3])
    require(sha(manifest_path)=='e0a704791deeea9296343a3e0a8da739852b6a54d4e562f6cc78607a8ab63dbc' and
            sha(cert_path)=='7117cd2d62771139f7f8f1f00275f16a455ab140b1e51ff20dd2f3c6be3de718' and
            manifest['checkpoint']==cert['checkpoint']=='CP729' and cert['verdict']=='certified' and
            set(cert['axioms'])==AXIOMS and cert['inputs']['sha256']==sha(prior_inputs_path) and
            cert['paid_parent_evidence']==prior_inputs['paid_parent_evidence'] and exact(cert['paid_parent_evidence'],prior)==evidence and
            (cert['counts']['safe'],cert['counts']['private'],cert['counts']['extras'])==(67,50,683),
            'CP729 signed source and kernel scope drift')
    for path in (*paths[1:],evidence):
        member, = [row for row in manifest['members'] if row['path']==path.relative_to(prior).as_posix()]
        require(exact(member,prior)==path,'CP729 original manifest member drift')
    verifier = runpy.run_path(str(verifier_path),run_name='cp729_signed_authority')
    paid_path = exact(stage['paid_parent_bindings'])
    paid = read(paid_path)
    rows = paid['rows']
    require(paid['schema']=='cofinal-topology-actual-successor-paid-parents/v1' and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            len(rows)==len({row['module'] for row in rows})==222 and rows==context['exact_paid_bodies'] and
            rows[210:]==compact['added_rows'] and compact['selected_lean_path']==paid['selected_lean_path'] and
            paid['old_compilations']==paid['copies']==context['old_objects_copied']==0,
            'CP730 exact paid inventory or aliases drift')
    moving_limit, moving_projection = rows[210:212]
    m,c,promotion_path,prior_stage_path,_ = map(exact,moving_projection['bindings'])
    require(m==manifest_path and c==cert_path and sha(promotion_path)==cert['main_promotion']['sha256'] and
            sha(prior_stage_path)==prior_inputs['frozen_inputs']['stage-map.json']==
                '15ec7eb164134ee13828885ee61f3cfff2020f68cbad17db620ee220dc39021c',
            'CP729 exact promoted compensated count source chain drift')
    prior_stage = read(prior_stage_path)
    prior_context = read(exact(prior_stage['context']))
    prior_paid,_ = verifier['verify_counted_full_moving_limit_parents'](repo,prior,prior_inputs,prior_stage,prior_context,roots)
    hit = lambda name: selected(name,roots)[0]
    require(all(current=={**old,'object':current['object'],'provider':current['provider']} and
                all(hit(current['module']).samefile(p) for p in
                    (current['object'],current['provider'],old['object'],old['provider']))
                for current,old in zip(rows[:210],prior_paid['rows'],strict=True)),
            'CP730 inherited CP729 first-hit inode or parent fact drift')
    promotion = read(promotion_path)
    require(promotion['exact'] and promotion['old_compilations']==0 and
            promotion['stage_map_sha256']==sha(prior_stage_path) and len(promotion['inputs'])==len(prior_stage['inputs'])==2,
            'CP729 exact promotion scope drift')
    for row,owner,promoted,ending,attempt in zip((moving_limit,moving_projection),prior_stage['inputs'],promotion['inputs'],
            ('NormalizedFibre.CountedFullMovingLimit','NormalizedFibre.CountedFullMovingProjection'),('002','003'),strict=True):
        module = row['module']
        refs = list(map(exact,row['bindings']))
        strict_path = refs[-1]
        strict = read(strict_path)
        source = repo/row['main']
        require(refs[:4]==[manifest_path,cert_path,promotion_path,prior_stage_path] and
                row['binding_kind']=='exact-certified-source-reuse' and row['tracked_source_commit']==revision and
                module.endswith('.'+ending) and module==owner['module']==promoted['module'] and
                row['main']==owner['main']==promoted['main'] and owner['final_attempt']==strict['attempt']==attempt and
                exact(owner['receipt'])==strict_path and promoted['receipt_sha256']==sha(strict_path) and
                strict['source_unchanged'] and strict['exit_code']==strict['old_compilations']==0 and
                set(FLAGS[:3])<=set(strict['command']) and strict['command']==owner['strict_command'] and
                strict['source']==owner['source']==row['source_evidence']['path'] and
                row['source_evidence']['kind']=='retained-source' and
                sha(source)==tracked_source_sha(repo,revision,source)==sha(owner['source'])==sha(strict['source_snapshot'])==
                    owner['source_sha256']==promoted['source_sha256']==strict['source_sha256']==row['source_sha256'] and
                all(hit(module).samefile(path) for path in (row['object'],row['provider'],exact(row['authority_object']),
                    exact(owner['object']),exact(strict['object']))) and
                sha(hit(module))==row['object_sha256']==promoted['object_sha256'],
                'CP729 exact source, strict compile and selected inode drift '+module)
    verify_cp267_topology_support(repo,revision,rows[212:217],roots)
    verify_cp74_native_support(repo,revision,rows[217:],context,inputs,roots)
    mathlib = read(exact(context['mathlib_bindings']))['rows']
    require(len(mathlib)==11 and mathlib==read(exact(prior_context['mathlib_bindings']))['rows'] and
            all(hit(row['module']).samefile(exact(row['object'])) for row in mathlib),
            'CP730 exact inherited Mathlib binding drift')
    require(sum(row['binding_kind']!='exact-certified-source-reuse' for row in rows)==75,
            'CP730 exact legacy parent count drift')
    direct = []
    for ending in ('.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel','.UpdatedFaces.InverseRead','.Calculation.Cursor.Native.Consumer'):
        module, = [row['module'] for row in rows if row['module'].endswith(ending)]
        direct.append(module)
    return paid,direct


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
    require(len(science)==3 and frozen.keys()==science.keys()==strict.keys(),'science owner drift')
    science_actual = []
    for module,row in science.items():
        source = (args.source_root or args.repo/'Lean')/(module.replace('.','/')+'.lean')
        artifact,index = selected(module,roots)
        require(sha(source)==row['source_sha256']==frozen[module]['source_sha256'] and
                artifact.samefile(frozen[module]['object']['path']) and sha(artifact)==row['artifact_sha256']==frozen[module]['object']['sha256'] and
                artifact.stat().st_size==row['artifact_bytes'],'science source/body drift '+module)
        imports = re.findall(r'^import\s+(\S+)',source.read_text(),re.M)
        require(module.startswith('SaturationMonoid.') and module.rsplit('.',1)[-1] in {'Successor','TopologySuccessor'} and
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
    paid,direct=verify_cofinal_topology_actual_successor_parents(args.repo,package,inputs,stage,context,roots)
    imports={m for row in science.values() for m in row['base']} - science.keys()
    require(imports==set(inputs['audit_base']),'CP730 exact direct import scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['payload'])
    parent_view=base.parent/'iqa-r-counted-full-moving-limit/lean-path.txt'
    parent_roots=list(map(Path,parent_view.read_text().strip().split(os.pathsep)))
    require(Path(output['control'])==base and output['copied_parent_objects']==output['source_copied']==0 and
            output['payload_volume']=='Extension2' and len(roots)==31 and roots==[base/'lib',*parent_roots[1:]] and
            physical.is_relative_to('runtime/ and
            all((base/name).is_symlink() and (base/name).resolve()==physical/name
                for name in ('objects','receipts','source-root')) and
            all(Path(row['object']['path']).resolve().parent==physical/'objects' and
                Path(row['source']).resolve()==physical/'source-root/main'/Path(*row['module'].split('.')).with_suffix('.lean') and
                [arg for arg in row['strict_command'] if arg.startswith('--root=')]==
                    [f"--root={base/'source-root/main'}"] for row in frozen.values()),
            'second SSD output binding drift')
    mathlib = exact(context['mathlib_bindings'])
    require(mathlib.samefile(base/'mathlib-bindings.json') and sha(mathlib)==inputs['frozen_inputs']['mathlib-bindings.json'],
        'frozen Mathlib provider list drift')
    require(imports==set(direct),'CP730 exact production import drift')
    gate_imports=re.findall(r'^import\s+(\S+)',(package/'Gate.lean').read_text(),re.M)
    require(gate_imports==[stage['inputs'][1]['module'],inputs['entry']],'CP730 independent Gate import drift')
    companions = read(exact(stage['compiler_companions']))
    require(companions['schema']=='cofinal-topology-actual-successor-compiler-companions/v1' and
        companions['companions']==inputs['compiler_companions']==[], 'unexpected fresh compiler runtime companion')
    require(exact(context['lean_path_compaction'])==exact(inputs['lean_path_compaction']) and
            context['lean_path_compaction']==read(exact(read(parent_view.parent/'stage-map.json')['context']))['lean_path_compaction'],
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
            report['fresh_raw_regions'] == 3 and report['paid_base_environment_imports'] == 1 and
            report['full_candidate_environment_imports'] == 0, 'replay escaped its subject-free base')
    require(inputs['compiler_companions']==stage['compiler_runtime']==[] and counts['compiler_runtime']==0,
        'unexpected fresh runtime companion')
    require(counts['raw_private']==counts['private']==13, 'private logical scope drift')
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
    generic = ['L','M','_','_']
    installed = ['Sorts','PhysicalValue','PhysicalVar','_','sort','seed','initial']
    public = {
        'allStageSuccessor': (generic+['action'],0),
        'allStage_successor_source': (generic+['action','value'],0),
        'allPrimeSuccessor': (generic+['action'],0),
        'allPrime_successor_source': (generic+['action','value'],0),
        'allPrime_successor_restriction': (generic+['action','prime','stage','value'],0),
        'allStage_successor_uniformContinuous': (generic+['action'],0),
        'allStage_source_successor_uniformContinuous': (generic+['action'],0),
        'allPrimeCoimageSuccessor': (generic+['action'],0),
        'allPrime_coimage_successor_source': (generic+['action','value'],0),
        'allStage_successor_fibre': (generic+['action','left','right'],0),
        'actual_topology_successor': (installed+['count','word'],0),
        'actual_topology_successor_fibre': (installed+['count','left','right'],0),
        'actual_inverse_relation_topology': (installed+['count'],0),
        'actual_actor_topology_successor': (['depth','count','within'],0),
    }
    binders = {}
    for row in report['public_mouths']:
        ending, = [name for name in public if row['name']==name or row['name'].endswith('.'+name)]
        require(ending not in binders,'duplicate public producer mouth '+ending)
        binders[ending] = (row['input_binders'],row['result_arrows'])
    require(binders==public, 'actual topology, original inverse and fixed actor telescope drift')
    require(stage['kernel_calls']==counts['kernel_calls']==stage['fresh_replayed']==counts['safe']==29 and
            stage['inductive_generated_CIs']==inputs['inductive_generated_CIs']==[] and
            counts['inductive_generated_CIs']==0,'full fresh logical CI coverage drift')
    ancestry = report['cofinal_topology_actual_successor_data_ancestry']
    require(ancestry==inputs['cofinal_topology_actual_successor_data_ancestry'] and all(ancestry.values()) and len(ancestry)==5,
            'actual integer source, installed original inverse and paid native actor ancestry drift')
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
    save(output/'provenance.json',{'schema':'cp730-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
         'paid_direct_imports':3,'paid_project_imports':3,'gate_only_project_imports':0,'pinned_mathlib_imports':0,'new_mathlib_support_bindings':0,'inherited_mathlib_support_bindings':11,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':222,'legacy_project_bindings':75,'inherited_parent_references':210,'added_paid_parent_rows':12,'verification_overlay_objects':0,'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None, 'paid_direct_imports':3,'paid_project_imports':3,'gate_only_project_imports':0,'pinned_mathlib_imports':0,'new_mathlib_support_bindings':0,'inherited_mathlib_support_bindings':11,'inherited_euler_mathlib_imports':1,'inherited_tail_mathlib_imports':2,'inherited_liouville_mathlib_imports':1,'inherited_resolvent_mathlib_imports':1,'legacy_jet_mathlib_compatibility':6,'legacy_mobius_mathlib_compatibility':2,'paid_reused_project_bodies':222,'legacy_project_bindings':75,'inherited_parent_references':210,'added_paid_parent_rows':12,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp730-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP730_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':inputs['audit_label'],'base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'physical':str(Path(r['selected_olean']).resolve(strict=True)),
            'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp730-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'compiler_runtime':report['stages'][0]['compiler_runtime'],'inductive_generated_CIs':report['stages'][0]['inductive_generated_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
