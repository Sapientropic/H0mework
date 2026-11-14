#!/usr/bin/env python3
"""Verify CP777 on its frozen parent view, then replay only its four new owners."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import struct
import subprocess
import time

FLAGS = ['--trust=0','-DElab.async=false','-DwarningAsError=true','-DmaxErrors=1',
         '-j1','-M32000','-DstderrAsMessages=false']
AXIOMS = {'propext','Classical.choice','Quot.sound'}
SCIENCE_ATTEMPTS = [('Index','003'),('Born','004'),('Carry','005'),('Effect','002')]
PREFIX = 'CP777_CONTROL '
_DIGESTS = {}


def require(condition, reason):
    if not condition:
        raise RuntimeError(reason)


def sha(path):
    path = Path(path)
    stat = path.stat()
    key = (stat.st_dev,stat.st_ino,stat.st_size,stat.st_mtime_ns)
    if key not in _DIGESTS:
        with path.open('rb') as stream:
            _DIGESTS[key] = hashlib.file_digest(stream,'sha256').hexdigest()
    return _DIGESTS[key]


def read(path):
    return json.loads(Path(path).read_text())


def save(path, value):
    Path(path).write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')


def exact(record):
    path = Path(record['path'])
    require(('bytes' not in record or path.stat().st_size==record['bytes']) and sha(path)==record['sha256'],
            'exact evidence drift '+str(path))
    return path


def first_hit(module, roots):
    relative = Path(*module.split('.')).with_suffix('.olean')
    root = next(path for path in roots if (path/relative.parts[0]).is_dir() or
                (path/(relative.parts[0]+'.olean')).is_file())
    hit = root/relative
    require(hit.is_file(),'selected package root lacks '+module)
    return hit


def tracked(repo, revision, path):
    content = subprocess.check_output(['git','--no-optional-locks','cat-file','blob',
        revision+':'+str(path.relative_to(repo))],cwd=repo)
    return hashlib.sha256(content).hexdigest()


def signed_package(repo, checkpoint, publication_path, certificate_path):
    publication = read(publication_path)
    cert = read(certificate_path)
    manifest = certificate_path.with_name('manifest.json')
    signed = read(manifest)
    revision = publication['commit']
    paths = publication.get('paths',publication.get('protected_paths'))
    require(cert['checkpoint']==checkpoint and cert['verdict']=='certified' and set(cert['axioms'])==AXIOMS and
            sha(manifest)==publication['manifest_sha256'] and
            all(str(path.relative_to(repo)) in paths and tracked(repo,revision,path)==sha(path)
                for path in (certificate_path,manifest)),checkpoint+' tracked publication drift')
    member, = [row for row in signed['members'] if row['path']=='certificate.json']
    exact({**member,'path':str(certificate_path)})
    if 'certificate_sha256' in publication:
        require(sha(certificate_path)==publication['certificate_sha256'],checkpoint+' certificate drift')
    return publication,cert,signed


def signed_member(cert_path, manifest, name):
    row, = [item for item in manifest['members'] if item['path']==name]
    return exact({**row,'path':str(cert_path.parent/name)})


def verify_prior_writeback(repo, stage, roots):
    parent = stage['parent']
    stage_path, publication_path, cert_path = (exact(parent[key]) for key in ('stage_map','publication','certificate'))
    prior = read(stage_path)
    publication,cert,_ = signed_package(repo,'CP776',publication_path,cert_path)
    row, = stage['parent_direct']
    old, = [item for item in prior['modules'] if item['module']==row['module']]
    promotion = read(exact(cert['main_promotion']))
    promoted, = [item for item in promotion['inputs'] if item['module']==row['module']]
    receipt = read(exact(row['receipt']))
    current = repo/row['main']
    parent_view = exact(prior['lean_path']).read_text().strip().split(os.pathsep)
    hit = first_hit(row['module'],roots)
    require(row==old and row['module'].endswith('.GradedInnovation.ColumnWriteback') and
            prior['checkpoint']==publication['checkpoint']=='CP776' and
            publication['stage_map_sha256']==promotion['stage_map_sha256']==sha(stage_path) and
            promotion['exact'] and promotion['old_compilations']==cert['old_ci_replays']==cert['old_source_recompiles']==0 and
            str(current.relative_to(repo)) in publication['paths'] and
            sha(current)==tracked(repo,publication['commit'],current)==tracked(repo,stage['project_head'],current)==
                sha(exact(row['source']))==receipt['source_sha256']==promoted['source_sha256'] and
            hit.samefile(exact(row['object'])) and hit.samefile(exact(receipt['object'])) and
            hit.samefile(first_hit(row['module'],list(map(Path,parent_view)))) and
            promoted['object_sha256']==row['object']['sha256'] and promoted['receipt_sha256']==row['receipt']['sha256'] and
            receipt['source_unchanged'] and sha(receipt['source_snapshot'])==receipt['source_sha256'] and
            receipt['exit_code']==receipt['old_compilations']==0 and
            (receipt['stage'],receipt['attempt'])==('Writeback','005') and set(FLAGS[:3])<=set(receipt['command']) and
            cert['default_main_static']['verdict']=='exact-inputs-verified' and
            [str(path) for path in roots[1:-1]]==parent_view,
            'CP776 selected ColumnWriteback source, certificate or first hit drift')
    ancestor = prior['parent']
    handoff,ancestor_cert,aliases,ancestor_pub = (exact(ancestor[key]) for key in
        ('handoff','certificate','aliases','publication'))
    signed_ancestor = read(ancestor_pub)
    require(signed_ancestor['checkpoint']=='CP477' and signed_ancestor['machine_finalized'] and
            signed_ancestor['current_finalized'] and signed_ancestor['frozen_first_hit_count']==
            cert['counts']['parent_alias_records']==720 and
            exact(signed_ancestor['independent_certificate'])==ancestor_cert and
            exact(signed_ancestor['frozen_capsule'])==handoff and exact(read(handoff)['full_aliases'])==aliases,
            'CP477 already-certified ancestor view drift')
    return row['module']


def verify_donor_owner(repo, rows, owner, revision):
    module = owner['module']
    row = rows[module]
    receipt = read(exact(owner['receipt']))
    require(owner['intended_formal_path']==row['main'] and owner['source_sha256']==row['source_sha256'] and
            sha(receipt['source']['snapshot'])==receipt['source']['sha256']==
                row['source_sha256']==tracked(repo,revision,repo/row['main']) and
            Path(row['first_hit']).samefile(exact(owner['object'])) and
            Path(row['first_hit']).samefile(exact(receipt['object'])) and
            receipt['exit_code']==0 and receipt['source_unchanged'] and set(FLAGS[:3])<=set(receipt['command']),
            'original strict donor owner drift '+module)


def lake_digest(data):
    # Lean 4.33 hash_str uses MurmurHash64A with seed 11. Lake mixes it with Hash.nil.
    multiplier = 0xc6a4a7935bd1e995
    mask = (1<<64)-1
    state = 11 ^ ((len(data)*multiplier)&mask)
    whole = len(data)&~7
    for word, in struct.iter_unpack('<Q',memoryview(data)[:whole]):
        mixed = (word*multiplier)&mask
        mixed = ((mixed^(mixed>>47))*multiplier)&mask
        state = ((state^mixed)*multiplier)&mask
    if whole<len(data):
        state = ((state^int.from_bytes(data[whole:],'little'))*multiplier)&mask
    state = ((state^(state>>47))*multiplier)&mask
    mixed = ((state^(state>>47))*multiplier)&mask
    return f'{((1723^mixed^(mixed>>47)^multiplier)*multiplier)&mask:016x}'


def verify_donor(repo, stage, roots):
    donor = stage['donor']
    stage_path,publication_path,cert_path,paid_path,production_path = (exact(donor[key]) for key in
        ('stage_map','publication','certificate','paid_parents','earlier_binding'))
    original = read(stage_path)
    publication,cert,manifest = signed_package(repo,'CP530',publication_path,cert_path)
    signed_inputs = signed_member(cert_path,manifest,'inputs.json')
    require(sha(signed_inputs)==cert['inputs']['sha256'] and
            read(signed_inputs)['frozen_inputs']['stage-map.json']==sha(stage_path) and
            exact(original['paid_parent_bindings'])==paid_path and
            sha(paid_path)==sha(signed_member(cert_path,manifest,'evidence/paid-parents.json')) and
            roots[-1]==stage_path.parent/'lib','CP530 signed selected view or paid evidence drift')
    rows = {row['module']:row for row in stage['supplement']}
    require(len(rows)==len(stage['supplement'])==7 and
            {module.rsplit('.',1)[-1] for module in rows}==
                {'Origin','Partition','Inventory','Occurrence','Execution','Words','Admission'},
            'CP530 exact graft scope drift')
    for module,row in rows.items():
        relative = Path(*module.split('.')).with_suffix('.lean')
        source = repo/'Lean'/relative
        hit = first_hit(module,roots)
        require(row['main']==str(source.relative_to(repo)) and
                sha(source)==tracked(repo,stage['project_head'],source)==row['source_sha256'] and
                hit==Path(row['first_hit']) and hit.is_symlink() and hit.samefile(exact(row['object'])) and
                hit.samefile(roots[-1]/relative.with_suffix('.olean')),
                'CP530 supplement source or first-hit inode drift '+module)
    origin, = [row for row in original['inputs'] if row['module'].endswith('.Receipt.Origin')]
    signed_origin, = [row for row in read(signed_inputs)['science'] if row['module']==origin['module']]
    require(signed_origin['source_sha256']==origin['source_sha256'] and
            signed_origin['artifact_sha256']==origin['object']['sha256'] and
            signed_origin['strict_receipt_sha256']==origin['receipt']['sha256'],'CP530 signed Origin input drift')
    verify_donor_owner(repo,rows,origin,publication['commit'])

    paid = {row['module'].rsplit('.',1)[-1]:row for row in read(paid_path)['parents']}
    partition = paid['Partition']
    partition_cert = exact(partition['certificate'])
    partition_pub,partition_signed,partition_manifest = signed_package(repo,'CP529',exact(partition['publication']),partition_cert)
    partition_inputs = signed_member(partition_cert,partition_manifest,'inputs.json')
    signed_partition, = [row for row in read(partition_inputs)['science'] if row['module']==partition['module']]
    partition_stage = read(exact(partition['stage_map']))
    partition_owner, = [row for row in partition_stage['inputs'] if row['module']==partition['module']]
    require(partition_pub['commit']==partition['tracked_commit'] and
            partition_owner['receipt']==partition['strict_receipt'] and partition_owner['object']==partition['object'] and
            sha(partition_inputs)==partition_signed['inputs']['sha256'] and
            signed_partition['artifact_sha256']==partition['object']['sha256'] and
            signed_partition['strict_receipt_sha256']==partition['strict_receipt']['sha256'],
            'CP529 signed Partition reuse drift')
    verify_donor_owner(repo,rows,partition_owner,partition_pub['commit'])

    execution = paid['Execution']
    production = read(production_path)
    results = read(exact(production['results']))
    verdict = read(exact(production['formal']['verdict.json']))
    require(exact(execution['production_binding'])==production_path and
            exact(execution['strict_receipt'])==exact(production['results']) and production['checkpoint']=='CP339' and
            production['verdict']=='certified canonical binding' and
            production['parent_recompiles']==production['library_copy_bytes']==0 and
            verdict['verdict']=='certified' and verdict['checkpoint']=='CP339 canonical' and
            exact(verdict['manifest'])==exact(production['formal']['manifest.json']),
            'CP339 signed canonical production authority drift')
    for record in production['canonical_sources']:
        module = record['module']
        if module not in rows or module.rsplit('.',1)[-1] not in {'Inventory','Occurrence','Execution'}:
            continue
        row = rows[module]
        receipt = results[module]
        require(record['source_sha256']==receipt['source_sha256']==row['source_sha256'] and
                sha(record['source'])==row['source_sha256'] and
                tracked(repo,execution['tracked_commit'],repo/row['main'])==row['source_sha256'] and
                Path(row['first_hit']).samefile(record['olean']) and
                record['olean_sha256']==receipt['olean_sha256']==row['object']['sha256'] and
                receipt['exit_code']==0 and set(FLAGS[:3])<=set(receipt['command']),
                'CP339 signed canonical source, result or inode drift '+module)
    require({row['module'].rsplit('.',1)[-1] for row in production['canonical_sources'] if row['module'] in rows}==
            {'Inventory','Occurrence','Execution','Admission','Words'},'CP339 canonical scope drift')
    admission, = [row for row in execution['inherited_selected_dependencies'] if row['module'].endswith('.Feed.Admission')]
    comparison = read(exact(admission['report']))
    comparison_receipt = read(exact(admission['strict_metadata_receipt']))
    row = rows[admission['module']]
    require(Path(row['first_hit']).samefile(exact(admission['selected'])) and
            sha(exact(admission['earlier']))!=row['object']['sha256'] and
            str(exact(admission['comparison_source'])) in comparison_receipt['command'] and
            comparison_receipt['exit_code']==0 and set(FLAGS[:3])<=set(comparison_receipt['command']) and
            comparison['selectedCIs']==comparison['earlierCIs']==cert['counts']['Admission_equal_raw_CIs_across_different_objects']==91 and
            comparison['sameImportNames'] and comparison['sameCompilerExtraNames'] and
            comparison['missing']==comparison['different']==comparison['added']==[],
            'CP530 signed Admission stored-CI comparison drift')
    words, = [row for module,row in rows.items() if module.endswith('.Feed.Words')]
    words_source = repo/words['main']
    words_object = Path(words['object']['path'])
    trace = read(words_object.with_suffix('.trace'))
    output_hash = words_object.with_suffix('.olean.hash').read_text().strip()
    require(not trace['synthetic'] and 'Module.name: '+words['module'] in dict(trace['inputs']) and
            dict(trace['inputs'])[str(words_source)]==lake_digest(words_source.read_bytes().replace(b'\r\n',b'\n')) and
            trace['outputs']['o']==[output_hash+'.olean'] and lake_digest(words_object.read_bytes())==output_hash,
            'CP530 selected Words Lake source or object drift')
    return {module for module,row in rows.items() if row['old_direct']}


def verify_parents(repo, stage, roots, inputs):
    direct = verify_donor(repo,stage,roots) | {verify_prior_writeback(repo,stage,roots)}
    require(len(direct)==len(stage['old_direct'])==3 and direct==set(stage['old_direct']),
            'three exact direct parents required')
    compared = read(exact(stage['old_alias_overlap']))
    require(len(compared)==len(inputs['overlap_objects'])==2,'exact old import comparison scope drift')
    for row,overlap,count,metadata in zip(compared,inputs['overlap_objects'],(52,41),(4,0),strict=True):
        selected = first_hit(overlap['module'],roots)
        earlier = roots[-1]/Path(*overlap['module'].split('.')).with_suffix('.olean')
        require(selected.samefile(row['selected']) and earlier.samefile(row['earlier']) and
                sha(selected)==overlap['selected_sha256'] and sha(earlier)==overlap['earlier_sha256'] and
                row['selectedCIs']==row['earlierCIs']==count and len(row['different'])==metadata and
                row['sameImportNames'] and row['sameCompilerExtraNames'] and row['missing']==row['added']==[] and
                all(all(ci[field] for field in ('sameType','sameBody','sameLevelParams','sameStoredInfo'))
                    for ci in row['different']),'exact old import comparison drift '+overlap['module'])
    return direct


def verify_construction(base, stage, inputs):
    cost = read(exact(stage['construction_cost']))
    records = []
    for row in cost['attempts']:
        stem = row['stage']+'-'+row['attempt']
        receipt_path = base/'receipts'/(stem+'.receipt.json')
        receipt = read(receipt_path)
        log = receipt_path.with_name(stem+'.log')
        require(all(receipt[k]==v for k,v in row.items()) and row['old_compilations']==0 and
                receipt['source_unchanged'] and sha(receipt['source_snapshot'])==receipt['source_sha256'] and
                sha(log)==receipt['log_sha256'] and log.stat().st_size==receipt['log_bytes'] and
                receipt['lean_path_sha256']==stage['lean_path']['sha256'] and set(FLAGS[:3])<=set(receipt['command']),
                'construction attempt drift '+stem)
        records.append([receipt_path.name,sha(receipt_path)])
    payload = json.dumps(records,separators=(',',':')).encode()
    require(cost['old_compilations']==0 and
            len(records)==inputs['counts']['construction_calls']==15 and
            sum(row['exit_code']!=0 for row in cost['attempts'])==10 and
            hashlib.sha256(payload).hexdigest()==inputs['construction_receipts_sha256'],
            'construction receipt set drift')


def verify_inputs(package, args):
    inputs = read(package/'inputs.json')
    for name,digest in inputs['code'].items():
        require(sha(package/name)==digest,'checker source drift '+name)
    stage_path = exact(inputs['stage_map'])
    stage = read(stage_path)
    base = stage_path.parent
    view = exact(stage['lean_path'])
    require(stage['checkpoint']=='CP777' and view.samefile(args.base_lean_path_file) and
            exact(stage['toolchain']).samefile(args.repo/'Lean/lean-toolchain') and
            exact(stage['lake_manifest']).samefile(args.repo/'Lean/lake-manifest.json'),
            'frozen view, toolchain or Lake package identity drift')
    roots = [Path(path) for path in view.read_text().strip().split(os.pathsep)]
    require(args.compiled_root.resolve()==roots[0].resolve() and roots[0]==base/'lib',
            'candidate compiled root drift')
    direct = verify_parents(args.repo,stage,roots,inputs)
    verify_construction(base,stage,inputs)
    inventory = read(exact(stage['raw_inventory']))
    require(inventory['regions_read']==len(inventory['rows'])==len(stage['modules'])==len(SCIENCE_ATTEMPTS)==4,
            'four selected science owners required')
    seen,paid_imports = set(),[]
    modules = []
    source_root = args.source_root or args.repo/'Lean'
    for row,raw,(label,attempt) in zip(stage['modules'],inventory['rows'],SCIENCE_ATTEMPTS,strict=True):
        module = row['module']
        relative = Path(*module.split('.')).with_suffix('.lean')
        source = source_root/relative
        artifact = first_hit(module,roots)
        receipt = read(exact(row['receipt']))
        require(row['main']==str(Path('Lean')/relative) and sha(source)==sha(exact(row['source']))==
                sha(receipt['source_snapshot'])==receipt['source_sha256'] and
                artifact.samefile(exact(row['object'])) and artifact.samefile(exact(receipt['object'])) and
                artifact.resolve().is_relative_to('runtime/ and receipt['exit_code']==receipt['old_compilations']==0 and
                (receipt['stage'],receipt['attempt'])==(label,attempt) and receipt['source_unchanged'] and
                receipt['lean_path_sha256']==stage['lean_path']['sha256'] and set(FLAGS[:3])<=set(receipt['command']),
                'strict science source/object/receipt drift '+module)
        imports = raw['imports']
        require(imports==row['imports'] and raw['object']==row['object']['path'] and
                raw['unsafe']==raw['partial']==0 and raw['raw']==len(raw['constants'])==row['raw'] and
                raw['private']==row['private'] and len(raw['compiler_extra_names'])==row['compiler_extra'] and
                [name for name in imports if name!='Init']==re.findall(r'^import\s+(\S+)',source.read_text(),re.M),
                'exact raw or source imports drift '+module)
        for name in imports:
            if name not in seen and name!='Init' and name not in paid_imports:
                paid_imports.append(name)
        seen.add(module)
        modules.append({'name':module,'selected':str(artifact),'physical':str(artifact.resolve(strict=True)),'imports':imports})
    require(paid_imports==inputs['audit_base'] and set(paid_imports)==direct and
            inputs['entry']==modules[-1]['name'] and
            re.findall(r'^import\s+(\S+)',(package/'Gate.lean').read_text(),re.M)==[inputs['entry']] and
            sum(row['raw'] for row in stage['modules'])==stage['raw']==50 and
            sum(row['private'] for row in stage['modules'])==stage['private']==18 and
            sum(row['compiler_extra'] for row in stage['modules'])==7,'direct imports or exact selected counts drift')
    return inputs,roots,stage,modules


def validate_report(report, inputs, stage):
    replay, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and report['fresh_raw_regions']==4 and report['paid_base_environment_imports']==1 and
            report['full_candidate_environment_imports']==0 and not replay['base_has_unverified_sources'] and
            report['safe_private_original_CIs']==report['fresh_safe_replayed_CIs']==replay['kernel_calls']==
                replay['raw']==replay['fresh_replayed']==counts['logical']==50 and
            replay['inherited']==replay['duplicates']==0 and replay['compiler_runtime']==replay['inductive_generated_CIs']==[] and
            sum(row['name'].startswith('_private.') for row in replay['declarations'])==counts['private']==18 and
            replay['compiler_extras']==counts['compiler_extras']==7 and
            set(report['axioms'])==AXIOMS and report['source_target_reads']==[] and
            all(report['graded_request_relay_ancestry'].values()) and len(report['graded_request_relay_ancestry'])==5 and
            len(report['public_mouths'])==counts['public_mouths']==15 and
            len(report['source_body_bindings'])==counts['body_bindings']==55 and
            len(report['source_type_bindings'])==counts['type_bindings']==65,
            'fresh CI, axiom or actual source contract drift')
    require(replay['label']==inputs['audit_label'] and len(replay['modules'])==len(stage['modules']),
            'wrong audited owner scope')
    for audited,row in zip(replay['modules'],stage['modules'],strict=True):
        require(audited['module']==row['module'] and audited['imports']==row['imports'] and
                sha(audited['selected_olean'])==row['object']['sha256'] and
                audited['raw']==row['raw'] and audited['compiler_extras']==row['compiler_extra'],
                'wrong audited owner '+row['module'])
    compared = read(exact(stage['old_alias_overlap']))
    require(report['inherited_generated_full_CI_matches']==0 and
            len(report['exact_old_import_edges'])==len(inputs['overlap_objects'])==len(compared)==2,
            'old edge comparison scope drift')
    for edge,bound,prior in zip(report['exact_old_import_edges'],inputs['overlap_objects'],compared,strict=True):
        require(edge['module']==bound['module'] and
                Path(edge['earlier']).samefile(prior['earlier']) and
                Path(edge['selected']).samefile(prior['selected']) and
                sha(edge['earlier'])==bound['earlier_sha256'] and sha(edge['selected'])==bound['selected_sha256'] and
                edge['kernel_replays']==0 and edge['stored_info_matches']==prior['selectedCIs'] and
                edge['metadata_only']==[row['name'] for row in prior['different']],
                'independent raw edge report drift '+bound['module'])
    return replay


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ('repo','compiled-root','base-lean-path-file','output'):
        parser.add_argument('--'+option,type=Path,required=True)
    parser.add_argument('--source-root',type=Path)
    parser.add_argument('--lean',type=Path)
    parser.add_argument('--verify-inputs-only',action='store_true')
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    inputs,roots,stage,modules = verify_inputs(package,args)
    args.output.mkdir(parents=True,exist_ok=True)
    result = {'verdict':'exact-inputs-verified','formal_sources':args.source_root is None,'science':len(modules),
        'paid_direct_imports':3,'supplement_links':7,'parent':'CP776','donor':'CP530',
        'canonical_donor':'CP339','parent_alias_records':720,'old_edge_CIs':93,'metadata_only':4,'lean_calls':0}
    save(args.output/'provenance.json',{**result,'stage_map':inputs['stage_map'],'inputs_sha256':sha(package/'inputs.json')})
    if args.verify_inputs_only:
        print(json.dumps(result))
        return
    lean = args.lean or Path(subprocess.check_output(['elan','which','lean'],cwd=args.repo/'Lean',text=True).strip())
    env = {**os.environ,'LEAN_PATH':os.pathsep.join(map(str,roots)),'LEAN_SYSROOT':str(lean.parent.parent)}
    cost = args.output/'cost.json'
    require(not cost.exists(),'use an empty output for fresh independent replay')
    calls = []

    def run(label, source, arguments):
        log = args.output/(label+'.log')
        start = time.monotonic()
        with log.open('xb') as stream:
            code = subprocess.call([str(lean),*FLAGS,*arguments],cwd=package,env=env,stdout=stream,stderr=subprocess.STDOUT)
        calls.append({'label':label,'exit_code':code,'elapsed_seconds':time.monotonic()-start,
                      'source_sha256':sha(source),'log_sha256':sha(log)})
        save(cost,{'calls':calls,'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:])
            raise SystemExit(code)
        return log

    gate = run('001-gate',package/'Gate.lean',[str(package/'Gate.lean')])
    markers = [line[len(PREFIX):] for line in gate.read_text().splitlines() if line.startswith(PREFIX)]
    require(markers==inputs['typed_controls'],'typed gate controls drift')
    config = args.output/'audit-config.json'
    report = args.output/'private-bodies.json'
    save(config,{'label':inputs['audit_label'],'base':inputs['audit_base'],'modules':modules,
        'output':str(report),'progress':str(args.output/'ci-progress.jsonl'),'current':str(args.output/'current-ci.json')})
    run('002-audit',package/'Audit.lean',['--run',str(package/'Audit.lean'),str(config)])
    validate_report(read(report),inputs,stage)
    print(json.dumps({'verdict':'certified','report_sha256':sha(report),'cost_sha256':sha(cost)}))


if __name__=='__main__':
    main()
