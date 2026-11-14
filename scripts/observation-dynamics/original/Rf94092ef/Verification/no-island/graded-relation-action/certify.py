#!/usr/bin/env python3
"""Verify CP778 on its frozen parent view, then replay only its three new owners."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

FLAGS = ['--trust=0','-DElab.async=false','-DwarningAsError=true','-DmaxErrors=1',
         '-j1','-M32000','-DstderrAsMessages=false']
AXIOMS = {'propext','Classical.choice','Quot.sound'}
SCIENCE_ATTEMPTS = [('Word','002'),('Relation','002'),('Consumer','002')]
PREFIX = 'CP778_CONTROL '
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


def verify_parent(repo, stage, roots):
    parent = stage['parent']
    prior_path,publication_path,cert_path = (exact(parent[key]) for key in ('stage_map','publication','certificate'))
    prior = read(prior_path)
    pub,cert,manifest = signed_package(repo,'CP777',publication_path,cert_path)
    inputs = signed_member(cert_path,manifest,'inputs.json')
    promotion = read(exact(cert['main_promotion']))
    view = exact(prior['lean_path'])
    require(prior['checkpoint']==pub['checkpoint']=='CP777' and
            exact(read(inputs)['stage_map'])==prior_path and sha(inputs)==cert['inputs']['sha256'] and
            pub['stage_map_sha256']==promotion['stage_map_sha256']==sha(prior_path) and
            promotion['exact'] and promotion['old_compilations']==cert['old_ci_replays']==cert['old_source_recompiles']==0 and
            cert['default_main_static']['verdict']=='exact-inputs-verified' and
            [str(path) for path in roots[1:]]==view.read_text().strip().split(os.pathsep),
            'CP777 exact signed stage and inherited view drift')

    effect, = [row for row in stage['parent_direct'] if row['module'].endswith('.RequestRelay.Effect')]
    original, = [row for row in prior['modules'] if row['module']==effect['module']]
    promoted, = [row for row in promotion['inputs'] if row['module']==effect['module']]
    receipt = read(exact(effect['receipt']))
    effect_source = repo/effect['main']
    hit = first_hit(effect['module'],roots)
    require(effect==original and effect['main'] in pub['paths'] and
            sha(effect_source)==tracked(repo,pub['commit'],effect_source)==tracked(repo,stage['project_head'],effect_source)==
                sha(exact(effect['source']))==sha(receipt['source_snapshot'])==
                receipt['source_sha256']==promoted['source_sha256'] and
            hit.samefile(exact(effect['object'])) and hit.samefile(exact(receipt['object'])) and
            hit.samefile(first_hit(effect['module'],roots[1:])) and
            promoted['object_sha256']==effect['object']['sha256'] and promoted['receipt_sha256']==effect['receipt']['sha256'] and
            receipt['source_unchanged'] and receipt['exit_code']==receipt['old_compilations']==0 and
            (receipt['stage'],receipt['attempt'])==('Effect','002') and set(FLAGS[:3])<=set(receipt['command']),
            'CP777 exact Effect source, object or strict receipt drift')

    admission, = [row for row in stage['parent_direct'] if row['module'].endswith('.Feed.Admission')]
    original, = [row for row in prior['supplement'] if row['module']==admission['module']]
    signed_comparison_path = exact(prior['donor']['paid_parents'])
    signed_comparison_cert = read(exact(prior['donor']['certificate']))
    comparison, = [dependency for row in read(signed_comparison_path)['parents']
        for dependency in row['inherited_selected_dependencies'] if dependency['module']==admission['module']]
    comparison_report = read(exact(comparison['report']))
    comparison_receipt = read(exact(comparison['strict_metadata_receipt']))
    admission_source = repo/admission['main']
    hit = first_hit(admission['module'],roots)
    require(admission==original and sha(admission_source)==tracked(repo,stage['project_head'],admission_source)==
                admission['source_sha256'] and hit.samefile(exact(admission['object'])) and
            hit.samefile(admission['first_hit']) and hit.samefile(exact(comparison['selected'])) and
            sha(exact(comparison['earlier']))!=admission['object']['sha256'] and
            comparison_report['selectedCIs']==comparison_report['earlierCIs']==
                signed_comparison_cert['counts']['Admission_equal_raw_CIs_across_different_objects']==91 and
            comparison_report['sameImportNames'] and comparison_report['sameCompilerExtraNames'] and
            comparison_report['missing']==comparison_report['different']==comparison_report['added']==[] and
            comparison_receipt['exit_code']==0 and set(FLAGS[:3])<=set(comparison_receipt['command']) and
            str(exact(comparison['comparison_source'])) in comparison_receipt['command'],
            'CP777 inherited Admission object or original stored CI proof drift')
    require(len(stage['parent_direct'])==2,'CP777 direct parent scope drift')
    return {effect['module'],admission['module']}


def verify_donor(repo, stage, roots):
    donor = stage['donor']
    prior_path,publication_path,cert_path = (exact(donor[key]) for key in ('stage_map','publication','certificate'))
    prior = read(prior_path)
    pub,cert,manifest = signed_package(repo,'CP775',publication_path,cert_path)
    inputs = signed_member(cert_path,manifest,'inputs.json')
    evidence = signed_member(cert_path,manifest,cert['paid_parent_evidence']['path'])
    require(pub['stage_map_sha256']==read(inputs)['frozen_inputs']['stage-map.json']==sha(prior_path) and
            sha(inputs)==cert['inputs']['sha256'] and sha(evidence)==cert['paid_parent_evidence']['sha256'] and
            prior['paid_parent_bindings']==donor['paid_parents'] and
            cert['default_main_static']['verdict']=='exact-inputs-verified',
            'CP775 original certificate or exact paid bindings drift')
    signed = {row['module']:row for row in read(evidence)['added_rows']}
    insert, = [row for row in prior['inputs'] if row['module'].endswith('.Projection.DualColumn.Insert')]
    signed_insert, = [row for row in read(inputs)['science'] if row['module']==insert['module']]
    receipt = read(exact(insert['receipt']))
    owner_source = repo/insert['main']
    require(insert['main'] in pub['paths'] and sha(owner_source)==tracked(repo,pub['commit'],owner_source)==
                sha(receipt['source_snapshot'])==receipt['source_sha256']==
                insert['source_sha256']==signed_insert['source_sha256'] and
            signed_insert['strict_receipt_sha256']==insert['receipt']['sha256'] and
            signed_insert['artifact_sha256']==insert['object']['sha256'] and
            signed_insert['raw_imports']==insert['imports'] and
            insert['final_attempt']==receipt['attempt']=='003' and
            receipt['exit_code']==receipt['old_compilations']==0 and receipt['source_unchanged'] and
            set(FLAGS[:3])<=set(receipt['command']) and exact(insert['object']).samefile(exact(receipt['object'])),
            'CP775 original strict Insert owner drift')

    rows = {row['module']:row for row in stage['supplement']}
    require(len(rows)==len(stage['supplement'])==4 and
            set(rows)=={insert['module']}|{name for name in insert['imports'] if name!='Init'},
            'CP775 exact source graph graft drift')
    donor_root = prior_path.parent/'lib'
    for module,row in rows.items():
        relative = Path(*module.split('.')).with_suffix('.olean')
        source = repo/row['main']
        hit = first_hit(module,roots)
        require(row['anchor']=='CP775' and row['main']=='Lean/'+relative.with_suffix('.lean').as_posix() and
                sha(source)==tracked(repo,stage['project_head'],source)==row['source_sha256'] and
                hit==Path(row['first_hit']) and hit.is_symlink() and hit.samefile(exact(row['object'])) and
                hit.samefile(donor_root/relative),'CP775 same-inode donor link drift '+module)
        if module==insert['module']:
            require(hit.samefile(exact(insert['object'])),'CP775 original Insert object drift')
        else:
            ancestor = signed[module]
            require(ancestor['binding_kind']=='exact-certified-source-reuse' and ancestor['main']==row['main'] and
                    ancestor['source_sha256']==row['source_sha256']==tracked(repo,ancestor['tracked_source_commit'],source) and
                    ancestor['object_sha256']==row['object']['sha256'] and
                    hit.samefile(exact(ancestor['authority_object'])) and hit.samefile(ancestor['provider']),
                    'CP775 original signed dependency drift '+module)
            for binding in ancestor['bindings']:
                exact(binding)

    projection = 'SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection'
    chosen = first_hit(projection,roots)
    require(chosen.samefile(exact(stage['same_projection'])) and chosen.samefile(first_hit(projection,roots[1:])) and
            chosen.samefile(first_hit(projection,[donor_root])),'shared original Projection inode drift')
    require({module for module,row in rows.items() if row['old_direct']}=={insert['module']},
            'CP775 direct owner scope drift')
    return {insert['module']}


def verify_parents(repo, stage, roots):
    direct = verify_parent(repo,stage,roots) | verify_donor(repo,stage,roots)
    require(len(direct)==len(stage['old_direct'])==3 and direct==set(stage['old_direct']),
            'three exact direct parents required')
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
            len(records)==inputs['counts']['construction_calls']==7 and
            sum(row['exit_code']!=0 for row in cost['attempts'])==2 and
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
    require(stage['checkpoint']=='CP778' and view.samefile(args.base_lean_path_file) and
            exact(stage['toolchain']).samefile(args.repo/'Lean/lean-toolchain') and
            exact(stage['lake_manifest']).samefile(args.repo/'Lean/lake-manifest.json'),
            'frozen view, toolchain or Lake package identity drift')
    roots = [Path(path) for path in view.read_text().strip().split(os.pathsep)]
    require(args.compiled_root.resolve()==roots[0].resolve() and roots[0]==base/'lib',
            'candidate compiled root drift')
    direct = verify_parents(args.repo,stage,roots)
    verify_construction(base,stage,inputs)
    inventory = read(exact(stage['raw_inventory']))
    require(inventory['regions_read']==len(inventory['rows'])==len(stage['modules'])==len(SCIENCE_ATTEMPTS)==3,
            'three selected science owners required')
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
            sum(row['raw'] for row in stage['modules'])==stage['raw']==26 and
            sum(row['private'] for row in stage['modules'])==stage['private']==12 and
            sum(row['compiler_extra'] for row in stage['modules'])==405,'direct imports or exact selected counts drift')
    return inputs,roots,stage,modules


def validate_report(report, inputs, stage):
    replay, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and report['fresh_raw_regions']==3 and report['paid_base_environment_imports']==1 and
            report['full_candidate_environment_imports']==0 and not replay['base_has_unverified_sources'] and
            report['safe_private_original_CIs']==report['fresh_safe_replayed_CIs']==replay['kernel_calls']==
                replay['raw']==replay['fresh_replayed']==counts['logical']==26 and
            replay['inherited']==replay['duplicates']==0 and replay['compiler_runtime']==replay['inductive_generated_CIs']==[] and
            sum(row['name'].startswith('_private.') for row in replay['declarations'])==counts['private']==12 and
            replay['compiler_extras']==counts['compiler_extras']==405 and
            set(report['axioms'])==AXIOMS and report['source_target_reads']==[] and
            all(report['graded_relation_action_ancestry'].values()) and len(report['graded_relation_action_ancestry'])==5 and
            len(report['public_mouths'])==counts['public_mouths']==9 and
            len(report['source_body_bindings'])==counts['body_bindings']==45 and
            len(report['source_type_bindings'])==counts['type_bindings']==52,
            'fresh CI, axiom or actual source contract drift')
    require(replay['label']==inputs['audit_label'] and len(replay['modules'])==len(stage['modules']),
            'wrong audited owner scope')
    for audited,row in zip(replay['modules'],stage['modules'],strict=True):
        require(audited['module']==row['module'] and audited['imports']==row['imports'] and
                sha(audited['selected_olean'])==row['object']['sha256'] and
                audited['raw']==row['raw'] and audited['compiler_extras']==row['compiler_extra'],
                'wrong audited owner '+row['module'])
    old = report['old_synthesis_single']
    donor, = [row for row in stage['supplement'] if row['old_direct']]
    require(report['inherited_generated_full_CI_matches']==0 and
            old['module']==donor['module'] and old['selected']==donor['first_hit'] and
            old['name'].startswith('_private.'+donor['module']+'.') and old['name'].endswith('.synthesis_single') and
            old['same_full_CI'] and old['kernel_replays']==0,'original private Insert declaration drift')
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
        'paid_direct_imports':3,'supplement_links':4,'parent':'CP777','donor':'CP775',
        'shared_projection_same_inode':True,'inherited_Admission_CIs':91,'lean_calls':0}
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
