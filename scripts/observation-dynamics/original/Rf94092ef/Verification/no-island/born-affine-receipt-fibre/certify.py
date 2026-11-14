#!/usr/bin/env python3
"""Verify CP782 on its frozen parent view, then replay only its two new owners."""
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
SCIENCE_ATTEMPTS = [('Fibre','006'),('Consumer','002')]
PREFIX = 'CP782_CONTROL '
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
    paths = publication.get('paths') or publication.get('protected_paths') or publication['owned_paths']
    require(cert['checkpoint']==checkpoint and cert['verdict']=='certified' and set(cert['axioms'])==AXIOMS and
            sha(manifest)==(publication.get('manifest_sha256') or publication['package_manifest_sha256']) and
            all(str(path.relative_to(repo)) in paths and tracked(repo,revision,path)==sha(path)
                for path in (certificate_path,manifest)),checkpoint+' tracked publication drift')
    member, = [row for row in signed.get('members',signed.get('files')) if row['path']=='certificate.json']
    exact({**member,'path':str(certificate_path)})
    if 'certificate_sha256' in publication:
        require(sha(certificate_path)==publication['certificate_sha256'],checkpoint+' certificate drift')
    return publication,cert,signed


def signed_member(cert_path, manifest, name):
    row, = [item for item in manifest.get('members',manifest.get('files')) if item['path']==name]
    return exact({**row,'path':str(cert_path.parent/name)})


def bind_signed_stage(repo, binding, checkpoint):
    stage_path,publication,cert_path = (exact(binding[key]) for key in ('stage_map','publication','certificate'))
    pub,cert,manifest = signed_package(repo,checkpoint,publication,cert_path)
    inputs = signed_member(cert_path,manifest,'inputs.json')
    prior = read(inputs)
    stage_hash = prior['stage_map']['sha256'] if 'stage_map' in prior else prior['frozen_inputs']['stage-map.json']
    require(sha(inputs)==cert['inputs']['sha256'] and sha(stage_path)==stage_hash and
            pub.get('stage_map_sha256',stage_hash)==stage_hash,checkpoint+' signed stage view drift')
    return stage_path,read(stage_path),pub,cert,cert_path,manifest,prior


def verify_owned_parent(repo, row, hit, signed):
    _,prior,pub,cert,*_ = signed
    owner, = [item for item in prior['modules'] if item['module']==row['module']]
    promotion = read(exact(cert['main_promotion']))
    promoted, = [item for item in promotion['inputs'] if item['module']==row['module']]
    receipt = read(exact(owner['receipt']))
    source = repo/row['main']
    require(row['main'] in pub['paths'] and owner['main']==row['main'] and
            tracked(repo,pub['commit'],source)==sha(exact(owner['source']))==sha(receipt['source_snapshot'])==
                row['source_sha256']==receipt['source_sha256']==promoted['source_sha256'] and
            hit.samefile(exact(owner['object'])) and hit.samefile(exact(receipt['object'])) and
            promoted['object_sha256']==row['object']['sha256'] and
            promoted['receipt_sha256']==owner['receipt']['sha256'] and
            receipt['exit_code']==receipt['old_compilations']==0 and receipt['source_unchanged'] and
            set(FLAGS[:3])<=set(receipt['command']) and promotion['exact'] and
            promotion['stage_map_sha256']==pub['stage_map_sha256'],
            'original signed parent source, receipt or inode drift '+row['module'])


def archive_member(archive, base, record):
    member = Path(record['path']).relative_to(base).as_posix()
    data = subprocess.check_output(['tar','--zstd','-xOf',str(archive),member])
    require(('bytes' not in record or len(data)==record['bytes']) and
            hashlib.sha256(data).hexdigest()==record['sha256'],'original archived evidence drift '+member)
    return data


def verify_receipt_owner(repo, row, hit, signed):
    stage_path,prior,pub,cert,cert_path,manifest,inputs = signed
    owner, = [item for item in prior['inputs'] if item['module']==row['module']]
    science, = [item for item in inputs['science'] if item['module']==row['module']]
    construction = read(signed_member(cert_path,manifest,'evidence/science-compiles.json'))
    original, = [item for item in construction['stages'] if item['module']==row['module']]
    base = stage_path.parent
    cold = read(base/'cold/closeout.json')
    recovery = cold['packages']['construction']
    archive = exact({'path':recovery['archive'],'sha256':recovery['archive_sha256'],
        'bytes':recovery['compressed_bytes']})
    require(cold['publication_commit']==pub['commit'] and cold['certificate_sha256']==sha(cert_path) and
            recovery['publication_commit']==pub['commit'],'CP514 original cold receipt binding drift')
    receipt = json.loads(archive_member(archive,base,owner['receipt']))
    archive_member(archive,base,{'path':receipt['source']['snapshot'],'sha256':row['source_sha256']})
    require(row['main'] in pub['owned_paths'] and science['intended_formal_path']==row['main'] and
            tracked(repo,pub['commit'],repo/row['main'])==science['source_sha256']==owner['source_sha256']==
                receipt['source']['sha256']==row['source_sha256'] and
            hit.samefile(exact(owner['object'])) and hit.samefile(exact(receipt['object'])) and
            science['artifact_sha256']==row['object']['sha256'] and
            original['receipt_sha256']==owner['receipt']['sha256'] and owner['final_attempt']=='004' and
            original['snapshot_sha256']==row['source_sha256'] and original['log_sha256']==receipt['log']['sha256'] and
            receipt['exit_code']==0 and receipt['source_unchanged'] and set(FLAGS[:3])<=set(receipt['command']),
            'CP514 signed Receipt owner, archived strict source or selected inode drift')


def verify_cp329(repo, stage, roots, modules):
    binding = stage['bindings']['CP329']
    results_path,config_path,verdict_path,production_path = (exact(binding[key]) for key in
        ('results','config','verdict','production_binding'))
    results,config,verdict,production = map(read,(results_path,config_path,verdict_path,production_path))
    manifest_path = exact({'path':str(verdict_path.with_name('manifest.json')),'sha256':verdict['manifest_sha256']})
    manifest = read(manifest_path)
    require(verdict['Verdict']==manifest['verdict']=='certified' and manifest['checkpoint']=='CP329' and
            verdict['trust0_warningAsError_asyncFalse'] and verdict['defects']==[] and set(verdict['axioms'])==AXIOMS and
            manifest['production_binding_sha256']==sha(production_path) and
            Path(production['fresh_parent_results']).samefile(results_path) and
            production['fresh_parent_results_sha256']==sha(results_path) and
            production['all_10_focused_trust0_werror_asyncfalse_exit0'] and production['no_old_flat_core_scope'] and
            production['copied_library_bytes']==config['copied_library_bytes']==0 and set(FLAGS[:3])<=set(config['flags']),
            'CP329 signed original focused production and exact affected results drift')
    for module in modules:
        row = results[module]
        source = Path(row['source'])
        artifact = first_hit(module,roots)
        require(row['module']==module and row['exit_code']==0 and row['source_unchanged'] and
                sha(source)==tracked(repo,config['head'],source)==tracked(repo,stage['project_head'],source)==
                    row['source_sha256'] and artifact.samefile(row['olean']) and sha(artifact)==row['olean_sha256'],
                'CP329 original selected source or object drift '+module)
        for dependency,digest in row['affected_imports'].items():
            require(sha(first_hit(dependency,roots))==digest,'CP329 affected parent first hit drift '+dependency)


def inherited_edge(repo, signed, roots, name, count):
    _,prior,_,cert,cert_path,manifest,_ = signed
    summary_path = signed_member(cert_path,manifest,'audit-summary.json')
    summary = read(summary_path)
    key = f'old_{name}_consumed_CIs'
    edge = read(exact(prior['old_edge']))
    current = exact(prior['selected_old_'+name])
    earlier = exact(prior['earlier_old_'+name])
    parts = current.with_suffix('').parts
    module = '.'.join(parts[parts.index('SaturationMonoid'):])
    require(sha(summary_path)==cert['audit_summary']['sha256'] and summary['accepted'] and
            summary[key]==cert['counts'][key]==len(edge['used_exact'])==count and
            first_hit(module,roots).samefile(current) and current.samefile(edge['comparison']['selected']) and
            earlier.samefile(edge['comparison']['earlier']),'inherited '+name+' first-hit and certificate drift')


def verify_parents(repo, stage, roots, inputs):
    bindings = stage['bindings']
    signed = {key:bind_signed_stage(repo,bindings[key],key)
              for key in ('CP781','CP780','CP778','CP530','CP514')}
    division_path,division,_,cert,*_ = signed['CP781']
    require(roots[1]==division_path.parent/'lib' and
            [str(path) for path in roots[1:]]==exact(division['lean_path']).read_text().strip().split(os.pathsep) and
            roots[2]==signed['CP780'][0].parent/'lib' and roots[3]==signed['CP530'][0].parent/'lib' and
            division['bindings']['CP780']==bindings['CP780'] and division['bindings']['CP530']==bindings['CP530'] and
            cert['default_main_static']['verdict']=='exact-inputs-verified',
            'CP781 original Division view or inherited authorities drift')

    gate_owner, = division['modules']
    gate_module = gate_owner['module']
    require(inputs['gate_only']==[gate_module],'original Division Gate-only scope drift')
    gate_row = {**gate_owner,'source_sha256':gate_owner['source']['sha256']}
    gate_hit = first_hit(gate_module,roots)
    require(gate_hit.samefile(first_hit(gate_module,roots[1:])),'original Division Gate first hit drift')
    verify_owned_parent(repo,gate_row,gate_hit,signed['CP781'])
    inherited_edge(repo,signed['CP781'],roots,'factory',3)
    inherited_edge(repo,signed['CP780'],roots,'clock',6)

    paid = stage['paid_inputs']
    require(len(paid)==len({row['module'] for row in paid})==4,'exact paid input scope drift')
    direct = set()
    cp329 = []
    for row in paid:
        module,anchor = row['module'],row['anchor']
        relative = Path(*module.split('.')).with_suffix('.olean')
        source = repo/row['main']
        hit = first_hit(module,roots)
        require(row['main']=='Lean/'+relative.with_suffix('.lean').as_posix() and
                sha(source)==tracked(repo,stage['project_head'],source)==row['source_sha256'] and
                hit==Path(row['first_hit']) and hit.samefile(exact(row['object'])) and row['old_direct'],
                'frozen paid first hit drift '+module)
        if anchor in ('CP780','CP778'):
            verify_owned_parent(repo,row,hit,signed[anchor])
        elif anchor=='CP514':
            verify_receipt_owner(repo,row,hit,signed['CP514'])
        else:
            require(anchor=='CP329' and hit.samefile(roots[3]/relative),'original CP329 inherited object drift '+module)
            cp329.append(module)
        direct.add(module)
    require(len(direct)==len(stage['old_direct'])==4 and direct==set(stage['old_direct']) and len(cp329)==1,
            'four exact direct parents required')
    verify_cp329(repo,stage,roots,cp329)

    word, = [row for row in paid if row['module'].endswith('.Feed.Action')]
    edge = stage['donor_edge']
    admission = first_hit(edge['module'],roots)
    prior_action_view = exact(signed['CP778'][1]['lean_path']).read_text().strip().split(os.pathsep)
    require(first_hit(word['module'],roots).is_symlink() and edge['same_inode'] and
            admission==Path(edge['selected']) and admission.samefile(edge['earlier']) and
            admission.samefile(exact(edge['object'])) and
            admission.samefile(first_hit(edge['module'],list(map(Path,prior_action_view)))) and
            signed['CP778'][3]['counts']['inherited_Admission_CIs']==91,
            'original Feed.Action and Admission donor edge drift')
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
            len(records)==inputs['counts']['construction_calls']==9 and
            sum(row['exit_code']!=0 for row in cost['attempts'])==6 and
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
    require(stage['checkpoint']=='CP782' and view.samefile(args.base_lean_path_file) and
            exact(stage['toolchain']).samefile(args.repo/'Lean/lean-toolchain') and
            exact(stage['lake_manifest']).samefile(args.repo/'Lean/lake-manifest.json'),
            'frozen view, toolchain or Lake package identity drift')
    roots = [Path(path) for path in view.read_text().strip().split(os.pathsep)]
    require(args.compiled_root.resolve()==roots[0].resolve() and roots[0]==base/'lib',
            'candidate compiled root drift')
    direct = verify_parents(args.repo,stage,roots,inputs)
    verify_construction(base,stage,inputs)
    inventory = read(exact(stage['raw_inventory']))
    require(inventory['regions_read']==len(inventory['rows'])==len(stage['modules'])==len(SCIENCE_ATTEMPTS)==2,
            'two selected science owners required')
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
            re.findall(r'^import\s+(\S+)',(package/'Gate.lean').read_text(),re.M)==[inputs['entry'],*inputs['gate_only']] and
            sum(row['raw'] for row in stage['modules'])==stage['raw']==46 and
            sum(row['private'] for row in stage['modules'])==stage['private']==33 and
            sum(row['compiler_extra'] for row in stage['modules'])==574,'direct imports or exact selected counts drift')
    return inputs,roots,stage,modules


def validate_report(report, inputs, stage):
    replay, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and report['fresh_raw_regions']==2 and report['paid_base_environment_imports']==1 and
            report['full_candidate_environment_imports']==0 and not replay['base_has_unverified_sources'] and
            report['safe_private_original_CIs']==report['fresh_safe_replayed_CIs']==replay['kernel_calls']==
                replay['raw']==replay['fresh_replayed']==counts['logical']==46 and
            replay['inherited']==replay['duplicates']==0 and replay['compiler_runtime']==replay['inductive_generated_CIs']==[] and
            sum(row['name'].startswith('_private.') for row in replay['declarations'])==counts['private']==33 and
            replay['compiler_extras']==counts['compiler_extras']==574 and
            set(report['axioms'])==AXIOMS and report['source_target_reads']==[] and
            all(report['born_affine_receipt_fibre_ancestry'].values()) and len(report['born_affine_receipt_fibre_ancestry'])==5 and
            len(report['public_mouths'])==counts['public_mouths']==11 and
            len(report['source_body_bindings'])==counts['body_bindings']==55 and
            len(report['source_type_bindings'])==counts['type_bindings']==53,
            'fresh CI, axiom or actual source contract drift')
    require(replay['label']==inputs['audit_label'] and len(replay['modules'])==len(stage['modules']),
            'wrong audited owner scope')
    for audited,row in zip(replay['modules'],stage['modules'],strict=True):
        require(audited['module']==row['module'] and audited['imports']==row['imports'] and
                sha(audited['selected_olean'])==row['object']['sha256'] and
                audited['raw']==row['raw'] and audited['compiler_extras']==row['compiler_extra'],
                'wrong audited owner '+row['module'])
    old = report['old_action_admission_edge']
    edge = stage['donor_edge']
    word, = [row for row in stage['paid_inputs'] if row['module'].endswith('.Feed.Action')]
    require(report['inherited_generated_full_CI_matches']==0 and
            old['consumer_module']==word['module'] and old['dependency_module']==edge['module'] and
            old['consumer']==word['first_hit'] and old['selected']==edge['selected'] and old['earlier']==edge['earlier'] and
            old['direct_import'] and old['kernel_replays']==0 and Path(old['selected']).samefile(old['earlier']),
            'old Feed.Action to Admission exact import drift')
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
        'paid_direct_imports':4,'gate_only_imports':1,'new_donor_links':1,'parent':'CP781',
        'original_R_view':'CP530','old_receipt':'CP514','original_common_action':'CP329',
        'old_admission_same_inode':True,'inherited_factory_consumed_CIs':3,
        'inherited_clock_consumed_CIs':6,'lean_calls':0}
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
