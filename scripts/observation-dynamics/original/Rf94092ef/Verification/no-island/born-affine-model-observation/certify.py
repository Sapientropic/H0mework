#!/usr/bin/env python3
"""Verify CP783 on its frozen parent view, then replay only its new owner."""
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
SCIENCE_ATTEMPTS = [('Observation','001')]
COIMAGE = 'SaturationMonoid.GenericFoundation.Operations.Observed.Coimage'
CP330_AUTHORITY = {
    'manifest.json':'2a5d6d8ae50291272e8765194a5c81fde7f7869d0441d3bb655eefecf9ebc832',
    'verdict.json':'165b04605837b37701fac26aa6bf19462dec6d4cee862366c340d9b2e9076b1c',
    'production-binding.json':'06ef7135d49dc37bea76b9580ad2719e3209b475976f1bd38813d0fecc30277e',
}
CP267_AUTHORITY = {
    'base.json':'8302aa6281b6d3518059b439721e3555a9bc31a8c52766f3496433e9570a8017',
    'closure-binding.json':'389599414ce78a2e51f5ff69d5c943e48adbda567ba3aff13bcb19604ba3d888',
}
PREFIX = 'CP783_CONTROL '
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


def verify_cp330(repo, stage, roots, row):
    binding = stage['bindings']['CP330']
    result_path, config_path, publication_path = (exact(binding[key]) for key in
        ('results','config','publication'))
    config, publication = read(config_path), read(publication_path)
    authority = result_path.parents[2]/'iqa-original-r-query-sigma-independent-clean-20261017'
    manifest, verdict, production = (read(exact({'path':str(authority/name),'sha256':digest}))
        for name,digest in CP330_AUTHORITY.items())
    require(manifest['checkpoint']=='CP330' and manifest['verdict']==verdict['Verdict']=='certified' and
            not verdict['defects'] and verdict['trust0_warningAsError_asyncFalse'] and set(verdict['axioms'])==AXIOMS and
            manifest['independent_scope']['exit_code']==0 and
            verdict['manifest_sha256']==CP330_AUTHORITY['manifest.json'] and
            manifest['production_binding_sha256']==CP330_AUTHORITY['production-binding.json'] and
            Path(production['config']).samefile(config_path) and
            Path(production['results']).samefile(result_path) and
            production['config_sha256']==binding['config']['sha256'] and
            production['results_sha256']==binding['results']['sha256'] and
            production['copied_library_bytes']==production['parent_recompiles_by_certifier']==production['old_scope_replays']==0 and
            set(FLAGS[:3])<=set(config['flags']),
            'CP330 original signed PostDecoderRead production drift')
    module = row['module']
    result = read(result_path)[module]
    configured, = [item for item in config['items'] if item['module']==module]
    signed, = [item for item in production['production_sources'] if item['module']==module]
    src = repo/row['main']
    hit = first_hit(module,roots)
    require(row['main'] in publication['paths'] and Path(result['source']).samefile(src) and
            sha(src)==tracked(repo,publication['commit'],src)==sha(result['candidate'])==
                row['source_sha256']==configured['source_sha256']==configured['candidate_sha256']==
                signed['source_sha256']==signed['candidate_sha256']==result['source_sha256']==result['candidate_sha256'] and
            hit.samefile(result['olean']) and hit.samefile(signed['olean']) and
            sha(hit)==row['object']['sha256']==result['olean_sha256']==signed['olean_sha256'] and
            result['exit_code']==result['trust']==0 and result['warning_as_error'] and not result['async'] and
            result['imports']==configured['imports'],
            'CP330 original source, selected object or strict receipt drift '+module)
    edges = stage['paid_import_edges']
    require([edge['module'] for edge in edges]==result['imports']==
            re.findall(r'^import\s+(\S+)',src.read_text(),re.M),
            'CP330 actual PostDecoderRead import list drift')
    for edge in edges:
        dependency = edge['module']
        actual = first_hit(dependency,roots)
        require(actual==Path(edge['first_hit']) and actual.samefile(exact(edge['object'])) and
                sha(actual)==result['import_olean_sha256'][dependency],
                'CP330 paid original import object drift '+dependency)


def verify_generic_gate(repo, stage, roots, base):
    support = base.parent/'iqa-original-source-physical-init-actor'
    record, closure = (read(exact({'path':str(support/name),'sha256':digest}))
        for name,digest in CP267_AUTHORITY.items())
    signed = record['single_formal267']
    manifest, verdict = (read(exact(signed[name])) for name in ('manifest.json','verdict.json'))
    require(verdict['verdict']=='certified' and verdict['manifest']==signed['manifest.json'] and
            manifest['head']==verdict['fixed_head'],'CP267 gate support signature drift')
    imports = manifest['closure'][COIMAGE]['imports']
    for module in (COIMAGE,*imports):
        original = manifest['closure'][module]
        loaded = closure['closure'][module]
        clone, = manifest['reuse_artifacts'][module]
        source = repo/original['file']
        hit = first_hit(module,roots)
        require(hit.samefile(loaded['loaded_artifact']) and
                Path(clone['snapshot']).samefile(loaded['formal_artifact_authority']) and
                sha(hit)==sha(clone['snapshot'])==clone['sha256']==loaded['olean_sha256'] and
                sha(source)==sha(original['source'])==tracked(repo,signed['commit'],source)==
                    tracked(repo,stage['project_head'],source)==original['sha256']==loaded['sha256'] and
                original['imports']==loaded['imports'],
                'CP267 exact generic history Gate support drift '+module)


def verify_parents(repo, stage, roots, inputs):
    bindings = stage['bindings']
    signed = {key:bind_signed_stage(repo,bindings[key],key) for key in ('CP782','CP781','CP530')}
    previous_path, previous, _, certificate, *_ = signed['CP782']
    require(roots[1]==previous_path.parent/'lib' and
            [str(path) for path in roots[1:]]==exact(previous['lean_path']).read_text().strip().split(os.pathsep) and
            roots[2]==signed['CP781'][0].parent/'lib' and roots[4]==signed['CP530'][0].parent/'lib' and
            previous['bindings']['CP781']==bindings['CP781'] and previous['bindings']['CP530']==bindings['CP530'] and
            certificate['default_main_static']['verdict']=='exact-inputs-verified',
            'CP782 signed actual birth view or inherited authorities drift')
    _, division, *_ = signed['CP781']
    gate_owner, = division['modules']
    gate_module = gate_owner['module']
    require(inputs['gate_only']==[gate_module,COIMAGE],'exact Gate-only import scope drift')
    gate_row = {**gate_owner,'source_sha256':gate_owner['source']['sha256']}
    verify_owned_parent(repo,gate_row,first_hit(gate_module,roots),signed['CP781'])
    verify_generic_gate(repo,stage,roots,roots[0].parent)

    paid = stage['paid_inputs']
    require(len(paid)==len({row['module'] for row in paid})==2,'two distinct paid direct inputs required')
    direct = set()
    for row in paid:
        module = row['module']
        relative = Path(*module.split('.')).with_suffix('.olean')
        source = repo/row['main']
        hit = first_hit(module,roots)
        require(row['main']=='Lean/'+relative.with_suffix('.lean').as_posix() and
                sha(source)==tracked(repo,stage['project_head'],source)==row['source_sha256'] and
                hit==Path(row['first_hit']) and hit.samefile(exact(row['object'])) and row['old_direct'],
                'frozen paid first hit drift '+module)
        if row['anchor']=='CP782':
            verify_owned_parent(repo,row,hit,signed['CP782'])
        else:
            require(row['anchor']=='CP330','unexpected PostDecoderRead origin '+module)
            verify_cp330(repo,stage,roots,row)
        direct.add(module)
    require(len(direct)==len(stage['old_direct'])==2 and direct==set(stage['old_direct']) and
            {row['anchor'] for row in paid}=={'CP782','CP330'},'exact direct imports drift')
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
            len(records)==inputs['counts']['construction_calls']==2 and
            all(row['exit_code']==0 for row in cost['attempts']) and
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
    require(stage['checkpoint']=='CP783' and view.samefile(args.base_lean_path_file) and
            exact(stage['toolchain']).samefile(args.repo/'Lean/lean-toolchain') and
            exact(stage['lake_manifest']).samefile(args.repo/'Lean/lake-manifest.json'),
            'frozen view, toolchain or Lake package identity drift')
    roots = [Path(path) for path in view.read_text().strip().split(os.pathsep)]
    require(args.compiled_root.resolve()==roots[0].resolve() and roots[0]==base/'lib',
            'candidate compiled root drift')
    direct = verify_parents(args.repo,stage,roots,inputs)
    verify_construction(base,stage,inputs)
    inventory = read(exact(stage['raw_inventory']))
    require(inventory['regions_read']==len(inventory['rows'])==len(stage['modules'])==len(SCIENCE_ATTEMPTS)==1,
            'one selected science owner required')
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
            sum(row['raw'] for row in stage['modules'])==stage['raw']==23 and
            sum(row['private'] for row in stage['modules'])==stage['private']==22 and
            sum(row['compiler_extra'] for row in stage['modules'])==269,'direct imports or exact selected counts drift')
    return inputs,roots,stage,modules


def validate_report(report, inputs, stage):
    replay, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and report['fresh_raw_regions']==1 and report['paid_base_environment_imports']==1 and
            report['full_candidate_environment_imports']==0 and not replay['base_has_unverified_sources'] and
            report['safe_private_original_CIs']==report['fresh_safe_replayed_CIs']==replay['kernel_calls']==
                replay['raw']==replay['fresh_replayed']==counts['logical']==23 and
            replay['inherited']==replay['duplicates']==0 and replay['compiler_runtime']==replay['inductive_generated_CIs']==[] and
            sum(row['name'].startswith('_private.') for row in replay['declarations'])==counts['private']==22 and
            replay['compiler_extras']==counts['compiler_extras']==269 and
            set(report['axioms'])==AXIOMS and report['source_target_reads']==[] and
            all(report['born_affine_model_observation_ancestry'].values()) and len(report['born_affine_model_observation_ancestry'])==5 and
            len(report['public_mouths'])==counts['public_mouths']==1 and
            len(report['source_body_bindings'])==counts['body_bindings']==36 and
            len(report['source_type_bindings'])==counts['type_bindings']==37,
            'fresh CI, axiom or actual source contract drift')
    require(replay['label']==inputs['audit_label'] and len(replay['modules'])==len(stage['modules']),
            'wrong audited owner scope')
    for audited,row in zip(replay['modules'],stage['modules'],strict=True):
        require(audited['module']==row['module'] and audited['imports']==row['imports'] and
                sha(audited['selected_olean'])==row['object']['sha256'] and
                audited['raw']==row['raw'] and audited['compiler_extras']==row['compiler_extra'],
                'wrong audited owner '+row['module'])
    require(report['inherited_generated_full_CI_matches']==0,'unexpected inherited fresh CIs')
    edges = report['paid_post_decoder_import_edges']
    require(len(edges)==len(stage['paid_import_edges'])==2,'two original PostDecoderRead import edges required')
    for observed,expected in zip(edges,stage['paid_import_edges'],strict=True):
        require(observed['module']==expected['module'] and observed['selected']==expected['first_hit'] and
                observed['raw_direct_import'] and observed['kernel_replays']==0,
                'original raw PostDecoderRead import evidence drift')
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
        'paid_direct_imports':2,'gate_only_imports':2,'new_donor_links':0,'parent':'CP782',
        'original_R_view':'CP530','original_post_decoder':'CP330','post_decoder_exact_import_edges':2,
        'gate_division':'CP781','gate_observed_coimage':'CP267','lean_calls':0}
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
