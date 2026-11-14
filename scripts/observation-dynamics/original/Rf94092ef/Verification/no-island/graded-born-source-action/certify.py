#!/usr/bin/env python3
"""Verify CP779 on its frozen parent view, then replay only its four new owners."""
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
SCIENCE_ATTEMPTS = [('Birth','002'),('Native','002'),('Receipt','005'),('Consumer','002')]
PREFIX = 'CP779_CONTROL '
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
            sha(manifest)==publication['manifest_sha256'] and
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


def verify_parents(repo, stage, roots, inputs):
    bindings = stage['bindings']
    signed = {key:bind_signed_stage(repo,bindings[key],key if key!='Receipt' else 'CP514')
              for key in ('CP778','CP777','CP776','CP530','Receipt')}
    head_path,parent,parent_pub,parent_cert,*_ = signed['CP778']
    require(parent['checkpoint']==parent_pub['checkpoint']=='CP778' and
            parent_cert['default_main_static']['verdict']=='exact-inputs-verified' and
            parent['parent']==bindings['CP777'] and signed['CP777'][1]['parent']==bindings['CP776'] and
            [str(path) for path in roots[1:]]==exact(parent['lean_path']).read_text().strip().split(os.pathsep),
            'CP778 signed view or inherited native authorities drift')

    ancestor = bindings['CP477']
    aliases_path, handoff, cert_path = (exact(ancestor[k]) for k in ('aliases','handoff','certificate'))
    aliases = read(aliases_path)
    certificate = read(cert_path)
    require(all(ancestor[k]==signed['CP776'][1]['parent'][k] for k in ancestor) and
            len(aliases)==720 and exact(read(handoff)['full_aliases'])==aliases_path and
            certificate['verdict']=='PASS' and set(certificate['standard_axioms'])==AXIOMS and
            exact(certificate['frozen_capsule'])==handoff and
            read(exact(certificate['source_verdict']))['verdict']=='certified',
            'CP477 original alias authority drift')

    donor_path,donor,_,_,_,_,_ = signed['CP530']
    require(roots[-1]==donor_path.parent/'lib' and
            signed['CP777'][1]['donor']['stage_map']==bindings['CP530']['stage_map'],
            'CP530 inherited donor view drift')
    _,_,_,_,receipt_cert,receipt_manifest,_ = signed['Receipt']
    prior_edges = signed_member(receipt_cert,receipt_manifest,'evidence/paid-parents.json')
    rows = {row['module']:row for row in read(prior_edges)['rows']}
    relation, = [row for row in rows.values() if row['module'].endswith('.Action.Source.Relation')]
    input_binding_path = exact({'path':relation['evidence'],'sha256':relation['evidence_sha256']})
    earlier_transport, = [guard for guard in read(input_binding_path)['guards']
                           if isinstance(guard,dict) and guard.get('path','').endswith('/Occurrence/Transport.olean')]

    paid = stage['paid_inputs']
    require(len(paid)==len({row['module'] for row in paid})==9,'exact paid input scope drift')
    linked = set()
    for row in paid:
        module,anchor = row['module'],row['anchor']
        relative = Path(*module.split('.')).with_suffix('.olean')
        source = repo/row['main']
        hit = first_hit(module,roots)
        require(row['main']=='Lean/'+relative.with_suffix('.lean').as_posix() and
                sha(source)==tracked(repo,stage['project_head'],source)==row['source_sha256'] and
                hit==Path(row['first_hit']) and hit.samefile(exact(row['object'])),
                'frozen paid source, object or first hit drift '+module)
        if anchor in ('CP776','CP777') and not module.endswith('.Action.Source.Inventory'):
            verify_owned_parent(repo,row,hit,signed[anchor])
        elif anchor=='CP777':
            original, = [item for item in signed['CP777'][1]['supplement'] if item['module']==module]
            require(hit.samefile(exact(original['object'])) and row['source_sha256']==original['source_sha256'],
                    'CP777 original Inventory reuse drift')
        elif anchor=='CP477':
            original = aliases[module]
            require(hit.samefile(exact(original)) and sha(exact(original['source']))==row['source_sha256'],
                    'CP477 original paid alias drift '+module)
        elif anchor=='Receipt':
            verify_receipt_owner(repo,row,hit,signed['Receipt'])
            linked.add(module)
        else:
            require(anchor=='CP530' and hit.samefile(roots[-1]/relative),'CP530 donor object drift '+module)
            linked.add(module)
            if module.endswith('.Occurrence.Transport'):
                require(hit.samefile(exact(earlier_transport)),
                        'CP394–397 original Transport provider drift')
            else:
                original = rows[module]
                require(hit.samefile(original['selected_object']) and
                        original['object_sha256']==row['object']['sha256'] and
                        original['source_sha256']==row['source_sha256']==tracked(repo,original['source_git_anchor'],source) and
                        original['paid']['exit_code']==0,
                        'CP514 signed source dependency drift '+module)
                exact({'path':str(repo/original['evidence']),'sha256':original['evidence_sha256']})
    require(len(linked)==4 and all(first_hit(module,roots).is_symlink() for module in linked),
            'four exact donor symlinks required')
    direct = {row['module'] for row in paid if row['old_direct']}
    require(len(direct)==len(stage['old_direct'])==6 and direct==set(stage['old_direct']),
            'six exact direct parents required')

    edge = read(exact(stage['old_edge']))
    compared = edge['comparison']
    bound = inputs['stock_edge_objects']
    old_stock = Path(compared['earlier'])
    new_stock = first_hit(bound['stock_module'],roots)
    actual_transport = first_hit(bound['consumer_module'],roots)
    require(actual_transport.samefile(exact(earlier_transport)) and actual_transport.samefile(edge['consumer']) and
            new_stock.samefile(compared['selected']) and old_stock.samefile(roots[-1]/
                Path(*bound['stock_module'].split('.')).with_suffix('.olean')) and
            sha(old_stock)==bound['earlier_sha256'] and sha(new_stock)==bound['selected_sha256'] and
            compared['earlierCIs']==compared['selectedCIs']==13 and
            compared['sameImportNames'] and compared['sameCompilerExtraNames'] and len(edge['used_exact'])==3 and
            len(compared['added'])==len(compared['missing'])==len(compared['different'])==1 and
            compared['different'][0]['name'].endswith('.preserves_length') and
            compared['different'][0]['sameType'] and compared['different'][0]['sameLevelParams'] and
            not compared['different'][0]['sameStoredInfo'] and not compared['different'][0]['sameBody'],
            'old Transport to Stock consumed-edge evidence drift')
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
            len(records)==inputs['counts']['construction_calls']==12 and
            sum(row['exit_code']!=0 for row in cost['attempts'])==7 and
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
    require(stage['checkpoint']=='CP779' and view.samefile(args.base_lean_path_file) and
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
            sum(row['raw'] for row in stage['modules'])==stage['raw']==43 and
            sum(row['private'] for row in stage['modules'])==stage['private']==12 and
            sum(row['compiler_extra'] for row in stage['modules'])==266,'direct imports or exact selected counts drift')
    return inputs,roots,stage,modules


def validate_report(report, inputs, stage):
    replay, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and report['fresh_raw_regions']==4 and report['paid_base_environment_imports']==1 and
            report['full_candidate_environment_imports']==0 and not replay['base_has_unverified_sources'] and
            report['safe_private_original_CIs']==report['fresh_safe_replayed_CIs']==replay['kernel_calls']==
                replay['raw']==replay['fresh_replayed']==counts['logical']==43 and
            replay['inherited']==replay['duplicates']==0 and replay['compiler_runtime']==replay['inductive_generated_CIs']==[] and
            sum(row['name'].startswith('_private.') for row in replay['declarations'])==counts['private']==12 and
            replay['compiler_extras']==counts['compiler_extras']==266 and
            set(report['axioms'])==AXIOMS and report['source_target_reads']==[] and
            all(report['graded_born_source_action_ancestry'].values()) and len(report['graded_born_source_action_ancestry'])==5 and
            len(report['public_mouths'])==counts['public_mouths']==15 and
            len(report['source_body_bindings'])==counts['body_bindings']==63 and
            len(report['source_type_bindings'])==counts['type_bindings']==65,
            'fresh CI, axiom or actual source contract drift')
    require(replay['label']==inputs['audit_label'] and len(replay['modules'])==len(stage['modules']),
            'wrong audited owner scope')
    for audited,row in zip(replay['modules'],stage['modules'],strict=True):
        require(audited['module']==row['module'] and audited['imports']==row['imports'] and
                sha(audited['selected_olean'])==row['object']['sha256'] and
                audited['raw']==row['raw'] and audited['compiler_extras']==row['compiler_extra'],
                'wrong audited owner '+row['module'])
    old = report['old_consumed_stock_edge']
    edge = read(exact(stage['old_edge']))
    compared = edge['comparison']
    bound = inputs['stock_edge_objects']
    require(report['inherited_generated_full_CI_matches']==0 and
            old['consumer_module']==bound['consumer_module'] and old['stock_module']==bound['stock_module'] and
            Path(old['consumer']).samefile(edge['consumer']) and
            Path(old['earlier']).samefile(compared['earlier']) and Path(old['selected']).samefile(compared['selected']) and
            old['full_CI_matches']==edge['used_exact'] and old['kernel_replays']==0 and
            old['unused_added']==compared['added'] and old['unused_removed']==compared['missing'] and
            old['unused_changed']==[entry['name'] for entry in compared['different']],
            'old Transport consumed Stock proof scope drift')
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
        'paid_direct_imports':6,'supplement_links':4,'parent':'CP778','retained_receipt':'CP514',
        'old_stock_consumed_CIs':3,'lean_calls':0}
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
