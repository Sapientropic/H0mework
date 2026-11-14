#!/usr/bin/env python3
"""Verify CP776 on its frozen CP477 source and object view, then replay only the five new owners."""
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
SCIENCE_ATTEMPTS = [('Increment','001'),('Collapse','002'),('Column','004'),('Gram','003'),('Writeback','005')]
PREFIX = 'CP776_CONTROL '
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


def verify_parent(repo, stage, roots):
    parent = stage['parent']
    handoff_path,cert_path,alias_path,publication_path = map(exact,
        (parent['handoff'],parent['certificate'],parent['aliases'],parent['publication']))
    handoff,cert,aliases,publication = map(read,(handoff_path,cert_path,alias_path,publication_path))
    require(len(aliases)==publication['frozen_first_hit_count']==720 and
            exact(handoff['full_aliases'])==alias_path and
            exact(cert['frozen_capsule'])==exact(publication['frozen_capsule'])==handoff_path and
            exact(publication['independent_certificate'])==cert_path and
            publication['checkpoint']=='CP477' and publication['machine_finalized'] and
            publication['current_finalized'] and not publication['publication_current_selection_pending'] and
            cert['verdict']=='PASS' and set(cert['standard_axioms'])==AXIOMS and
            cert['parent_CI_or_old_getter_replay']==0 and
            cert['new_safe_private_CIs']==publication['certified_scope_safe_private_CIs']==342 and
            read(exact(cert['source_verdict']))['verdict']=='certified' and
            read(exact(cert['same_actual_completed_source_born_chain']))['verdict']=='PASS',
            'CP477 original signed capsule, alias view or same-chain evidence drift')
    owned = {row['module']:row for row in publication['owned_sources']}
    direct = stage['old_direct']
    require(len(direct)==len({row['module'] for row in direct})==4,'CP477 direct owner scope drift')
    for row in direct:
        module = row['module']
        alias = aliases[module]
        current_source = repo/row['main']
        historical = subprocess.check_output(['git','--no-optional-locks','cat-file','blob',
            stage['project_head']+':'+row['main']],cwd=repo)
        selected = first_hit(module,roots)
        require(row['parent']=='CP477' and row['main']=='Lean/'+module.replace('.','/')+'.lean' and
                sha(current_source)==sha(exact(alias['source']))==row['source_sha256']==
                    hashlib.sha256(historical).hexdigest() and
                selected==Path(row['first_hit']) and selected.samefile(exact(row['object'])) and
                selected.samefile(alias['path']) and sha(selected)==alias['sha256']==row['object']['sha256'],
                'CP477 direct source or object identity drift '+module)
        if module in owned:
            owner = owned[module]
            strict = read(exact(owner['receipt']))
            require(sha(exact(owner['frozen_source']))==strict['source']['sha256']==row['source_sha256'] and
                    selected.samefile(exact(owner['object'])) and selected.samefile(exact(strict['object'])) and
                    strict['strict_green'] and strict['exit_code']==strict['parent_recompile']==strict['parent_copies']==0 and
                    set(FLAGS[:3])<=set(strict['command']),
                    'CP477 original strict owner drift '+module)
    return {row['module'] for row in direct}


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
            len(records)==inputs['counts']['construction_calls']==16 and
            sum(row['exit_code']!=0 for row in cost['attempts'])==9 and
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
    require(stage['checkpoint']=='CP776' and view.samefile(args.base_lean_path_file) and
            exact(stage['toolchain']).samefile(args.repo/'Lean/lean-toolchain') and
            exact(stage['lake_manifest']).samefile(args.repo/'Lean/lake-manifest.json'),
            'frozen view, toolchain or Lake package identity drift')
    roots = [Path(path) for path in view.read_text().strip().split(os.pathsep)]
    require(args.compiled_root.resolve()==roots[0].resolve() and roots[0]==base/'lib',
            'candidate compiled root drift')
    direct = verify_parent(args.repo,stage,roots)
    verify_construction(base,stage,inputs)
    inventory = read(exact(stage['raw_inventory']))
    require(inventory['regions_read']==len(inventory['rows'])==len(stage['modules'])==len(SCIENCE_ATTEMPTS)==5,
            'five selected science owners required')
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
            sum(row['raw'] for row in stage['modules'])==stage['raw']==41 and
            sum(row['private'] for row in stage['modules'])==stage['private']==7 and
            sum(row['compiler_extra'] for row in stage['modules'])==1,'direct imports or exact selected counts drift')
    return inputs,roots,stage,modules


def validate_report(report, inputs, stage):
    replay, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and report['fresh_raw_regions']==5 and report['paid_base_environment_imports']==1 and
            report['full_candidate_environment_imports']==0 and not replay['base_has_unverified_sources'] and
            report['safe_private_original_CIs']==report['fresh_safe_replayed_CIs']==replay['kernel_calls']==
                replay['raw']==replay['fresh_replayed']==counts['logical']==41 and
            replay['inherited']==replay['duplicates']==0 and replay['compiler_runtime']==replay['inductive_generated_CIs']==[] and
            sum(row['name'].startswith('_private.') for row in replay['declarations'])==counts['private']==7 and
            replay['compiler_extras']==counts['compiler_extras']==1 and
            set(report['axioms'])==AXIOMS and report['source_target_reads']==[] and
            all(report['graded_column_action_ancestry'].values()) and len(report['graded_column_action_ancestry'])==5 and
            len(report['public_mouths'])==counts['public_mouths']==22 and
            len(report['source_body_bindings'])==counts['body_bindings']==70 and
            len(report['source_type_bindings'])==counts['type_bindings']==70,
            'fresh CI, axiom or actual source contract drift')
    require(replay['label']==inputs['audit_label'] and len(replay['modules'])==len(stage['modules']),
            'wrong audited owner scope')
    for audited,row in zip(replay['modules'],stage['modules'],strict=True):
        require(audited['module']==row['module'] and audited['imports']==row['imports'] and
                sha(audited['selected_olean'])==row['object']['sha256'] and
                audited['raw']==row['raw'] and audited['compiler_extras']==row['compiler_extra'],
                'wrong audited owner '+row['module'])
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
        'paid_direct_imports':4,'parent':'CP477','parent_alias_records':720,'lean_calls':0}
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
