#!/usr/bin/env python3
"""Verify the stored-prefix continuation, paid horizon, and original native writeback."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

FLAGS = ['--trust=0', '-DElab.async=false', '-DwarningAsError=true', '-DmaxErrors=1',
         '-j1', '-M32000', '-DstderrAsMessages=false']
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


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


def selected(module, roots):
    package = module.split('.')[0]
    for index, root in enumerate(roots):
        if (root/package).is_dir() or (root/(package+'.olean')).is_file():
            path = root/(module.replace('.', '/')+'.olean')
            require(path.is_file(), 'selected package root lacks '+module)
            return path, index
    raise RuntimeError('missing '+module)


def verify_signed_science(args, roots, stage_path, cert_path, checkpoint, module):
    old, = [row for row in read(stage_path)['inputs'] if row['module']==module]
    signed = read(cert_path)
    prior_path = cert_path.with_name('inputs.json')
    prior = read(prior_path)
    row, = [entry for entry in prior['science'] if entry['module']==module]
    hit,_ = selected(module,roots)
    formal = old.get('main') or old['intended_formal_path']
    require(signed['checkpoint']==checkpoint and signed['verdict']=='certified' and set(signed['axioms'])==AXIOMS and
            signed['inputs']['sha256']==sha(prior_path) and
            prior['frozen_inputs']['stage-map.json']==sha(stage_path) and
            formal==row['intended_formal_path'] and
            sha(args.repo/formal)==old['source_sha256']==row['source_sha256'] and
            hit.samefile(old['object']['path']) and sha(hit)==old['object']['sha256']==row['artifact_sha256'],
            'signed selected science drift '+module)
    return old


def verify_parent(args, roots, row):
    module = row['module']
    hit,_ = selected(module,roots)
    require(hit.samefile(row['object']) and hit.samefile(row['provider']) and
            sha(hit)==row['object_sha256'] and sha(args.repo/row['main'])==row['source_sha256'],
            'paid exact source/body drift '+module)
    checkpoint = {'NativeHistoryLookup':'CP592','PaidPivot':'CP595',
                  'ScheduledPriceMatrix':'CP591','CofinalPriceRecord':'CP590'}[module.rsplit('.',1)[-1]]
    stage_path,cert_path,receipt_path = [exact(row[key]) for key in ('signed_binding','certificate','receipt')]
    old = verify_signed_science(args,roots,stage_path,cert_path,checkpoint,module)
    receipt = read(receipt_path)
    require(old['source_sha256']==row['source_sha256'] and old['object']['sha256']==row['object_sha256'] and
            hit.samefile(old['object']['path']) and exact(old['receipt']).samefile(receipt_path) and
            receipt['source_unchanged'] and receipt['exit_code']==receipt['old_compilations']==0 and
            receipt['source_sha256']==row['source_sha256'] and receipt['object']['sha256']==row['object_sha256'] and
            hit.samefile(receipt['object']['path']) and set(FLAGS[:3])<=set(receipt['command']),
            'paid exact strict source or receipt drift '+module)


def verify_paid_row_lineage(args, roots, parents):
    lookup, = [row for row in parents if row['module'].endswith('.NativeHistoryLookup')]
    pivot, = [row for row in parents if row['module'].endswith('.PaidPivot')]
    pivot_cert = exact(pivot['certificate'])
    pivot_stage = exact(pivot['signed_binding'])
    candidate = pivot['module'].removesuffix('PaidPivot')+'CandidateRead'
    verify_signed_science(args,roots,pivot_stage,pivot_cert,'CP595',candidate)
    tape_cert = exact(lookup['certificate'])
    tape_stage = exact(lookup['signed_binding'])
    tape_inputs = read(tape_cert.with_name('inputs.json'))
    tape, = [row['module'] for row in tape_inputs['science'] if row['module'].endswith('.ScheduledNativeTape')]
    verify_signed_science(args,roots,tape_stage,tape_cert,'CP592',tape)
    tape_paid = tape_cert.with_name('evidence')/'paid-parents.json'
    require(sha(tape_paid)==tape_inputs['frozen_inputs']['paid-parent-bindings.json'], 'original tape paid binding drift')
    prices, = [r for r in read(tape_paid)['rows'] if r['module'].endswith('.ScheduledPriceMatrix')]
    verify_parent(args,roots,prices)
    price_stage, price_cert = map(exact, (prices['signed_binding'],prices['certificate']))
    sibling = prices['module'].removesuffix('ScheduledPriceMatrix')+'ScheduledNativePrice'
    verify_signed_science(args,roots,price_stage,price_cert,'CP591',sibling)
    price_inputs = read(price_cert.with_name('inputs.json'))
    price_paid = price_cert.with_name('evidence')/'paid-parents.json'
    require(sha(price_paid)==price_inputs['frozen_inputs']['paid-parent-bindings.json'], 'original sparse decoder paid binding drift')
    record, = [r for r in read(price_paid)['rows'] if r['module'].endswith('.CofinalPriceRecord')]
    verify_parent(args,roots,record)


def verify_original_whole(args, roots, lineage):
    cert_path = exact(lineage['certificate'])
    signed = read(cert_path)
    prior_path = cert_path.with_name('inputs.json')
    prior = read(prior_path)
    paid_path = exact(lineage['paid_binding'])
    require(signed['checkpoint']=='CP557' and signed['verdict']=='certified' and set(signed['axioms'])==AXIOMS and
            signed['inputs']['sha256']==sha(prior_path) and
            prior['frozen_inputs']['paid-parent-bindings.json']==sha(paid_path) and
            prior['local_evidence_sha256']['evidence/paid-parents.json']==sha(paid_path),
            'original same-root whole provenance drift')
    whole, = [r for r in read(paid_path)['rows'] if r['module']==lineage['module']]
    hit,_ = selected(whole['module'],roots)
    require(whole['module'].endswith('.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction') and
            hit.samefile(whole['object']) and hit.samefile(whole['provider']) and
            sha(hit)==whole['object_sha256'] and sha(args.repo/whole['main'])==whole['source_sha256'],
            'original same-root whole/next selected body drift')
    root_cert, = [read(exact(attachment)) for attachment in whole['bindings']]
    require(root_cert['checkpoint']=='CP541' and root_cert['verdict']=='certified' and
            set(root_cert['axioms'])==AXIOMS, 'original Division root certificate drift')


def verify_native_codegen(base, stage):
    cost = read(exact(stage['construction_cost']))
    report_path = base/'codegen-verification.json'
    report = read(report_path)
    require(report==cost['native_codegen'], 'generated C records disagree with frozen construction cost')
    logical_module = 'SaturationMonoid.GenericFoundation.Operations.Inquiry.NativeHistoryContinuation'
    selected, = [row for row in stage['inputs'] if row['module']==logical_module]
    require(selected['final_attempt']=='003', 'unexpected selected generic codegen stage')
    builds = {row['attempt']:row for row in cost['source_attempts']
              if row['stage']=='NativeHistoryContinuation'}
    for label,attempt in (('negative','002'),('selected','003')):
        obj = report[label]['source']
        path = exact(obj)
        require(path==base/'objects'/f'NativeHistoryContinuation-{attempt}.c' and builds[attempt]['exit_code']==0,
                'unexpected native codegen output path or attempt')
        require(path.read_text().splitlines()[1]=='// Module: '+logical_module, 'generated C module identity drift')
    strict = read(exact(selected['receipt']))
    command = strict['command']
    require(builds['003']['receipt']==selected['receipt'] and
            command[command.index('-c')+1]==report['selected']['source']['path'] and
            command[command.index('-o')+1]==selected['object']['path'] and strict['exit_code']==0,
            'selected OLean and generated C were not built in the same strict invocation')

    def parse(path):
        code = Path(path).read_text()
        bodies, calls = {}, []
        function = None
        for line_number,line in enumerate(code.splitlines(),1):
            header = re.match(r'^LEAN_EXPORT .* (\w+)\([^;]*\)\{',line)
            if header:
                function = header[1]
                bodies[function] = []
            if function is None:
                continue
            bodies[function].append(line)
            call = re.fullmatch(r'\s*(?:(\w+)\s*=\s*|return\s+)(\w+)\(([^;]*)\);\s*',line)
            if call:
                calls.append((function,line_number,line.strip(),call[1],call[2],
                              tuple(arg.strip() for arg in call[3].split(','))))
        return bodies,calls

    _, old = parse(report['negative']['source']['path'])
    bodies,new = parse(report['selected']['source']['path'])
    next_state = 'ExactActivatedInquiryOccurrenceAt_nextState'
    old_replay = [r for r in old if next_state in r[4]]
    require(len(old_replay)==1 and old_replay[0][0].endswith('HistoryAt_continueFor___lam__1') and
            not any(next_state in row[4] or 'State_tick' in row[4] for row in new), 'stored-prefix replay detected')
    suffix = [r for r in new if r[4].endswith(('SourceNativeInquiryRuntime_runFrom','SourceNativeInquiryRuntime_runFrom___redArg'))]
    require(len(suffix)==1 and suffix[0][0].endswith('HistoryAt_continueFor___lam__0'), 'unexpected new execution site')
    stored = [r for r in new if r[4].endswith('storedStart___redArg')]

    def row_record(row):
        return dict(function=row[0],line=row[1],expression=row[2])

    require([row_record(r) for r in old_replay]==report['negative']['old_next_calls'] and
            [row_record(r) for r in suffix]==report['selected']['suffix_execution'] and
            [row_record(r) for r in stored]==report['selected']['stored_reads'] and
            report['selected']['old_next_calls']==[], 'actual native call sites differ from frozen report')
    suffix_call, = suffix
    initial_read, = [row for row in stored if row[0]==suffix_call[0]]
    require(initial_read[1]<suffix_call[1] and suffix_call[5][-1]==initial_read[3],
            'suffix execution does not consume the stored reached state')
    for branch in ('HistoryAt_continueFor___lam__1','HistoryAt_storedOccurrenceAt___redArg___lam__1'):
        read_tail, = [row for row in stored if row[0].endswith(branch)]
        tail_call, = [row for row in new if row[0]==read_tail[0] and row[4]=='lean_apply_2']
        require(read_tail[1]<tail_call[1] and tail_call[5][1:]==(read_tail[3],read_tail[5][0]),
                'old-history recursion does not pass its stored state and exact tail')
    stored_body, = [body for name,body in bodies.items() if name.endswith('storedStart___redArg')]
    field_reads = re.findall(r'lean_ctor_get\((v_history_\d+_), ([01])\);','\n'.join(stored_body))
    require(len(field_reads)==2 and field_reads[0][0]==field_reads[1][0] and
            {field for _,field in field_reads}=={'0','1'} and any('lean_obj_tag' in line for line in stored_body),
            'stored start is not read directly from both history constructors')
    return {'negative_old_next_state_calls':1,'selected_old_next_state_calls':0,'selected_suffix_calls':1,
            'stored_state_passes_checked':3,'report_sha256':sha(report_path),
            'negative_c_sha256':report['negative']['source']['sha256'],
            'selected_c_sha256':report['selected']['source']['sha256']}


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
    require(len(science)==2 and frozen.keys()==science.keys()==strict.keys(),'science owner drift')
    science_actual = []
    for module,row in science.items():
        source = (args.source_root or args.repo/'Lean')/(module.replace('.','/')+'.lean')
        artifact,index = selected(module,roots)
        require(sha(source)==row['source_sha256']==frozen[module]['source_sha256'] and
                artifact.samefile(frozen[module]['object']['path']) and sha(artifact)==row['artifact_sha256']==frozen[module]['object']['sha256'] and
                artifact.stat().st_size==row['artifact_bytes'],'science source/body drift '+module)
        imports = re.findall(r'^import\s+(\S+)',source.read_text(),re.M)
        require(module.startswith('SaturationMonoid.') and module.endswith(('.GenericFoundation.Operations.Inquiry.NativeHistoryContinuation','.GammaSource.PositionGap.ResidualProbe.PaidContinuation')) and
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
                set(FLAGS[:3]) <= set(actual_receipt['command']) and actual_receipt['old_compilations']==0,
                'strict source/body receipt drift '+module)
        science_actual.append({**row,'selected_olean':str(artifact),'search_path_index':index})

    paid_path = package/'evidence/paid-parents.json'
    paid = read(paid_path)
    parents = paid['rows']
    imports = {m for row in science.values() for m in row['base']} - science.keys()
    require(paid['schema']=='paid-prefix-continuation-paid-parents/v1' and
            len(parents)==2 and parents==context['exact_paid_bodies'] and
            sha(paid_path)==inputs['frozen_inputs']['paid-parent-bindings.json'] and
            context['old_objects_copied']==paid['copies']==paid['old_compilations']==0 and
            imports==set(inputs['audit_base'])=={row['module'] for row in parents}, 'paid scope drift')
    require(exact(paid['selected_lean_path']).samefile(args.base_lean_path_file) and
            context['selected_lean_path']==paid['selected_lean_path'] and
            all(receipt['lean_path_sha256']==paid['selected_lean_path']['sha256'] for receipt in strict.values()),
            'strict selected view drift')
    output = read(exact(stage['output_location']))
    physical = Path(output['physical'])
    require(output['schema']=='owned-proof-stage-output-location/v1' and Path(output['logical'])==base and
            physical.is_relative_to('runtime/ and
            all((base/name).is_symlink() and (base/name).resolve()==physical/name
                for name in ('objects','source-root','receipts')) and
            all(Path(row['object']['path']).resolve().parent==physical/'objects' for row in frozen.values()),
            'second SSD output binding drift')
    for row in parents:
        verify_parent(args,roots,row)
    for ancestor in inputs['gate_signed_science']:
        verify_signed_science(args,roots,exact(ancestor['stage_map']),exact(ancestor['certificate']),
                              ancestor['checkpoint'],ancestor['module'])
    verify_original_whole(args,roots,inputs['whole_lineage'])
    verify_paid_row_lineage(args,roots,parents)
    native = verify_native_codegen(base,stage)
    expected = dict(inputs['native_codegen'])
    negative_receipt = expected.pop('negative_strict_receipt_sha256')
    cost = read(exact(stage['construction_cost']))
    old, = [row for row in cost['source_attempts']
            if row['stage']=='NativeHistoryContinuation' and row['attempt']=='002']
    require(native==expected and old['receipt']['sha256']==negative_receipt and
            native['report_sha256']==inputs['frozen_inputs']['codegen-verification.json'],
            'independently checked native suffix evidence drift')
    require(read(exact(stage['compiler_companions']))['companions']==[], 'unexpected compiler runtime companions')
    return inputs,roots,science_actual


def validate_report(path, inputs, actual):
    report = read(path)
    stage, = report['stages']
    counts = inputs['counts']
    require(report['accepted'] and stage['duplicates'] == 0 and
            stage['inherited'] == counts['inherited'] == report['inherited_generated_full_CI_matches'] and
            stage['fresh_replayed'] == counts['kernel_calls'] == report['fresh_safe_replayed_CIs'] and
            stage['fresh_replayed']+stage['inherited']==stage['raw'] and
            not stage['base_has_unverified_sources'] and not stage['compiler_runtime'] and
            report['fresh_raw_regions'] == 2 and report['paid_base_environment_imports'] == 1 and
            report['full_candidate_environment_imports'] == 0, 'replay escaped its subject-free base')
    owners = {r['module']:r for r in actual}
    for owner in stage['modules']:
        selected_owner = owners.pop(owner['module'])
        require(sha(owner['selected_olean']) == selected_owner['artifact_sha256'] and
                owner['raw'] == selected_owner['raw_CIs'] and owner['imports'] == selected_owner['raw_imports'] and
                owner['compiler_extras'] == selected_owner['compiler_extras'],
                'wrong audited owner '+owner['module'])
    require([r['name'] for r in stage['inherited_generated_full_CIs']]==inputs['inherited_generated_CIs'] and
            all(r['same_full_constant_info'] and not r['kernel_replayed']
                for r in stage['inherited_generated_full_CIs']), 'inherited CI qualification drift')
    require(not owners and report['safe_private_original_CIs'] == stage['raw'] == counts['safe'] and
            stage['kernel_calls'] == counts['kernel_calls'] and stage['compiler_extras'] == counts['extras'] and
            sum(r['name'].startswith('_private.') for r in stage['declarations']) == counts['private'] and
            len(report['public_mouths']) == counts['public_mouths'] and
            len(report['source_body_bindings']) == counts['body_bindings'] and
            len(report['source_type_bindings']) == counts['type_bindings'] and
            report['source_target_reads'] == [] and set(report['axioms']) == AXIOMS,
            'incomplete SCI or source provenance')
    binders = {r['name'].rsplit('.',1)[-1]:r['binders'] for r in report['public_mouths']}
    frame = ['observation','nontrivial','half','depth']
    book = [*frame,'start','count']
    stored = ['process','runtime','fuel','state','history']
    run = [*book,'priorLength','prior','within']
    expected = {
        'eq_runFrom':stored,
        'storedOccurrenceAt':[*stored,'a._@._internal._hyg.0'],
        'stored_occurrence_eq':[*stored,'i'],
        'continueFor':[*stored,'extra'],
        'extendTo':[*stored,'total','within'],
        'extendTo_prefix':[*stored,'total','within'],
        'preparationLength':book,
        'paidLatestTime':book,
        'paidContinuationLength':book,
        'actual_paid_latest_time':book,
        'actual_paid_continuation_length':book,
        'actual_retained_length':book,
        'NativeRun':[*frame,'length'],
        'preparePaidRun':run,
        'continuePaidRun':run,
        'actual_continued_preparation':run,
        'actual_continued_prefix':run,
        'preparedMaterial':[*book,'history','actor','row'],
        'continuedCandidate':[*run,'actor','offset'],
        'actual_continued_candidate':[*run,'actor','offset'],
        'actual_continued_selected':[*run,'actor'],
    }
    require(binders==expected, 'stored history or exact paid continuation input drift')
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
    save(output/'provenance.json',{'schema':'cp596-provenance/v1','science':actual,
        'formal_sources':args.source_root is None,'inputs_sha256':sha(package/'inputs.json'),
        'paid_direct_imports':2,'gate_ancestor_bindings':2,'verification_overlay_objects':0,'native_codegen':inputs['native_codegen'],'old_source_recompiles':0,'old_ci_replays':0})
    if args.verify_inputs_only:
        print(json.dumps({'verdict':'exact-inputs-verified','science':len(actual),
            'formal_sources':args.source_root is None,'paid_direct_imports':2,'gate_ancestor_bindings':2,'verification_overlay_objects':0,'lean_calls':0}))
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
        save(cost,{'schema':'cp596-independent-cost/v1','calls':calls,'actual_calls':len(calls),
            'known_seconds':sum(x['elapsed_seconds'] for x in calls),'old_ci_replays':0,'old_source_recompiles':0})
        if code:
            print(log.read_text()[-7000:],flush=True)
            raise SystemExit(code)
        return log

    gate = run('001-gate','Gate.lean',[str(lean),*FLAGS,str(package/'Gate.lean')],env)
    markers = [list(x) for x in re.findall(r'^CP596_CONTROL ([+-]) (\w+)$',gate.read_text(),re.M)]
    require(markers==inputs['typed_controls'],'typed controls drift')
    config = output/'audit-config.json'
    raw = output/'private-bodies.json'
    save(config,{'label':'cp596-paid-prefix-continuation','base':inputs['audit_base'],
        'modules':[{'name':r['module'],'selected':r['selected_olean'],'imports':r['raw_imports']} for r in actual],
        'output':str(raw),'progress':str(output/'ci-progress.jsonl'),'current':str(output/'current-ci.json')})
    run('002-audit','Audit.lean',[str(lean),*FLAGS,'--run',str(package/'Audit.lean'),str(config)],env)
    report = validate_report(raw,inputs,actual)
    save(output/'certificate.json',{'schema':'cp596-reproduction/v1','verdict':'certified','axioms':report['axioms'],
        'safe_private_original_CIs':report['safe_private_original_CIs'],
        'fresh_safe_replayed_CIs':report['fresh_safe_replayed_CIs'],'report_sha256':sha(raw),
        'inputs_sha256':sha(package/'inputs.json'),
        'cost_sha256':sha(cost),'old_ci_replays':0})
    print(json.dumps({'verdict':'certified','certificate':str(output/'certificate.json')}),flush=True)


if __name__ == '__main__':
    main()
