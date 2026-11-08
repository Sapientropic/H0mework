"""Independent consumer of full-return privacy proofs and literal two-history outputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/Privacy/'
NAMES = ('Step', 'Words', 'Windows', 'Origin', 'Observation', 'Packets', 'Complete', 'Adaptive', 'PrivateStock', 'AuditLaw', 'Governance', 'Supply', 'Source')
MOUTHS = ('Twin.valid', 'Twin.step', 'Twin.attempt', 'Twin.next', 'Twin.window_word', 'Twin.handoff_word',
          'WindowTwin.current', 'WindowTwin.openPaid', 'WindowTwin.nextWindow', 'SeedTwin.current',
          'original_twin', 'Twin.rows', 'Twin.packets', 'handoff_packets_are_original',
          'continuation_packets_are_original', 'WindowTwin.complete', 'SeedTwin.complete',
          'WindowTwin.phases', 'WindowTwin.response', 'every_adaptive_finite_prefix_has_identical_complete_output',
          'WindowTwin.envelope', 'energy_private_step', 'energy_private_execute',
          'window_keeps_own_private_feed', 'handoff_keeps_own_private_feed',
          'AuditLaw.valid', 'AuditLaw.step', 'AuditLaw.all_valid',
          'GovernancePrivacy.original_emit_next', 'GovernancePrivacy.current', 'GovernancePrivacy.response',
          'GovernancePrivacy.private_step', 'rebuilt_replies_equal', 'source_plans', 'PlanTwin.paid',
          'PlanTwin.after', 'PlanTwin.available', 'PlanTwin.epoch', 'original_source_generates_initial_windows',
          'source_response_equal', 'every_original_source_strategy_preserves_complete_cumulative_privacy',
          'every_decoded_source_strategy_preserves_all_output')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


def kernel(lean, env, source, log, expected):
    process = subprocess.run([str(lean), '--trust=0', '-j1', '-DElab.async=false', '-DwarningAsError=true', str(source)],
                             cwd=ROOT/'Lean', env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write_text(process.stdout)
    assert process.returncode == 0, f'独立内核检查失败：{log}\n{process.stdout[-6000:]}'
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", process.stdout)
    assert {name for name, _ in rows} == set(expected), ('AXIOM_MOUTH_COVERAGE', rows)
    for name, axioms in rows:
        assert set(filter(None, map(str.strip, axioms.split(',')))) <= {'propext', 'Classical.choice', 'Quot.sound'}, name
    return len(rows)


def audit(box, run, out):
    out.mkdir(parents=True, exist_ok=False)
    receipt = load(run/'accepted.json')
    required = {f'Lean/{PREFIX}{name}.lean' for name in NAMES} | {
        f'Lean/scripts/verification/public-{feature}-source.lean' for feature in ('energy', 'continuation', 'handoff')}
    required.add('Lean/scripts/verification/public-privacy-check.py')
    assert set(receipt['inputs']) == required
    for path in sorted(required):
        assert sha(ROOT/path) == receipt['inputs'][path], ('SOURCE_BYTES', path)
    for name in NAMES:
        assert sha(run/'lib'/(PREFIX+name+'.olean')) == receipt['compiled_modules'][name], name
    assert sha(run/'source-family.lean') == receipt['generated_family_sha256']
    assert sha(run/'export-contracts.lean') == receipt['export_contracts_sha256']
    assert sha(run/'native-input.jsonl') == receipt['request_sha256']
    assert sha(run/'native.stdout') == receipt['output_sha256']
    assert (run/'native.stderr').read_bytes() == b''
    assert sha(box/'ha/handoff/native/closure.json') == receipt['closure_sha256']
    pin = (ROOT/'Lean/lean-toolchain').read_text().strip().replace(':', '---').replace('/', '--')
    lean = Path.home()/'.elan/toolchains'/pin/'bin/lean'
    assert sha(lean) == receipt['compiler_sha256']

    requests = [json.loads(line) for line in (run/'native-input.jsonl').read_text().splitlines()]
    answers = [json.loads(line) for line in (run/'native.stdout').read_text().splitlines()]
    assert len(requests) == len(answers) == 48
    assert answers[0] == load(run/'original-return.json'), 'ORIGINAL_FULL_LITERAL'
    assert answers[0]['next']['holder'] == answers[0]['actor'] == answers[0]['candidate'] == 2
    assert [row['kind'] for row in answers[0]['rows']] == ['revoke','transfer','transfer','propose','accept','use','use']
    assert answers[0]['before']['energy'] == ['2','0','0','3'] and answers[0]['next']['energy'] == ['0']*4
    for pair in (13, 14, 15, 18, 19, 21):
        assert answers[2*pair] == {'error':'ORIGINAL_SUPPLY_NOT_READY'}, ('SOURCE_REFUSAL', pair)
    assert answers[32] == {'error':'SOURCE_ORDER'}
    for pair in (17, 20):
        assert answers[2*pair]['reason'] == 'DELIVERED' and len(answers[2*pair]['packets']) == 1
    assert [item['cut'] for item in requests[38]['replies']] == [20, 12]
    assert requests[40]['replies'][0] == requests[40]['replies'][1]
    commands, actors, errors, leaks = set(), set(), set(), set()
    for i in range(0, len(requests), 2):
        left, right = requests[i:i+2]
        assert left['privateLarger'] is False and right['privateLarger'] is True
        assert {k:v for k,v in left.items() if k != 'privateLarger'} == {k:v for k,v in right.items() if k != 'privateLarger'}
        mode = left['mode']
        a, b = answers[i:i+2]
        if mode in ('private-error', 'private-metadata'):
            if mode == 'private-error':
                assert a == {'error':'39'} and b == {'error':'38'}
            else:
                assert a['native'] == b['native'] == answers[0]
                assert a['metadata'] == '39' and b['metadata'] == '38'
            leaks.add(mode)
            continue
        assert a == b, ('COMPLETE_VALUE', i)
        if 'error' in a:
            errors.add(a['error'])
        elif mode == 'continuation':
            commands.add(left['phases'][-1][-1]['op'])
        elif len(left['handoffs']) == 2:
            actors.add(left['handoffs'][-1]['actor'])
    assert commands == {'read','repair','revoke','open','grant'}
    assert actors == {1,2,4,100003}
    assert errors == {'EMPTY_HANDOFF','EMPTY_PHASE','FIELD_MASK','ORIGINAL_SUPPLY_NOT_READY','SOURCE_ORDER'}
    assert leaks == {'private-error','private-metadata'}

    env = os.environ.copy()
    env['LEAN_PATH'] = str(run/'lib')
    namespace = PREFIX.replace('/', '.')
    mouths = [namespace+mouth for mouth in MOUTHS]
    capsule = out/'kernel.lean'
    capsule.write_text(''.join('import '+namespace+name+'\n' for name in ('Origin','Source','PrivateStock'))+
                       ''.join('#print axioms '+mouth+'\n' for mouth in mouths))
    count = kernel(lean, env, capsule, out/'kernel.log', mouths)
    contract = out/'export-contracts.lean'
    contract.write_text((run/'export-contracts.lean').read_text()+
                       '\n#print axioms ExportContracts.handoff\n#print axioms ExportContracts.continuation\n'+''.join('#print axioms ExportContracts.'+feature+'_source_plan\n' for feature in ('energy','continuation','handoff')))
    count += kernel(lean, env, contract, out/'export-contracts.log', ['ExportContracts.handoff','ExportContracts.continuation']+['ExportContracts.'+feature+'_source_plan' for feature in ('energy','continuation','handoff')])
    result = dict(source_inputs=len(required), strict_modules=len(NAMES), standard_axiom_mouths=count,
                  complete_pairs=22, private_leak_controls=2, original_return_equal=True,
                  receipt_sha256=sha(run/'accepted.json'), audit_source_sha256=sha(__file__),
                  scope='Original governance and supply generate both initial windows or exact refusal; all original-source adaptive complete outputs')
    (out/'accepted.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(f'INDEPENDENT FULL-OUTPUT PRIVACY PASS: {len(NAMES)} modules; {count} standard-axiom mouths; 22 complete pairs; 2 real private leaks detected', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('box',type=Path)
    parser.add_argument('run',type=Path)
    parser.add_argument('out',type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--source-only',action='store_true',help='Consume the historical source-semantic checkpoint explicitly')
    mode.add_argument('--network-run',type=Path,help='Consume the complete signed network experiment')
    parser.add_argument('--readout-only',action='store_true',help='Consume the historical source plus public-readout checkpoint explicitly')
    parser.add_argument('--online-run',type=Path,help='Consume original HA same-event execution and recovery evidence')
    parser.add_argument('--online-events-only',action='store_true',help='Consume the historical three-face event checkpoint explicitly')
    parser.add_argument('--timing-run',type=Path,help='Consume public-only HA epochs and exact private-frame reconstruction')
    args = parser.parse_args()
    box, run, out = args.box.resolve(), args.run.resolve(), args.out.resolve()
    if args.source_only:
        if args.online_run or args.readout_only or args.online_events_only or args.timing_run:
            parser.error('--source-only cannot consume online evidence')
        audit(box,run,out)
        return
    if args.readout_only and (args.online_run or args.online_events_only or args.timing_run):
        parser.error('--readout-only cannot consume online evidence')
    if args.online_events_only and args.timing_run:
        parser.error('--online-events-only cannot consume timing evidence')
    network = args.network_run
    if network is None:
        pointer = run.parent/'network-current.json'
        if not pointer.is_file():
            raise RuntimeError('NETWORK_PRIVACY_EVIDENCE_REQUIRED: use --network-run or explicit --source-only')
        selected = load(pointer)
        network = Path(selected['run'])
        if sha(network/'actual/accepted.json') != selected['receipt_sha256']:
            raise RuntimeError('NETWORK_PRIVACY_RECEIPT_BINDING')
    # Historical readout evidence cannot silently satisfy the online event gate.
    sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
    from privacy_compare import audit as network_audit
    timing = None
    if not args.readout_only and not args.online_events_only:
        actual = args.timing_run
        if actual is None:
            pointer = run.parent/'timing-current.json'
            if not pointer.is_file():
                raise RuntimeError('HA_TIMING_EVIDENCE_REQUIRED: use --timing-run or explicit --online-events-only')
            selected = load(pointer)
            actual = Path(selected['run'])
            if sha(actual/'accepted.json') != selected['receipt_sha256']:
                raise RuntimeError('HA_TIMING_RECEIPT_BINDING')
        evidence = load(actual/'accepted.json')
        if not {'source_inputs','files','public_epoch_closed_sha256','lanes'} <= evidence.keys():
            raise RuntimeError('HA_TIMING_ACTUAL_EVIDENCE_REQUIRED')
        timing = actual.resolve()
    out.mkdir(parents=True,exist_ok=False)
    if timing is not None:
        from ha_timing_check import audit as timing_audit
        timing_audit(timing,out/'timing')
        timing = load(out/'timing/accepted.json')
    online = None
    if not args.readout_only:
        actual = args.online_run
        if actual is None:
            pointer = run.parent/'online-current.json'
            if not pointer.is_file():
                raise RuntimeError('ONLINE_EVENT_EVIDENCE_REQUIRED: use --online-run or explicit --readout-only')
            selected = load(pointer)
            actual = Path(selected['run'])
            if sha(actual/'accepted.json') != selected['receipt_sha256']:
                raise RuntimeError('ONLINE_EVENT_RECEIPT_BINDING')
        from online_privacy_check import audit as online_audit
        online_audit(actual.resolve(),out/'online')
        online = load(out/'online/accepted.json')
    network_audit(network.resolve(),out/'network')
    audit(box,run,out/'source')
    source = load(out/'source/accepted.json')
    wire = load(out/'network/accepted.json')
    result = dict(mode='source-and-network',source=source,network=wire,
                  source_receipt_sha256=sha(out/'source/accepted.json'),
                  network_receipt_sha256=sha(out/'network/accepted.json'),
                  audit_source_sha256=sha(__file__))
    if online is not None:
        result.update(mode='source-network-and-online-events',online=online,
                      online_receipt_sha256=sha(out/'online/accepted.json'))
    if timing is not None:
        result.update(mode='source-network-online-and-timing',timing=timing,
                      timing_receipt_sha256=sha(out/'timing/accepted.json'))
    (out/'accepted.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(('SOURCE NETWORK ONLINE AND HA TIMING PRIVACY PASS: public-only epochs; complete own-root nexts; exact recovery' if timing is not None else
           'SOURCE NETWORK AND ONLINE EVENT PRIVACY PASS: actual private successors; same-event payment; exact recovery' if online is not None else
           'COMPLETE SOURCE AND NETWORK PRIVACY PASS: native governance/supply; full adaptive outputs; independent entropy and clock witnesses'),flush=True)


if __name__ == '__main__':
    main()
