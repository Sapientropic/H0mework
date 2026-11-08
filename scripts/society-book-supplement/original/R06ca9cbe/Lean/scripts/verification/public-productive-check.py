"""Replay the productive source witness using original material recipes and payments."""
import argparse
from copy import deepcopy
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
from pathlib import Path


def load(path):
    return json.loads(Path(path).read_text())


def state(raw):
    result = deepcopy(raw)
    result['clock'] = Q(result['clock'])
    result['stock'] = {(a, g): Q(n) for a, g, n in raw['stock']}
    result['claims'] = {(i, a, b): Q(n) for i, a, b, n in raw['claims']}
    assert len(raw['stock']) == len(result['stock']) == 48
    assert len(raw['claims']) == len(result['claims']) == 147
    assert ('audit:3', 'feed') not in result['stock']
    return result


def amounts(entries):
    result = {}
    for a, g, n in entries:
        result[a, g] = result.get((a, g), Q(0)) + Q(n)
    return {k: v for k, v in result.items() if v}


def verify(witness, commands, parent, *, require_finance=True):
    assert witness['parent'][-1] == parent
    assert witness['initial'] == parent['next']
    initial = state(witness['initial'])
    current = deepcopy(initial)
    recipes = {
        'provider:0': ([['feed', 1], ['labor', 1]], [['energy', 2], ['labor', 3]]),
        'provider:1': ([['feed', 1], ['energy', 1], ['labor', 1]], [['life', 3], ['waste', 1]]),
        'provider:2': ([['waste', 1], ['energy', 1], ['labor', 1]], [['feed', 1]])}
    transfers = {
        ('audit:0', 'provider:0'): [['feed', '1']],
        ('audit:0', 'provider:1'): [['feed', '1']],
        ('provider:0', 'provider:1'): [['energy', '1'], ['labor', '1']],
        ('provider:0', 'provider:2'): [['energy', '1'], ['labor', '1']],
        ('provider:1', 'provider:2'): [['waste', '1']],
        ('provider:2', 'provider:0'): [['feed', '1']],
        ('audit:3', 'audit:0'): [['energy', '4']],
        ('audit:3', 'audit:1'): [['energy', '2']],
        ('audit:3', 'audit:2'): [['energy', '2']]}
    counts = dict(factory=0, recycling=0, fuel=0, births=0, settlements=0, rejected=0)
    origins = None
    count=len(commands)
    assert count in (9,14) and count==len(witness['output'])==len(witness['public'])
    for ordinal, (command, result) in enumerate(zip(commands, witness['output'])):
        public = {k: v for k, v in result.items() if k not in ('nativeBefore', 'nativeNext')}
        assert witness['public'][ordinal] == public, 'EXACT_PROVED_RENDERER'
        if 6 <= ordinal < 9:
            assert result['status'] == 'ERROR' and result['metadata'] == command
            assert set(result) == {'status', 'metadata', 'message'} and result['message']
            continue
        assert result['history'] == 21 + ordinal - (3 if ordinal>=9 else 0)
        current['clock'] += 1
        current['round'] += 1
        if command['kind'] == 'cycle':
            assert state(result['before']) == current
            assert result['metadata'] == command
            if require_finance:
                ledger = result['nativeBefore']
                if origins is not None:
                    assert ledger == origins
                assert ledger['slots'] == 12 + counts['births']
                assert Q(ledger['outstanding']) == current['claims']['delivery', 'provider:0', 'audit:3']
        for index, row in enumerate(result['rows']):
            assert row['index'] == index
            if 'before' in row:
                assert state(row['before']) == current
            action = row['request']; op = action['operation']; kind = op['kind']
            expected = deepcopy(current); debit = []; credit = []
            if kind == 'produce':
                actor = op['actor']; src, dst = recipes[actor]
                debit = [[actor, g, str(n)] for g, n in src]
                credit = [[actor, g, str(n)] for g, n in dst]
                assert action['purpose'] == dict(kind='provider', base='reserve', owner=int(actor[-1]))
                signer = actor
            elif kind == 'transfer':
                signer = op['from']
                assert op['bundle'] == transfers[op['from'], op['to']]
                if op['from']=='audit:3' and op['to'] in ('audit:1','audit:2'):
                    members=list(dict.fromkeys(slot['actor'] for slot in result['scope']['slots']))
                    replacement=next((a for a in members if a!=0 and a!=current['technology']['audit']['holder']),0)
                    assert op['to']=='audit:'+str(replacement)
                debit = [[op['from'], g, n] for g, n in op['bundle']]
                credit = [[op['to'], g, n] for g, n in op['bundle']]
                if op['from'] == 'audit:0':
                    assert current['claims']['delivery', 'provider:0', 'audit:3'] > 0
                    assert action['purpose'] == dict(kind='exchange')
            elif kind in ('issue', 'settle'):
                signer = 'provider:0'
                assert op['debtor'] == signer and op['creditor'] == 'audit:3'
                assert op['instrument'] == 'delivery' and Q(op['quantity']) == 2
                key = ('delivery', signer, 'audit:3')
                if kind == 'issue':
                    assert current['claims'][key] == 0
                    expected['claims'][key] += 2
                else:
                    assert current['claims'][key] >= 2
                    expected['claims'][key] -= 2
                    debit = [[signer, 'energy', '2']]; credit = [['audit:3', 'energy', '2']]
            elif kind == 'revise':
                signer = op['actor']
                assert signer in ('audit:0', 'audit:1', 'audit:2')
                debit = [[signer, 'energy', '1']]
                expected['technology'] = deepcopy(op['technology'])
                old = current['technology']; new = expected['technology']
                assert new['audit']['version'] == old['audit']['version'] + 1
                assert new['provider'] == old['provider']
                assert new['clockLag'] == old['clockLag'] and new['roundLag'] == old['roundLag']
            elif kind == 'use':
                signer = op['actor']
                assert op['purpose'] == 'external' and op['bundle'] == [['energy', '1']]
                debit = [[signer, 'energy', '1']]
            else:
                raise AssertionError('UNKNOWN_PRODUCTIVE_OPERATION')
            paid = action['signer'] == signer and all(current['stock'][k] >= n for k, n in amounts(debit).items())
            assert row['accepted'] == paid
            if paid:
                assert amounts(row['debit']) == amounts(debit) and amounts(row['credit']) == amounts(credit), 'ORIGINAL_RECIPE'
                for k, n in amounts(debit).items():
                    assert n >= 0; expected['stock'][k] -= n
                for k, n in amounts(credit).items():
                    assert n >= 0; expected['stock'][k] += n
                current = expected
                if kind == 'produce':
                    counts[{'provider:0': 'fuel', 'provider:1': 'factory', 'provider:2': 'recycling'}[op['actor']]] += 1
                elif kind == 'issue': counts['births'] += 1
                elif kind == 'settle': counts['settlements'] += 1
            else:
                counts['rejected'] += 1
                assert index == len(result['rows']) - 1
                assert row['debit'] == row['credit'] == []
            if 'after' in row:
                assert state(row['after']) == current
        current['clock'] += 1; current['round'] += 1
        assert state(result['next']) == current, 'ACTUAL_SUCCESSOR'
        for k, value in initial['claims'].items():
            if k[0] != 'delivery': assert current['claims'][k] == value, 'OLD_CLAIM'
        if command['kind'] == 'cycle':
            assert result['status'] == ('BLOCKED' if ordinal == 0 else 'PRODUCED')
            if require_finance:
                next_ledger = result['nativeNext']
                assert next_ledger['slots'] == 12 + counts['births']
                assert Q(next_ledger['outstanding']) == current['claims']['delivery', 'provider:0', 'audit:3']
                assert next_ledger['origins'][:ledger['slots']] == ledger['origins']
                assert len(next_ledger['origins']) == next_ledger['slots']
                origins = next_ledger
    cycles=3 if count==9 else 6
    assert counts == dict(factory=cycles, recycling=cycles, fuel=2*cycles, births=cycles, settlements=cycles, rejected=1)
    denied, resumed = witness['output'][:2]
    assert denied['rows'][-1]['request']['signer'] == 'audit:0'
    assert resumed['rows'][0]['request']['operation'] == dict(kind='produce', actor='provider:1')
    assert not any(r['request']['operation']['kind'] == 'transfer' and r['request']['operation']['from'] == 'provider:0'
                   for r in resumed['rows']), 'REPAID_BOOTSTRAP'
    assert current['stock']['audit:0', 'feed'] == 12-2*cycles
    assert current['stock']['provider:1', 'life'] == 3*cycles
    assert current['stock']['provider:1', 'waste'] == current['stock']['provider:2', 'waste'] == 0
    assert current['stock']['provider:0', 'labor'] == 26+2*cycles
    assert witness['output'][4]['status'] == 'OPENED' and witness['output'][5]['status'] == 'DELIVERED'
    if count==14:assert witness['output'][12]['status']=='OPENED' and witness['output'][13]['status']=='DELIVERED'
    assert witness['next'] == witness['output'][5 if count==9 else 13]['next']
    if require_finance:
        assert witness['native']['slots'] == 12+cycles and Q(witness['native']['outstanding']) == 0
        assert witness['native']['origins'] == origins['origins']
    return counts


def main():
    parser = argparse.ArgumentParser(); parser.add_argument('home', type=Path)
    args = parser.parse_args(); home = args.home
    request = load(home/'input.json'); witness = load(home/'output.json')
    rows = load(home.parent/'refeed/actual/events.json')
    assert len(rows) == 53
    parent = json.loads(rows[-1][3])['body']['native']
    assert request['parent'] == load(home.parent/'refeed/actual/source-input.json')
    counts = verify(witness, request['commands'], parent)
    spec = importlib.util.spec_from_file_location('productive_prior_check', Path(__file__).with_name('public-material-check.py'))
    prior = importlib.util.module_from_spec(spec); spec.loader.exec_module(prior)
    dual = 0
    for packet in witness['output'][5]['packets']:
        assert [e['slot'] for e in packet] == list(range(6))
        for evidence in packet:
            assert prior.old.privacy.original._dual.payment_scan(evidence['slot'], evidence) == 'verified'
            assert prior.old.privacy.original._dual.lifecycle_replay(evidence['slot'], evidence) == 'verified'
            dual += 2
    assert dual == 12
    mutations = []
    for name in ('free-factory', 'invented-waste', 'cleared-failure-debt', 'repaid-bootstrap'):
        changed = deepcopy(witness)
        if name == 'free-factory': changed['output'][1]['rows'][0]['debit'] = []
        elif name == 'invented-waste': changed['output'][1]['rows'][0]['credit'][1][2] = '2'
        elif name == 'cleared-failure-debt': changed['output'][0]['nativeNext']['outstanding'] = '0'
        else: changed['output'][1]['rows'] = changed['output'][0]['rows'][4:5] + changed['output'][1]['rows']
        changed['public'] = [{k: v for k, v in result.items() if k not in ('nativeBefore', 'nativeNext')}
                             for result in changed['output']]
        try: verify(changed, request['commands'], parent)
        except (AssertionError, KeyError): mutations.append(name)
        else: raise AssertionError('MUTATION_ACCEPTED:' + name)
    receipt = dict(status='PASS', source_events=53, appended_live_events=0, commands=9, parse_errors=3,
                   counts=counts, feed_left=6, life_produced=9, supplier_labor=32,
                   native_slots=15, outstanding=0, new_windows=1, deliveries=1, dual_checks=dual,
                   mutations_rejected=mutations,
                   input_sha256=hashlib.sha256((home/'input.json').read_bytes()).hexdigest(),
                   output_sha256=hashlib.sha256((home/'output.json').read_bytes()).hexdigest())
    (home/'independent.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('INDEPENDENT PRODUCTIVE REPLAY PASS ' + json.dumps(receipt, sort_keys=True))


if __name__ == '__main__': main()
