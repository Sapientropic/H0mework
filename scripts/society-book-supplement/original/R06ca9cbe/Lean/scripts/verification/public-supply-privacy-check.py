"""Independently consume complete supply replies and original material evidence."""
from __future__ import annotations

from copy import deepcopy
from fractions import Fraction as Q
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('original_supply_consumer', HERE/'public-regeneration-check.py')
original = importlib.util.module_from_spec(spec)
spec.loader.exec_module(original)
CASES = ('normal', 'withhold-fuel', 'deny-production', 'wrong-supplier', 'narrow-default')


def public_state(value):
    audit = value['technology']['audit']
    assert len(value['stock']) == 48 and len(value['claims']) == 147
    assert len({tuple(row[:2]) for row in value['stock']}) == 48
    assert len({tuple(row[:3]) for row in value['claims']}) == 147
    assert ['audit:3', 'feed'] not in [row[:2] for row in value['stock']], 'PRIVATE_COORDINATE'
    return original.state(dict(clock=value['clock'], round=value['round'],
        holder=audit['holder'], offered=audit['offered'], version=audit['version'],
        stock=[dict(actor=p, good=g, quantity=q) for p, g, q in value['stock']],
        claims=[dict(instrument=i, debtor=p, creditor=h, quantity=q) for i, p, h, q in value['claims']]))


def reference_groups(path):
    groups = {}; current = None
    for row in map(json.loads, Path(path).read_text().splitlines()):
        if 'mode' in row:
            current = row['mode']; groups[current] = []
        else:
            groups[current].append(row['transition'])
    assert set(groups) == set(CASES[:-1])
    assert all(len(rows) == 13 for rows in groups.values())
    return groups


def check(records, reference):
    groups = {}
    for row in records:
        assert set(row) == {'world', 'case', 'index', 'reply'}
        assert type(row['world']) is bool and row['case'] in CASES
        key = (row['world'], row['case'])
        groups.setdefault(key, []).append(row)
    assert len(groups) == 10 and len(records) == 140
    dual_checks = insufficient = parsed_errors = 0
    largest = 0
    for case in CASES:
        left, right = groups[False, case], groups[True, case]
        assert [r['index'] for r in left] == list(range(14))
        assert [r['index'] for r in right] == list(range(14))
        assert [r['reply'] for r in left] == [r['reply'] for r in right], 'COMPLETE_OUTPUT_OR_METADATA'
        old = reference['normal' if case == 'narrow-default' else case]
        for index, record in enumerate(left):
            value = record['reply']; meta = value['metadata']
            largest = max(largest, len(json.dumps(value, separators=(',', ':')).encode()))
            assert largest < 65536, 'SOURCE_FRAME_LIMIT'
            assert meta['metadata'] == dict(actor=f'caller-{index}', feeUnit='energy',
                nonce=f'nonce-{index}', timestampNs=str(100000+index)), 'METADATA_NOT_EXACT'
            if index == 5:
                assert set(value) == {'metadata', 'status', 'message'}
                assert value['status'] == 'ERROR' and value['message'] == 'SUPPLY_MODE'
                parsed_errors += 1
                continue
            ordinal = index if index < 5 else index-1
            expected = old[ordinal]
            assert value['history'] == ordinal+1, 'PARSE_ERROR_ADVANCED_SOURCE'
            assert value['actor'] == expected['before']['holder'] or (
                expected['before']['holder'] is None and value['actor'] == expected['target'])
            assert value['target'] == expected['target']
            assert value['opening'] == expected['opening']
            assert public_state(value['next']) == original.state(expected['next']), 'OWN_NEXT_OR_NATIVE_CLAIMS'
            assert value['scope']['unit'] == value['nextScope']['unit'] == 'energy'
            assert Q(value['scope']['earliest']) == Q(expected['task']['earliest'])
            assert Q(value['scope']['deadline']) == Q(expected['task']['deadline'])
            assert value['scope']['revisionCost'] == [['energy', '1']]
            if value['opening']:
                assert Q(value['nextScope']['earliest']) == Q(value['next']['clock'])+1
                assert Q(value['nextScope']['deadline']) == Q(value['next']['clock'])+7
            else:
                assert value['nextScope'] == value['scope']
            assert len(value['rows']) == len(expected['rows'])
            for row, old_row in zip(value['rows'], expected['rows'], strict=True):
                assert set(row) == {'index', 'request', 'accepted', 'debit', 'credit'}
                request = row['request']; before = original.state(old_row['before'])
                assert set(request) == {'signer', 'consents', 'purpose', 'gates', 'operation'}
                assert row['index'] == old_row['index'] and row['accepted'] == old_row['accepted']
                assert request['signer'] == old_row['action']['signer']
                assert request['operation']['kind'] == old_row['action']['op']['kind']
                if not row['accepted']:
                    assert row['debit'] == row['credit'] == [], 'REJECTED_REQUEST_WAS_PAID'
                actual_stock = dict(before['stock'])
                for sign, flow in ((-1, row['debit']), (1, row['credit'])):
                    for party, good, quantity in flow:
                        assert Q(quantity) >= 0
                        assert (party, good) in actual_stock
                        actual_stock[party, good] += sign*Q(quantity)
                assert actual_stock == original.state(old_row['after'])['stock'], 'ACTUAL_FEE_OR_MATERIAL_FLOW'
            assert [r['index'] for r in value['refusals']] == [r['index'] for r in value['rows'] if not r['accepted']]
            assert all(r['kind'] in ('fuel-absent', 'labor-absent', 'source-rejected') for r in value['refusals'])
            assert len(value['packets']) == expected['packets']
            if case != 'narrow-default':
                assert value['packets'] == expected['evidence'], 'ORIGINAL_PACKET_CHANGED'
            for packet in value['packets']:
                for evidence in packet:
                    outcomes = [original._dual.payment_scan(evidence['slot'], evidence),
                                original._dual.lifecycle_replay(evidence['slot'], evidence)]
                    assert all(outcome in ('verified', 'insufficient') for outcome in outcomes), 'INSUFFICIENT_IS_NOT_VIOLATION'
                    dual_checks += 2
                    insufficient += 'insufficient' in outcomes
    return dict(responses=140, actual_rounds=130, source_parse_errors=parsed_errors*2,
                dual_checks=dual_checks*2, insufficient_slices=insufficient*2, max_reply_bytes=largest)


def main():
    path, reference = map(Path, sys.argv[1:3])
    records = list(map(json.loads, path.read_text().splitlines()))
    groups = reference_groups(reference)
    result = check(records, groups)
    negatives = []
    for name in ('metadata', 'fee', 'parse-advance', 'private-disclosure', 'packet'):
        changed = deepcopy(records)
        index = 6 if name == 'parse-advance' else 1 if name == 'packet' else 0
        # Alter both worlds identically, so equality alone cannot reject a forgery.
        for record in changed:
            if record['case'] != 'normal' or record['index'] != index:
                continue
            value = record['reply']
            if name == 'metadata':
                value['metadata']['metadata']['actor'] = 'seat-for-life'
            elif name == 'fee':
                fee = next(row for row in value['rows'] if row['request']['operation']['kind'] == 'use')
                fee['debit'][0][2] = str(Q(fee['debit'][0][2])+1)
            elif name == 'parse-advance':
                value['history'] += 1
            elif name == 'private-disclosure':
                value['next']['stock'].append(['audit:3', 'feed', '39'])
            else:
                value['packets'][0][0]['payment'] = None
        try:
            check(changed, groups)
        except AssertionError:
            negatives.append(name)
        else:
            raise AssertionError(('NEGATIVE_WAS_ACCEPTED', name))
    result['negative_controls'] = negatives
    print('INDEPENDENT DEFAULT SUPPLY PRIVACY PASS '+json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
