"""Each original node replays its own journal before signing the material successor."""
import argparse
import copy
import json
from pathlib import Path
import time

from anchor import public_key
from crypto import app_private, digest, sign, verify
from source_semantics import Engine
import material_extension
import regeneration
import source_extension
import source_readiness as original


def probe(config, rows):
    value, _, _ = regeneration.context(config, rows)
    commands = ['deny-recycling']*4+['refeed', 'normal', 'normal']
    value = copy.deepcopy(value)
    for index, mode in enumerate(commands):
        value['requests'].append(dict(query=dict(slots=63, fields=3), mode=mode,
                                     metadata=dict(stage='material-readiness', index=index)))
    return value


def evaluate(config, rows, argument, seconds=300):
    old, _, _ = regeneration.context(config, rows)
    if argument != probe(config, rows): raise ValueError('MATERIAL_PROBE_ORIGIN')
    legacy = original.LocalEngine(config['semantic']); new = original.LocalEngine(config['refeed'])
    results = []
    try:
        legacy.sync(rows, deadline=time.monotonic()+seconds)
        legacy_status = legacy.status(); new.start()
        for count in range(1, len(argument['requests'])+1):
            value = {**argument, 'requests': argument['requests'][:count]}
            results.append(new.call(value, time.monotonic()+seconds))
        new_status = new.status()
    finally:
        original.close_all(legacy, new)
    expected = [json.loads(r[3])['body']['native'] for r in rows
                if json.loads(r[3])['body']['type'] == regeneration.KIND]
    if results[:len(old['requests'])] != expected: raise ValueError('MATERIAL_OLD_LITERAL_CHANGED')
    tail = results[len(expected):]
    recycled = [item for result in tail for item in result['rows']
                if item['accepted'] and item['request']['operation'] == dict(kind='produce', actor='provider:2')]
    refused = [item for result in tail for item in result['rows']
               if not item['accepted'] and item['request']['operation'] == dict(kind='produce', actor='provider:2')]
    if (len(recycled) != 1 or len(refused) != 1 or not any(r['opening'] for r in tail)
            or not any(r['packets'] for r in tail)):
        raise ValueError('MATERIAL_PROBE_DID_NOT_RECOVER_AND_DELIVER')
    return results, legacy_status, new_status


def issue(config, directory):
    directory = Path(directory); directory.mkdir(parents=True, exist_ok=False)
    config = original.isolated(config, directory)
    member, signed, prefix = original.snapshot(config); rows = [r[:4] for r in signed]
    point = material_extension.point(config, prefix)
    if point['parent'] != digest(source_extension.require(config, rows)[1]):
        raise ValueError('MATERIAL_ACTUAL_PARENT_CERTIFICATE')
    argument = probe(config, rows); result, old, new = evaluate(config, rows, argument)
    if original.snapshot(config) != (member, signed, prefix): raise ValueError('MATERIAL_PREFIX_MOVED')
    key = app_private(Path(config['pki'])/'anchor')
    if key.public_key().public_bytes_raw().hex() != config['registry']['anchor']['app']:
        raise ValueError('MATERIAL_SIGNER')
    body = dict(point=point, member=member, compiler=point['descriptor']['compiler'], legacy_prefix=prefix,
                probe=dict(input=digest(argument), output=digest(result)), legacy_backend=old['backend'],
                source_backend=new['backend'], journal=digest(signed), at=time.time())
    vote = dict(member=member, receipt=sign(key, material_extension.READY, body))
    for name, value in [('rows', signed), ('input', argument), ('output', result), ('vote', vote)]:
        original.save(directory/(name+'.json'), value)
    return vote


def check(config, directory, output):
    directory = Path(directory); output = Path(output); output.mkdir(parents=True, exist_ok=False)
    config = original.isolated(config, output)
    member, signed, prefix = original.snapshot(config)
    rows = [r[:4] for r in signed]
    recorded = json.loads((directory/'rows.json').read_text())
    if recorded != [list(r) for r in signed]: raise ValueError('MATERIAL_INDEPENDENT_JOURNAL')
    vote = json.loads((directory/'vote.json').read_text())
    body = verify(public_key(config['registry']['anchor']), material_extension.READY, vote['receipt'])
    argument = json.loads((directory/'input.json').read_text())
    expected = json.loads((directory/'output.json').read_text())
    if (vote['member'] != member or body['member'] != member or body['point'] != material_extension.point(config, prefix)
            or body['journal'] != digest(signed) or body['legacy_prefix'] != prefix
            or body['probe'] != dict(input=digest(argument), output=digest(expected))):
        raise ValueError('MATERIAL_INDEPENDENT_BINDING')
    actual, old, new = evaluate(config, rows, argument)
    if actual != expected or not old['backend'] or not new['backend']:
        raise ValueError('MATERIAL_INDEPENDENT_REPLAY')
    report = dict(exit=0, member=member, prefix=prefix, literal_outputs=len(actual),
                  parent=digest(source_extension.require(config, rows)[1]), probe=body['probe'])
    original.save(output/'acceptance.json', report)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['issue', 'check']); parser.add_argument('config', type=Path)
    parser.add_argument('directory', type=Path); parser.add_argument('--output', type=Path)
    args = parser.parse_args(); config = json.loads(args.config.read_text())
    result = issue(config, args.directory) if args.operation == 'issue' else check(config, args.directory, args.output)
    print(json.dumps(result))
