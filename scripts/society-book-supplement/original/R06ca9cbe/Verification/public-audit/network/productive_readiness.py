"""Each original node replays its own journal before signing the material successor."""
import argparse
import copy
import json
from pathlib import Path
import time

from anchor import public_key
from crypto import app_private, digest, sign, verify
from source_semantics import Engine
import productive_extension
import material_regeneration
import material_extension
import source_readiness as original


def commands():
    return ([dict(kind='cycle',mode=mode) for mode in ['deny-factory','normal','normal','normal']]
        + [dict(kind='service',query=dict(slots=63,fields=3)) for _ in range(2)]
        + [dict(kind='cycle',mode='unregistered',metadata=dict(probe='invalid-mode')),
           dict(kind='unregistered',actor='private-frame-test',fee='uncharged'),
           dict(kind='service',query=dict(slots='bad',fields=3),metadata=['invalid-query',7])])


def probe(config, rows):
    parent, _, _ = material_regeneration.context(config, rows)
    return dict(mode='productive',parent=parent,commands=commands())


def evaluate(config, rows, argument, seconds=300):
    if argument != probe(config, rows): raise ValueError('PRODUCTIVE_PROBE_ORIGIN')
    legacy = original.LocalEngine(config['semantic']); new = original.LocalEngine(config['productive'])
    results = []
    try:
        legacy.sync(rows,deadline=time.monotonic()+seconds)
        legacy_status=legacy.status();new.start()
        parent={**argument['parent'],'mode':'regeneration'}
        if new.call(parent,time.monotonic()+seconds)!=json.loads(rows[-1][3])['body']['native']:
            raise ValueError('PRODUCTIVE_OLD_LITERAL_CHANGED')
        for count in range(1,len(argument['commands'])+1):
            value={**argument,'commands':argument['commands'][:count]}
            results.append(new.call(value,time.monotonic()+seconds))
        new_status=new.status()
    finally: original.close_all(legacy,new)
    if ([r['status'] for r in results] != ['BLOCKED','PRODUCED','PRODUCED','PRODUCED','OPENED','DELIVERED','ERROR','ERROR','ERROR']
            or sum(item['accepted'] and item['request']['operation']==dict(kind='produce',actor='provider:1')
                   for r in results for item in r.get('rows',[]))!=3):
        raise ValueError('PRODUCTIVE_PROBE_DID_NOT_RECOVER_AND_DELIVER')
    return results,legacy_status,new_status


def issue(config, directory):
    directory = Path(directory); directory.mkdir(parents=True, exist_ok=False)
    config = original.isolated(config, directory)
    member, signed, prefix = original.snapshot(config); rows = [r[:4] for r in signed]
    point = productive_extension.point(config, prefix)
    if point['parent'] != digest(material_extension.require(config, rows)[1]):
        raise ValueError('PRODUCTIVE_ACTUAL_PARENT_CERTIFICATE')
    argument = probe(config, rows); result, old, new = evaluate(config, rows, argument)
    if original.snapshot(config) != (member, signed, prefix): raise ValueError('PRODUCTIVE_PREFIX_MOVED')
    key = app_private(Path(config['pki'])/'anchor')
    if key.public_key().public_bytes_raw().hex() != config['registry']['anchor']['app']:
        raise ValueError('PRODUCTIVE_SIGNER')
    body = dict(point=point, member=member, compiler=point['descriptor']['compiler'], legacy_prefix=prefix,
                probe=dict(input=digest(argument), output=digest(result)), legacy_backend=old['backend'],
                source_backend=new['backend'], journal=digest(signed), at=time.time())
    vote = dict(member=member, receipt=sign(key, productive_extension.READY, body))
    for name, value in [('rows', signed), ('input', argument), ('output', result), ('vote', vote)]:
        original.save(directory/(name+'.json'), value)
    return vote


def check(config, directory, output):
    directory = Path(directory); output = Path(output); output.mkdir(parents=True, exist_ok=False)
    config = original.isolated(config, output)
    member, signed, prefix = original.snapshot(config)
    rows = [r[:4] for r in signed]
    recorded = json.loads((directory/'rows.json').read_text())
    if recorded != [list(r) for r in signed]: raise ValueError('PRODUCTIVE_INDEPENDENT_JOURNAL')
    vote = json.loads((directory/'vote.json').read_text())
    body = verify(public_key(config['registry']['anchor']), productive_extension.READY, vote['receipt'])
    argument = json.loads((directory/'input.json').read_text())
    expected = json.loads((directory/'output.json').read_text())
    if (vote['member'] != member or body['member'] != member or body['point'] != productive_extension.point(config, prefix)
            or body['journal'] != digest(signed) or body['legacy_prefix'] != prefix
            or body['probe'] != dict(input=digest(argument), output=digest(expected))):
        raise ValueError('PRODUCTIVE_INDEPENDENT_BINDING')
    actual, old, new = evaluate(config, rows, argument)
    if actual != expected or not old['backend'] or not new['backend']:
        raise ValueError('PRODUCTIVE_INDEPENDENT_REPLAY')
    report = dict(exit=0, member=member, prefix=prefix, literal_outputs=len(actual),
                  parent=digest(material_extension.require(config, rows)[1]), probe=body['probe'])
    original.save(output/'acceptance.json', report)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['issue', 'check']); parser.add_argument('config', type=Path)
    parser.add_argument('directory', type=Path); parser.add_argument('--output', type=Path)
    args = parser.parse_args(); config = json.loads(args.config.read_text())
    result = issue(config, args.directory) if args.operation == 'issue' else check(config, args.directory, args.output)
    print(json.dumps(result))
