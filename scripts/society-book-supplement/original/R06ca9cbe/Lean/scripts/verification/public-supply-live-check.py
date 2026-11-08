"""Consume the actual four journals, native comparisons and retained disposition."""
import argparse
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'Verification/public-audit/network'))
import anchor
from crypto import canonical, digest, verify
from ha_anchor import verify_quorum
import supply_disposition as supply
from recovery_loop import save


def module(name, file):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(file))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value)
    return value


deploy = module('supply_live_deploy', 'public-donor-live-deploy.py')
client = module('supply_live_client', 'public-supply-live-request.py')
load = deploy.load


def run(box, work, revision, collect):
    directory = work/'actual'; manifest = load(box/'ha/deployment.json')
    prepared = load(work/'source-view'/revision/'prepared.json'); profile = load(work/'source-view'/revision/'profile.json')
    if manifest['release'] != revision or digest(profile['files']) != revision:
        raise ValueError('SUPPLY_LIVE_PROFILE')
    request = load(directory/'original-request.json'); parent = load(directory/'parent.json')
    result = load(directory/'result.json'); summary = client.checked(manifest['mac']['service'], parent, request, result)
    accepted = {}
    for member in 'abcd':
        saved = directory/('independent-'+member+'.json')
        if collect and not saved.exists():
            entry = prepared['nodes'][member]
            cfgpath = entry['original_config']
            script = f'''import hashlib,json,sqlite3,sys
from pathlib import Path
sys.path.insert(0,{entry['code']!r})
import source_readiness
cfg=json.loads(Path({cfgpath!r}).read_text());member,rows,prefix=source_readiness.snapshot(cfg)
assert member=={member!r}
with sqlite3.connect(Path(cfg['database']).resolve().as_uri()+'?mode=ro',uri=True) as db:
 bad=db.execute('SELECT message,proof FROM ha_rejected_intents WHERE stream=? AND seq=?',('recovery',{len(parent)+1})).fetchall()
 decisions=db.execute('SELECT payload FROM semantic_decisions ORDER BY rowid').fetchall()
 proof=db.execute('SELECT payload FROM ha_events JOIN ha_proofs ON ha_events.id=ha_proofs.event WHERE ha_proofs.stream=? AND ha_proofs.seq=?',('recovery',{len(parent)+1})).fetchone()
entry=next(row for row in rows if row[0]=={len(parent)+1})
messages={{json.loads(raw)['body']['message'] for _,raw in bad}}
target=json.loads(entry[3]);events={{__import__('crypto').digest(target)}}|messages
selected=[json.loads(raw) for raw, in decisions if json.loads(raw)['body'].get('event') in events]
print(json.dumps(dict(member=member,prefix=prefix,config_digest=__import__('crypto').digest(cfg),
 protocol={{name:source_readiness.sha(Path({entry['code']!r})/name) for name in {list(profile['files'])!r}}},
 entry=entry,bad=[dict(message=json.loads(raw),receipt=json.loads(receipt)) for raw,receipt in bad],decisions=selected,
 proof=json.loads(proof[0]) if proof else None)))
'''
            save(saved, json.loads(deploy.execute(member, script, manifest, 90)))
        evidence = load(saved); node = prepared['nodes'][member]['vote']['body']['point']
        if (evidence['member'] != member or evidence['protocol'] != profile['files'] or
                evidence['config_digest'] != node['candidate_configuration'] or evidence['entry'][:4] !=
                [len(parent)+1, parent[-1][2], result['head'], canonical(result['ledger']).decode()]):
            raise ValueError('SUPPLY_LIVE_LITERAL_ENTRY')
        if len(evidence['bad']) != 1: raise ValueError('SUPPLY_LIVE_DEVIATION_COUNT')
        bad = evidence['bad'][0]; rejected = verify(anchor.public_key(manifest['trust']['members'][member]), 'ha-intent-rejection', bad['receipt'])
        if (rejected['disposition'] != 'source-invalid' or rejected['message'] != digest(bad['message']) or
                bad['message']['body']['request'] != request or rejected['seq'] != len(parent)+1 or
                rejected['previous'] != parent[-1][2]):
            raise ValueError('SUPPLY_LIVE_ORIGINAL_REQUEST')
        supply.consume(manifest['mac']['service'], parent, bad['message'], rejected['comparison'])
        wanted = supply.binding(supply.context_at(manifest['mac']['service']), manifest['mac']['service']['semantic_policy'],
                                parent, result['ledger'], load(work/'authorized-source-input.json'),
                                supply.program(manifest['mac']['service']['donor']))
        wanted.update(classification='verified', expected=wanted['actual'])
        checked = [verify(anchor.public_key(manifest['trust']['members'][member]), 'source-semantic-decision', value)
                   for value in evidence['decisions']]
        if wanted not in checked: raise ValueError('SUPPLY_LIVE_ACTUAL_NATIVE_COMPARISON')
        proof = verify(anchor.public_key(manifest['trust']['members'][member]), 'ha-event', evidence['proof'])
        token = proof['grant']['point']
        if (proof['source'] != token['source'] or token['source'] != request['body']['source'] or
                proof['stream'] != token['stream'] or token['stream'] != 'recovery' or
                proof['cluster'] != token['cluster'] or token['cluster'] != manifest['mac']['service']['cluster'] or
                token['owner'] not in manifest['owners']):
            raise ValueError('SUPPLY_LIVE_FENCED_SOURCE')
        point = dict(token=proof['grant']['point'], seq=len(parent)+1, previous=parent[-1][2], head=result['head'],
                     message=digest(result['ledger']), operation_id=request['body']['request_id'])
        if proof['operation'] != 'append' or proof['point'] != point: raise ValueError('SUPPLY_LIVE_FENCED_COMMIT')
        verify_quorum({'ha':{'trust':manifest['trust']}}, proof['grant'], 'ha-grant', point['token'])
        verify_quorum({'ha':{'trust':manifest['trust']}}, proof['intent'], 'ha-intent', point)
        anchor.verify_commit(manifest['trust']['members'][member], proof['receipt'], source=request['body']['source'],
            stream='recovery', seq=len(parent)+1, previous=parent[-1][2], head=result['head'],
            message=result['ledger'], cluster=token['cluster'])
        accepted[member] = dict(expected=wanted['expected'], rejected=digest(bad['receipt']), proof=digest(evidence['proof']))
    comparison = load(directory/'independent-a.json')['bad'][0]['receipt']['body']['comparison']
    actual_bad = load(directory/'independent-a.json')['bad'][0]['message']
    controls = []
    for name, change in {
        'missing-comparison': lambda value: value['votes'].pop(),
        'duplicate-receipt': lambda value: value['votes'].__setitem__(1, value['votes'][0]),
        'wrong-signer': lambda value: value['votes'][0].__setitem__('receipt', value['votes'][1]['receipt']),
        'forged-native-result': lambda value: value['votes'][0]['receipt']['body'].__setitem__('expected', '0'*64),
    }.items():
        value = deepcopy(comparison); change(value)
        try:supply.consume(manifest['mac']['service'], parent, actual_bad, value)
        except (ValueError, KeyError):controls.append(name)
        else:raise ValueError('SUPPLY_LIVE_NEGATIVE_ACCEPTED:'+name)
    report = dict(exit=0, schema='actual-source-supply-disposition/v1', protocol=revision, **summary,
        original_members=sorted(accepted), source_comparisons=4, retained_dispositions=4,
        actual=dict(accepted), source_input=digest(load(work/'authorized-source-input.json')),
        original_owner_permission=digest(load(work/'owner-packet.json')['permission']),
        actual_negative_controls=controls,
        native_preparations=0, checker_native_computations=0, checker_economic_requests=0,
        original_economic_requests=1, original_90_replayed=0)
    save(directory/'independent.json', report)
    print(json.dumps(report))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--box', type=Path, default=ROOT/'.agents/tmp/public-recovery-20261103/live')
    parser.add_argument('--work', type=Path, required=True); parser.add_argument('--revision', required=True)
    parser.add_argument('--collect', action='store_true')
    args = parser.parse_args(); run(args.box.resolve(), args.work.resolve(), args.revision, args.collect)


if __name__ == '__main__':
    main()
