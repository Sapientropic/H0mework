"""Consume four actual native votes and the original owner's donor permission."""
import argparse
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
from cryptography.exceptions import InvalidSignature

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'Verification/public-audit/network'))
import donor_arrival_admission as auth
from crypto import digest, verify
from recovery_loop import save


def load(path):
    return json.loads(Path(path).read_text())


def reject(name, action):
    try:
        action()
    except (ValueError, InvalidSignature):
        return name
    raise ValueError('NEGATIVE_ACCEPTED:'+name)


def local_journal(point, member, signed, rows):
    auth.require(isinstance(signed, list) and len(signed) == len(rows) and
        all(isinstance(r, list) and len(r) == 5 for r in signed), 'DONOR_COMPLETE_LOCAL_JOURNAL')
    auth.require([r[:4] for r in signed] == rows, 'DONOR_COMMON_LEDGER')
    for seq, previous, head, raw, receipt in signed:
        auth.anchor.verify_commit(point['members']['members'][member], json.loads(receipt),
            source=point['source'], stream=point['stream'], seq=seq, previous=previous,
            head=head, message=json.loads(raw), cluster=point['cluster'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('work', type=Path)
    parser.add_argument('--box', type=Path, default=ROOT/'.agents/tmp/public-recovery-20261103/live')
    parser.add_argument('--collect', action='store_true')
    args = parser.parse_args()
    work, box = args.work.resolve(), args.box.resolve()
    config = load(box/'local-anchor/config.json')
    _, signed, prefix = auth.source_readiness.snapshot(config)
    rows = [list(r[:4]) for r in signed]
    program = auth.programs(ROOT, config)
    point, request, old = auth.context(config, rows, program)
    votes, permit = load(work/'votes.json'), load(work/'owner-permit.json')
    auth.require(load(work/'point.json') == point and load(work/'program.json') == program and
                 load(work/'request.json') == request and load(work/'old.json') == old, 'DONOR_CHECK_ORIGIN')
    auth.permission(config, rows, program, votes, permit)
    deploy = manifest = None
    if args.collect:
        spec = importlib.util.spec_from_file_location('donor_check_transport', Path(__file__).with_name('public-arrival-deploy.py'))
        deploy = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(deploy)
        manifest = load(box/'ha/deployment.json')
    reports = {}
    for member in 'abcd':
        path = work/('evidence-'+member+'.json')
        if args.collect and not path.exists():
            record = load(work/('node-'+member+'.json'))
            home = record['home']
            code = str(ROOT/'Verification/public-audit/network') if member == 'a' else manifest['nodes'][member]['code']
            cfgpath = str(box/'local-anchor/config.json') if member == 'a' else manifest['nodes'][member]['home']+'/config.json'
            script = f'''import hashlib,json,sys
from pathlib import Path
sys.path.insert(0,{code!r})
import source_readiness
p=Path({home!r});c=json.loads(Path({cfgpath!r}).read_text())
member,signed,prefix=source_readiness.snapshot(c)
names=['settings','input','output','facts','native','rows','vote']
result={{n:json.loads((p/(n+'.json')).read_text()) for n in names}}
result['current']=prefix;result['member']=member
result['objects']={{n:hashlib.sha256((p/'lib'/n).read_bytes()).hexdigest() for n in result['native']['objects']}}
print(json.dumps(result))
'''
            save(path, json.loads(deploy.execute(member, script, manifest, 120)))
        item = load(path)
        local_journal(point, member, item['rows'], rows)
        body = verify(auth.anchor.public_key(point['members']['members'][member]), auth.READY, votes[member])
        auth.require(item['member'] == member and item['current'] == prefix and
            item['settings']['point'] == point and item['settings']['program'] == program and
            item['input'] == request and item['vote'] == votes[member] and
            [r[:4] for r in item['rows']] == rows and
            body['output'] == digest(item['output']) == item['native']['output'] and
            item['native']['input'] == digest(request) and
            item['native']['program'] == program and item['native']['compiler'] == program['compiler'] and
            item['native']['exit'] == 0 and item['native']['original_database_writes'] == 0 and
            item['objects'] == item['native']['objects'] == body['objects'], 'DONOR_CHECK_LOCAL_EXECUTION')
        strict = item['native']['strict']
        auth.require(strict[1:] == ['--trust=0','-j1','-M8000','-DElab.async=false','-DwarningAsError=true'],
                     'DONOR_STRICT_COMMAND')
        reports[member] = auth.inspect_trace(ROOT, item['output'], request, old)
        auth.require(reports[member] == item['facts'], 'DONOR_INDEPENDENT_SOURCE_ACCOUNT')
    failures = []
    missing = deepcopy(votes); missing.pop('d')
    failures.append(reject('missing-fourth-native', lambda: auth.consume(config, rows, program, missing)))
    forged = deepcopy(votes); forged['a']['body']['output'] = '0'*64
    failures.append(reject('forged-native-receipt', lambda: auth.consume(config, rows, program, forged)))
    wrong = deepcopy(votes); wrong['a'] = votes['b']
    failures.append(reject('wrong-native-signer', lambda: auth.consume(config, rows, program, wrong)))
    shifted = deepcopy(rows); shifted[-1][2] = '0'*64
    failures.append(reject('stale-parent-permit', lambda: auth.permission(config, shifted, program, votes, permit)))
    changed = deepcopy(program); changed['sources'][auth.MODULES[0]] = '0'*64
    failures.append(reject('different-program-permit', lambda: auth.permission(config, rows, changed, votes, permit)))
    badpermit = deepcopy(permit); badpermit['body']['disposition'] = 'decided'
    failures.append(reject('forged-permit-disposition', lambda: auth.permission(config, rows, program, votes, badpermit)))
    failures.append(reject('readiness-as-owner-permit', lambda: auth.permission(config, rows, program, votes, votes['c'])))
    old_permit = load(work/'old68-owner-packet.json')['permission']
    failures.append(reject('old68-isolation-permit', lambda: auth.permission(config, rows, program, votes, old_permit)))
    missing_receipt = deepcopy(load(work/'evidence-a.json')['rows']); missing_receipt[-1].pop()
    failures.append(reject('deleted-local-commit-receipt', lambda: local_journal(point, 'a', missing_receipt, rows)))
    wrong_receipt = deepcopy(load(work/'evidence-a.json')['rows'])
    wrong_receipt[-1][4] = load(work/'evidence-b.json')['rows'][-1][4]
    failures.append(reject('other-anchor-commit-receipt', lambda: local_journal(point, 'a', wrong_receipt, rows)))
    auth.require(auth.source_readiness.snapshot(config)[2] == prefix, 'DONOR_CHECK_PREFIX_MOVED')
    result = dict(verdict='accepted', point=digest(point), prefix=prefix, native_members=list(reports),
        permission=digest(permit), negative_controls=failures, source_facts=reports['a'],
        native_computations=0, original_database_writes=0,
        timing_scope='offline-preflight-only', combined_timing_acceptance=False,
        disposition='prepared-for-original77-control-admission')
    save(work/'independent.json', result)
    print(json.dumps(result))


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    main()
