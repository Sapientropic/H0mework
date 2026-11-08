"""Consume original source receipts and four physical-node journals independently."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
from itertools import combinations
import json
from pathlib import Path
import shutil
import sqlite3
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[3]
BOX=ROOT/'.agents/tmp/public-distributed-audit-20261102'
NETWORK=ROOT/'Verification/public-audit/network'
OLD=ROOT/'.agents/tmp/public-quorum-audit-20261102'
sys.path.insert(0,str(NETWORK))
from anchor import ledger_hash,public_key
from crypto import digest,verify


def require(condition,message):
    if not condition:raise RuntimeError(message)


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path,sql,args=()):
    connection=sqlite3.connect(path.resolve().as_uri()+'?mode=ro&immutable=1',uri=True)
    try:return connection.execute(sql,args).fetchall()
    finally:connection.close()


def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


base=load_module('paid_four_anchor',ROOT/'Lean/scripts/verification/public-quorum-audit.py')
challenge=load_module('causal_rpc_contract',ROOT/'Lean/scripts/verification/public-anchor-challenge.py')


def inputs():
    extra=['Verification/public-audit/network/'+name for name in ('challenge_anchor.py','remote_anchor.py','distributed_exercise.py')]
    extra+=['Verification/public-audit/runtime/'+name for name in ('pyproject.toml','uv.lock','.python-version')]
    extra+=['Lean/scripts/verification/'+name for name in ('public-distributed-audit.py','public-anchor-challenge.py','public-scoped-audit.py')]
    return {**base.producer_inputs(),**{path:sha(ROOT/path) for path in extra}}


def original_chain():
    accepted=json.loads((OLD/'acceptance.json').read_text());final=json.loads((OLD/'final-check.json').read_text())
    integration=json.loads((OLD/'integration.json').read_text())
    frozen=integration.get('implementation_commit',integration['commit'])
    for path,wanted in accepted['producer'].items():require(sha(ROOT/path)==wanted,'original source changed: '+path)
    for path,wanted in accepted['checker'].items():
        historical=subprocess.check_output(['git','show',frozen+':'+path],cwd=ROOT)
        require(hashlib.sha256(historical).hexdigest()==wanted,'historical checker differs: '+path)
        if not path.endswith('/public-scoped-audit.py'):require(sha(ROOT/path)==wanted,'original independent checker changed')
    require(final['exit']==0 and sha(OLD/'acceptance.json')==final['acceptance_sha256']
            and sha(OLD/'final-audit-02.log')==final['independent_full_audit_log_sha256'],'original audit provenance')
    actual=Path(accepted['actual'])
    for path,wanted in final['data'].items():require(sha(actual/path)==wanted,'paid original witness changed: '+path)
    base.single.paid_proofs()
    result=subprocess.run([sys.executable,str(ROOT/'Lean/scripts/verification/public-source-final-audit.py'),'--check-main'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (BOX/'original-six.log').write_text(result.stdout)
    require(result.returncode==0,'original six / full cost audit failed')
    print('ORIGINAL SOURCE CHAIN PASS: 7 original literal routes; full costs; 512 paid requests and exact prior source replay preserved',flush=True)
    return actual


def collect(actual):
    evidence={}
    for tag,member in [('pc','b'),('spark','c'),('studio','d')]:
        state=ROOT/'ComputeNode/state'/('public-anchor-'+tag+'-20261102')
        spec=json.loads((state/'units.jsonl').read_text())
        receipts=[json.loads(line) for line in (state/'results/accepted.jsonl').read_text().splitlines() if line]
        found=[entry for entry in receipts if entry['id']==spec['id']]
        require(len(found)==1 and found[0]['exit']==0,'physical unit not accepted: '+tag)
        source=state/'results'/spec['id'];destination=actual/('node-'+member)
        destination.mkdir(exist_ok=True)
        for name,wanted in found[0]['files'].items():
            require('/' not in name and name in {'journal.sqlite','placement.json','management.jsonl','snapshots.tar.gz','anchor.log','final.json'},'unexpected node output')
            require(sha(source/name)==wanted,'node transfer hash differs')
            shutil.copyfile(source/name,destination/name)
        evidence[member]={'receipt':found[0],'unit':spec,'state':str(state)}
    (actual/'node-receipts.json').write_text(json.dumps(evidence,indent=2)+'\n')


def independent(actual,original):
    public=json.loads((actual/'public-keys.json').read_text())
    trust=public['trust'];cluster=digest(trust);registry=public['audit']
    source=json.loads((original/'receipt.json').read_text())['source']
    require(trust['version']==1 and trust['threshold']==3 and set(trust['members'])==set('abcd'),'four-member trust')
    require(len({entry['app'] for entry in trust['members'].values()})==4,'duplicate anchor key')
    placements=public['placement']
    protocol={name:sha(NETWORK/name) for name in ('anchor.py','crypto.py','quorum.py','challenge_anchor.py','remote_anchor.py')}
    expected={'b':('pc','Luciano-PC'),'c':('spark','robo-dog-fa3b'),'d':('studio','mac-studio')}
    machines=set()
    for member,statement in placements.items():
        point=verify(public_key(trust['members'][member]),'anchor-placement',statement)
        require(point['member']==member and point['identity']==trust['members'][member] and point['source']==source and point['protocol']==protocol,'physical/source placement')
        machines.add(point['machine'])
        if member in expected:require(point['host']==expected[member][1],'wrong physical host')
    require(len(machines)==4 and len(set(public['tls_roots'].values()))==4,'shared physical machine / TLS issuer')
    quorums=list(map(set,combinations('abcd',3)))
    require(all((a&b)-{fault} for a in quorums for b in quorums for fault in 'abcd'),'rollback intersection')
    receipts=json.loads((actual/'node-receipts.json').read_text())
    for member,item in receipts.items():
        require(item['receipt']['host']==placements[member]['body']['host'],'scheduler and journal disagree about host')
        directory=actual/('node-'+member)
        final=verify(public_key(trust['members'][member]),'anchor-final',json.loads((directory/'final.json').read_text()))
        require(final['member']==member and final['source']==source,'physical final identity')
        for name,wanted in final['files'].items():require(sha(directory/name)==wanted,'signed node final bytes')
        require(json.loads((directory/'placement.json').read_text())==placements[member],'returned placement changed')
        cases=[]
        for line in (directory/'management.jsonl').read_text().splitlines():
            event=json.loads(line);body=verify(public_key(trust['members'][member]),'anchor-management',event['response'])
            require(body['request']==digest(event['command']) and body['source']==source and body['member']==member and 'error' not in body['result'],'physical recovery operation failed')
            cases.append(event['command']['op'])
            if event['command']['op']=='lose-storage':require('ANCHOR_STORAGE_MISSING' in body['result']['rejection'],'missing node silently reinitialized')
        require(cases[-1]=='finish' and ('crash' in cases if member=='c' else 'lose-storage' in cases if member=='b' else 'restore' in cases),'physical fault was not exercised')
        require((cases.count('lose-storage')==4 if member=='b' else cases.count('crash')==2 if member=='c' else cases.count('restore')==6 and cases.count('snapshot')==2),'incomplete signed physical fault history')
    histories=[]
    for world in ('one','two'):
        literal=rows(original/(world+'-audit-domain/ledger.sqlite'),'SELECT id,previous,hash,message FROM events ORDER BY id')
        certificates=json.loads((actual/(world+'-certificates.json')).read_text())
        require(len(literal)==len(certificates)==257,'missing source events')
        prior='0'*64;remote_only=False
        for (seq,before,head,text),qc in zip(literal,certificates):
            message=json.loads(text);event=verify(public_key(registry['server']),'ledger',message)
            require(event['source']==source and event['stream']==world and before==prior and ledger_hash(before,message)==head,'original signed source chain')
            expected_point=dict(source=source,stream=world,seq=seq,head=head,previous=before,message=digest(message),cluster=cluster)
            require(qc['kind']=='anchor-quorum' and qc['cluster']==cluster and qc['body']==expected_point,'new physical QC point')
            names=[vote['member'] for vote in qc['votes']]
            require(names==sorted(set(names)) and 3<=len(names)<=4,'physical QC quorum')
            for vote in qc['votes']:require(verify(public_key(trust['members'][vote['member']]),'anchor-commit',vote['receipt'])==expected_point,'physical QC signature')
            remote_only|=names==['b','c','d'];prior=head
        require(remote_only,'no actual commit by the three remote machines alone')
        for position,names in [(i,['a','b','c']) for i in range(8,12)]+[(i,['a','b','d']) for i in (64,65)]+[(i,['b','c','d']) for i in (192,193)]:
            require([vote['member'] for vote in certificates[position]['votes']]==names,'partition/crash did not use the exact surviving machines')
        for member,identity in trust['members'].items():
            path=actual/'a-journal.sqlite' if member=='a' else actual/('node-'+member)/'journal.sqlite'
            binding=rows(path,'SELECT value FROM binding')
            expected_binding={'streams':{stream:{'source':source,'writer':registry['server']} for stream in ('one','two')},'identity':identity,'cluster':cluster,'transport_writer':public['transport'][member]}
            require(len(binding)==1 and json.loads(binding[0][0])==expected_binding,'physical journal owner/source/membership binding differs')
            external=rows(path,'SELECT seq,previous,hash,message,receipt FROM entries WHERE stream=? ORDER BY seq',(world,))
            require([entry[:4] for entry in external]==literal,'physical full database differs: '+member+'/'+world)
            for seq,before,head,text,signature in external:
                point=dict(source=source,stream=world,seq=seq,head=head,previous=before,message=digest(json.loads(text)),cluster=cluster)
                require(verify(public_key(identity),'anchor-commit',json.loads(signature))==point,'physical stored receipt differs')
        records=[json.loads(row[3])['body']['record'] for row in literal if json.loads(row[3])['body']['type']=='disclosure']
        require(records==json.loads((original/(world+'-observations.json')).read_text()) and sum(int(record['labor']) for record in records)==14,'original scope/payment changed in physical replication')
        histories.append(records)
        print('INDEPENDENT PHYSICAL '+world+' PASS: 257 original events; 4 machine databases; 3 remote signers commit without local anchor',flush=True)
    require(histories[0]==histories[1],'physical recovery changed cumulative disclosure')
    require(not (actual/'private-clients').exists(),'temporary client/local-anchor keys not released')
    summary=json.loads((actual/'receipt.json').read_text())
    suffixes=('single_partial_remote_copy_lost_original_intent_retained','two_two_partition_refused_three_one_continues',
              'reconnected_physical_node_caught_up_exactly',*(f'whole_remote_database_rollback_{index}_healed' for index in (32,128,240)),
              'remote_anchor_process_SIGKILL_three_nodes_continue','remote_crash_restart_exact_prefix',
              'lost_physical_node_database_rebuilt_all_streams','local_anchor_unavailable_remote_three_commit','partition_after_two_remote_acks_exact_recovery')
    expected_cases={world+'_'+suffix for world in ('one','two') for suffix in suffixes}
    require(summary['events']==514 and summary['machines']==4 and len(summary['tests'])==22 and set(summary['tests'])==expected_cases,'physical attack coverage')
    challenge.check(BOX)
    print('FOUR PHYSICAL MACHINE AUDIT PASS: 514 QCs; 2056 exact original rows; 22 partition/crash/rollback cases; disclosure and payment retained',flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--verify-only',action='store_true');parser.add_argument('--use-run',type=Path);parser.add_argument('--check-main',action='store_true');args=parser.parse_args()
    require(BOX.is_dir(),'mounted physical evidence missing')
    current=inputs()
    if args.verify_only:
        accepted=json.loads((BOX/'acceptance.json').read_text());require(accepted['inputs']==current,'physical acceptance inputs changed');actual=Path(accepted['actual'])
    else:
        require(args.use_run is not None,'explicit completed physical run required');actual=args.use_run.resolve();collect(actual)
    original=original_chain();independent(actual,original)
    closeout={}
    for tag,cfg in [('pc','pcnode.json'),('spark','sparknode.local.json'),('studio','studionode.local.json')]:
        state=ROOT/'ComputeNode/state'/('public-anchor-'+tag+'-20261102');path=BOX/(tag+'-closeout.json')
        if not args.verify_only:
            result=subprocess.run([sys.executable,str(ROOT/'ComputeNode/mac/hygiene.py'),'check','--config',str(ROOT/'ComputeNode'/cfg),'--state',str(state),'--budget-seconds','30','--output',str(path)],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            require(result.returncode==0,'physical resource closeout incomplete: '+tag+'; '+result.stdout)
        require(json.loads(path.read_text())['closed'],'physical workload resources not closed');closeout[tag]=sha(path)
    if not args.verify_only:(BOX/'acceptance.json').write_text(json.dumps({'actual':str(actual),'inputs':current,'closeout':closeout,'original_acceptance':sha(OLD/'acceptance.json'),'challenge':sha(BOX/'challenge-contract.json')},indent=2)+'\n')
    else:require(accepted['closeout']==closeout and accepted['challenge']==sha(BOX/'challenge-contract.json') and accepted['original_acceptance']==sha(OLD/'acceptance.json'),'physical witness/cleanup receipts changed')
    if args.check_main:
        for path,wanted in current.items():require(hashlib.sha256(subprocess.check_output(['git','show','refs/heads/main:'+path],cwd=ROOT)).hexdigest()==wanted,'main differs: '+path)
        print('PHYSICAL AUDIT MAIN INTEGRATION PASS',flush=True)
    print('DISTRIBUTED AUDIT ACCEPTED: Mac + PC + Spark + Studio; issuer-nonce freshness; closed node resources',flush=True)


if __name__=='__main__':main()
