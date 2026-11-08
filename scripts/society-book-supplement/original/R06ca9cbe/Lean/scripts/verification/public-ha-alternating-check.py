"""Independently verify the exact alternating crash, takeover and recovery witnesses."""
import importlib.util
import json
from pathlib import Path
import sqlite3
import sys

ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
from anchor import public_key
from crypto import digest, verify
from ha_anchor import verify_quorum

spec=importlib.util.spec_from_file_location('ha_audit_helpers',Path(__file__).with_name('public-ha-check.py'))
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
require=base.require;load=base.load


def check(box, manifest, config, literal):
    p=box/'ha/alternating-01';old=load(p/'baseline.json');server=public_key(config['registry']['server'])
    require(len(literal)==13 and literal[:9]==[tuple(r) for r in old['rows']] and
            old['prior_final']['exit']==0 and old['prior_final']['source_events']==9 and old['prior_final']['labor']==14,
            'alternating run changed the already paid nine-event prefix')
    mac0=base.status(manifest,'mac',old['mac']);spark0=base.status(manifest,'spark',old['spark'])
    require(mac0['phase']=='leader' and spark0['phase']=='standby' and spark0['service'] is None and
            mac0['head']['seq']==spark0['head']['seq']==9,'alternating initial active roles differ')
    boundary=verify(server,'ha-fault-boundary',load(p/'mac-boundary.json'))
    require(boundary['phase']=='after-source' and boundary['seq']==10 and boundary['message']==base.json.loads(literal[9][3]) and
            boundary['previous']==literal[8][2] and boundary['grant']['point']==mac0['grant']['point'],
            'Mac executor did not fail at the exact new source event')
    point=dict(token=boundary['grant']['point'],seq=10,previous=literal[9][1],head=literal[9][2],
               message=digest(boundary['message']),operation_id=boundary['message']['body']['request']['body']['request_id'])
    verify_quorum({'ha':{'trust':manifest['trust']}},boundary['intent'],'ha-intent',point)
    require(load(p/'mac-pending.json')=={k:boundary[k] for k in ('seq','previous','message')} and
            load(p/'mac-unknown.json')=={'error':'OUTCOME_UNKNOWN','request':boundary['message']['body']['request']},
            'executor failure lost original uncertain request')

    def ready(value):return verify(server,'ha-service-ready',value)
    def same_process(a,b):return all(a[k]==b[k] for k in ('pid','birth','boot'))
    def lookup(name, seq):
        result=load(p/name);response=result['response'];event=base.json.loads(literal[seq-1][3])
        require(result['tls']=='TLSv1.3' and response['ledger']==event and response['event']==event['body'] and
                response['request']==digest(event['body']['request']) and
                response['request_id']==event['body']['request']['body']['request_id'], 'recovery lookup changed original event')
        base.original_check.certificate(config,response['anchor'],base.original_check.point(config,literal[seq-1]))

    mac1=load(p/'mac-executor-after.json');mac1_state=base.status(manifest,'mac',mac1['coordinator'])
    mac_ready0=ready(load(p/'mac-executor-before.json'));mac_ready1=ready(mac1['ready'])
    require(same_process(mac0,mac1_state) and mac1_state['phase']=='leader' and mac1_state['head']['seq']==10 and
            mac1_state['grant']['point']==mac0['grant']['point'] and
            mac_ready1['pid']!=mac_ready0['pid'] and mac_ready1['backend']['pid']!=mac_ready0['backend']['pid'],
            'Mac executor was not rebuilt by the same original coordinator/grant')
    lookup('mac-executor-recovered.json',10);lookup('paid-lookup-1.json',8)

    before_mac=load(p/'mac-domain-before.json');mac2=base.status(manifest,'mac',before_mac['mac'])
    spark2=base.status(manifest,'spark',before_mac['spark']);spark3=base.status(manifest,'spark',load(p/'spark-takeover.json'))
    require(load(p/'mac-domain-frozen.json')==mac2 and set(mac2['members'])==set('abcd') and
            same_process(spark0,spark2) and same_process(spark2,spark3) and spark3['phase']=='leader' and
            spark3['head']['seq']==10 and spark3['grant']['point']['epoch']>mac2['grant']['point']['epoch'] and
            [v['member'] for v in spark3['grant']['votes']]==list('bcd'),'Mac-domain failure did not cause independent remote takeover')
    verify_quorum({'ha':{'trust':manifest['trust']}},spark3['grant'],'ha-grant',spark3['grant']['point'])
    returned_mac=base.status(manifest,'mac',load(p/'mac-returned.json'))
    require(returned_mac['phase']=='standby' and returned_mac['service'] is None and returned_mac['head']['seq']==11 and
            same_process(mac2,returned_mac),'returning Mac failed nonwriter catchup')
    lookup('paid-lookup-2.json',8);lookup('spark-next11.json',11)
    require([v['member'] for v in load(p/'spark-next11.json')['response']['anchor']['votes']]==list('bcd'),
            'new event depended on the unavailable Mac domain')

    before_exec=load(p/'spark-executor-before.json');spark4=base.status(manifest,'spark',before_exec['coordinator'])
    ready4=ready(before_exec['ready']);killed=load(p/'spark-execution-killed.json')
    after_exec=load(p/'spark-executor-after.json');spark5=base.status(manifest,'spark',after_exec['coordinator']);ready5=ready(after_exec['ready'])
    anchor_before=verify(public_key(manifest['trust']['members']['c']),'recovery-host-status',killed['host_status'])
    anchor_after=verify(public_key(manifest['trust']['members']['c']),'recovery-host-status',after_exec['anchor'])
    require(killed['backend']==ready4['backend'] and killed['anchor']==anchor_before['process'] and killed['service_alive_at_injection'] and
            same_process(spark4,spark5) and spark5['grant']['point']==spark4['grant']['point'] and
            ready4['pid']!=ready5['pid'] and ready4['backend']['pid']!=ready5['backend']['pid'] and
            anchor_before['boot']==anchor_after['boot']==spark5['boot'] and anchor_before['process']['pid']!=anchor_after['process']['pid'] and
            spark5['phase']=='leader' and spark5['head']['seq']==11,'native Lean/anchor executor failure did not rebuild under the original managers')
    lookup('paid-lookup-3.json',8);lookup('spark-next12.json',12)

    before_spark=load(p/'spark-domain-before.json');spark6=base.status(manifest,'spark',before_spark['spark'])
    mac6=base.status(manifest,'mac',before_spark['mac']);frozen=load(p/'spark-domain-frozen.json')
    mac7=base.status(manifest,'mac',load(p/'mac-takeover.json'))
    require(frozen['coordinator']==spark6 and set(frozen['groups'])=={'service','anchor'} and
            frozen['groups']['service']==spark6['service'] and same_process(mac6,mac7) and same_process(mac2,mac7) and
            mac7['phase']=='leader' and mac7['head']['seq']==12 and
            mac7['grant']['point']['epoch']>spark6['grant']['point']['epoch'] and
            [v['member'] for v in mac7['grant']['votes']]==list('abd'),'Spark-domain failure did not cause surviving a/b/d takeover')
    verify_quorum({'ha':{'trust':manifest['trust']}},mac7['grant'],'ha-grant',mac7['grant']['point'])
    returned=base.status(manifest,'spark',load(p/'spark-returned.json'));final_mac=base.status(manifest,'mac',load(p/'final-mac.json'))
    require(returned['phase']=='standby' and returned['service'] is None and returned['head']['seq']==13 and
            same_process(spark6,returned) and final_mac['phase']=='leader' and final_mac['head']['seq']==13 and
            same_process(mac7,final_mac),'final nonwriter recovery or active service differs')
    lookup('paid-lookup-4.json',8);lookup('paid-lookup-final.json',8);lookup('mac-next13.json',13)
    require([v['member'] for v in load(p/'mac-next13.json')['response']['anchor']['votes']]==list('abd'),
            'new event depended on the unavailable Spark anchor')
    for row in literal[9:]:
        record=base.json.loads(row[3])['body']['record']
        require(record['access'] in {'unfunded','expired','unauthorized'} and record['labor']=='0',
                'new continuation changed already exhausted financing or charged a refusal')
    db=sqlite3.connect((box/'local-anchor/journal.sqlite').as_uri()+'?mode=ro',uri=True)
    try:proofs=dict(db.execute('SELECT seq,payload FROM ha_proofs JOIN ha_events ON ha_proofs.event=ha_events.id WHERE seq>=10'))
    finally:db.close()
    for seq,holder in [(10,mac0),(11,spark3),(12,spark5),(13,mac7)]:
        proof=verify(public_key(manifest['trust']['members']['a']),'ha-event',json.loads(proofs[seq]))
        require(proof['point']['token']==holder['grant']['point'] and proof['point']['head']==literal[seq-1][2],
                'new original event was committed by a different owner or term')
    final=load(p/'final.json');require([tuple(r) for r in final['rows']]==literal,'final original event bytes differ')
    for member, point in final['anchors'].items():
        require(point['boot']==old['anchors'][member]['boot'],'physical host rebooted during alternating faults')
    require(set(final['anchors'])==set('abcd'),'missing final physical anchor evidence')
    print('ALTERNATING FAULTS PASS: exact uncertain event10; two preexisting-candidate handovers bcd/abd; native Lean and anchor rebuild; four paid-event lookups unchanged',flush=True)
