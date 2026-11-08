"""Consume raw donor wire evidence and its lossless logical result view."""
import base64
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
from anchor import public_key
from application_receipt_check import replay
from crypto import digest,verify
from donor_result_codec import enabled as codec_enabled,decode_body
from online_privacy import source_input
from online_privacy_check import frames,tls_streams
from quorum import verify_certificate


def records(path):return [json.loads(v) for v in Path(path).read_text().splitlines()]


def committed_error(manifest,cfg,rows,request,body):
    assert body['code'] in {'ANCHOR_RECONCILIATION_REQUIRED','ANCHOR_COMMITTED_RECOVERY_REQUIRED','FRAME_TOO_LARGE'}
    matches=[r for r in rows if json.loads(r[3])['body'].get('request')==request]
    assert len(matches)==1,'DONOR_RECOVERY_REQUIRES_ORIGINAL_COMMITTED_EVENT'
    row=matches[0]
    if body['code']=='FRAME_TOO_LARGE':
        assert body['request']==digest(request)
        verify_certificate(manifest['trust'],body['anchor'],source=cfg['source'],stream='recovery',
            seq=row[0],previous=row[1],head=row[2],message=json.loads(row[3]))
    return row


def wire(box,manifest,home,rows,before,expected_events=13):
    cfg=manifest['mac']['service'];directory=home/'actual';server=public_key(cfg['registry']['server']);admitted=codec_enabled(cfg)
    client=replay(records(directory/'applications.jsonl'),public_key(cfg['registry']['auditor2']),cfg['source'],'recovery','client',cfg['registry'])
    counterparts={};boundaries=[];wire_observations=[]
    for owner in ('mac','spark'):
        counterparts.update(replay(records(directory/(owner+'-applications.jsonl')),server,cfg['source'],'recovery','server',cfg['registry']))
        for signed in records(directory/(owner+'-boundary.jsonl')):
            if signed['kind']=='online-privacy-boundary':boundaries.append(verify(server,signed['kind'],signed))
            elif signed['kind']=='online-wire-observation':wire_observations.append(verify(server,signed['kind'],signed))
    incomplete=[];matched=[];lookups=0;direct=0;direct_ids=set();lookup_ids={};recoveries=[];projected=0
    for identity,value in client.items():
        peers=[v for v in counterparts.values() if v['challenge']==value['challenge']]
        assert len(peers)==1;peer=peers[0];matched.append(peer)
        assert value['tls']['tls']==peer['tls']['tls']=='TLSv1.3'
        candidates=[]
        for observation in wire_observations:
            data={'sent':b'','received':b''}
            for op in observation['operations']:data[op['direction']]+=base64.b64decode(op['bytes'],validate=True)
            sent=frames(data['sent'])
            if sent and sent[0]==value['challenge']:candidates.append(data)
        assert candidates==[peer['io']],'DONOR_APPLICATION_AND_WIRE_BYTES'
        if value['intended'] is None:
            assert value['status']=='insufficient'
            outcome=peer['status']
            if outcome!='verified-no-command':
                assert outcome=='verified' and peer['request'] is None and peer['io']['received']==b''
                assert peer['response']['kind']=='error' and verify(server,'error',peer['response'])=={'code':'TimeoutError'}
                outcome='verified-pre-command-timeout'
            incomplete.append(dict(attempt=identity,observation='insufficient',outcome=outcome,support=peer['tail']))
            continue
        assert value['status']==peer['status']=='verified' and value['response']==peer['response']
        request=value['intended'];response=value['response']
        # Keep response unchanged for literal application/TLS checks above.
        body=decode_body(response['kind'],verify(server,response['kind'],response),admitted=admitted)
        if response['kind']=='error':
            assert request['kind']!='lookup'
            row=committed_error(manifest,cfg,rows,request,body)
            recoveries.append(dict(attempt=identity,observation='verified-error',code=body['code'],
                request_id=request['body']['request_id'],seq=row[0],outcome='verified-original-id-recovery'))
            continue
        raw_result=response['body']['result'] if response['kind']=='lookup-response' else response['body']
        projected+=int('event_ref' in raw_result)
        result=body['result'] if response['kind']=='lookup-response' else body
        seq=result['anchor']['body']['seq'];row=rows[seq-1]
        assert result['ledger']==json.loads(row[3]) and result['event']==result['ledger']['body']
        verify_certificate(manifest['trust'],result['anchor'],source=cfg['source'],stream='recovery',seq=row[0],previous=row[1],head=row[2],message=result['ledger'])
        if request['kind']=='lookup':
            assert request['body']['lookup_id']==result['event']['request']['body']['request_id'];lookups+=1
            lookup_ids.setdefault(request['body']['lookup_id'],[]).append(dict(attempt=identity,seq=seq))
        else:
            assert result['event']['request']==request;direct+=1;direct_ids.add(request['body']['request_id'])
    recovered_ids={r['request_id'] for r in recoveries}
    assert direct_ids.isdisjoint(recovered_ids) and len(direct_ids|recovered_ids)==expected_events
    assert lookups==2*expected_events+len(recoveries)
    for recovery in recoveries:
        matches=[v for v in lookup_ids.get(recovery['request_id'],[]) if v['seq']==recovery['seq']]
        assert len(matches)>=3,'DONOR_RECOVERY_LINKS_LOOKUP_AND_TWO_IDEMPOTENCE_READS'
        recovery['lookup_attempts']=[v['attempt'] for v in matches]
    for identity in direct_ids:assert len(lookup_ids.get(identity,[]))==2
    streams=tls_streams(directory,expected_connections=len(client))
    for row in rows[len(before):]:
        event=json.loads(row[3])['body'];argument=source_input(cfg,rows[:row[0]-1],event)
        assert any(b['phase']=='before-intent' and b['seq']==row[0] and b['event']==digest(event) and b['input']==argument and b['native']==digest(event['native']) for b in boundaries)
    return dict(attempts=len(client),direct=direct,lookups=lookups,dual_literal_replays=len(matched),tls_streams=len(streams),
        lossless_projected_replies=projected,dispositions=incomplete,recovered=recoveries,pending=0)
