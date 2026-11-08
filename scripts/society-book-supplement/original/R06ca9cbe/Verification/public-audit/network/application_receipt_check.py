"""Reconstruct application observations from signed literal stages, without PASS flags."""
from __future__ import annotations
import base64
from collections import OrderedDict
from crypto import canonical,digest,verify
from application_receipts import KIND,ZERO
from online_privacy_check import frames


def replay(records,key,source,stream,side,registry):
    attempts=OrderedDict();previous=ZERO
    for index,signed in enumerate(records):
        item=verify(key,KIND,signed)
        if (set(item)!={'index','previous','source','stream','side','attempt','stage','at_ns','data'}
                or item['index']!=index or item['previous']!=previous or item['source']!=source
                or item['stream']!=stream or item['side']!=side or type(item['at_ns']) is not int):
            raise ValueError('APPLICATION_CHAIN')
        previous=digest(signed);identity=item['attempt'];stage=item['stage'];data=item['data']
        if stage=='opened':
            if identity in attempts:raise ValueError('APPLICATION_DUPLICATE_ATTEMPT')
            signer=registry['auditor'+data['actor']] if side=='client' else registry['server']
            if key.public_bytes_raw().hex()!=signer['app']:raise ValueError('APPLICATION_SIGNER_ROLE')
            attempts[identity]=dict(records=[],closed=False,tls=None,challenge=None,request=None,
                intended=None,sent=False,response=None,io={'received':b'','sent':b''},last=item['at_ns'])
        if identity not in attempts:raise ValueError('APPLICATION_MISSING_OPEN')
        state=attempts[identity]
        if state['closed'] or item['at_ns']<state['last']:raise ValueError('APPLICATION_ORDER')
        if state.get('rejection') and stage!='closed':raise ValueError('APPLICATION_REJECTED_TERMINAL')
        state['last']=item['at_ns'];state['records'].append(signed)
        if stage=='opened':pass
        elif stage=='tls':
            if state['tls'] is not None or data['tls']!='TLSv1.3' or not data['cipher']:raise ValueError('APPLICATION_TLS')
            peer=data['peer'];expected=registry['server'] if side=='client' else next(
                entry for entry in registry.values() if entry.get('app')==peer['app'] and entry.get('fingerprint')==peer['fingerprint'])
            if peer['app']!=expected['app'] or peer['fingerprint']!=expected['fingerprint']:
                raise ValueError('APPLICATION_PEER')
            if peer['uri']!='urn:public-audit:'+expected['actor']:raise ValueError('APPLICATION_PEER_ROLE')
            state['tls']=data
        elif stage=='challenge':
            if side!='client' or state['tls'] is None or state['challenge'] is not None:raise ValueError('APPLICATION_CHALLENGE_ORDER')
            body=verify(key_from(registry['server']),'challenge',data)
            if body['source']!=source or body['stream']!=stream:raise ValueError('APPLICATION_NAMESPACE')
            if body['actor']!=state['records'][0]['body']['data']['actor']:raise ValueError('APPLICATION_ACTOR')
            state['challenge']=data
        elif stage=='send-intent':
            if side!='client' or state['challenge'] is None or state['intended'] is not None:raise ValueError('APPLICATION_INTENT_ORDER')
            challenge=state['challenge']['body'];actor=registry['auditor'+challenge['actor']]
            body=verify(key_from(actor),data['kind'],data)
            if any(body.get(k)!=challenge[k] for k in ('source','stream','actor','nonce','seq','cut','epoch','expires')):
                raise ValueError('APPLICATION_CHALLENGE_BINDING')
            state['intended']=data
        elif stage=='sent':
            if state['intended'] is None or state['sent'] or data!={'request':digest(state['intended'])}:raise ValueError('APPLICATION_SENT_ORDER')
            state['sent']=True
        elif stage=='response':
            if not state['sent'] or state['response'] is not None:raise ValueError('APPLICATION_RESPONSE_ORDER')
            if data['kind'] not in ('response','lookup-response','error'):raise ValueError('APPLICATION_RESPONSE_KIND')
            verify(key_from(registry['server']),data['kind'],data);state['response']=data
        elif stage=='preflight-rejected':
            if side!='client' or state['challenge'] is None or state['intended'] is not None:raise ValueError('APPLICATION_PREFLIGHT_ORDER')
            if not data.get('code'):raise ValueError('APPLICATION_PREFLIGHT_REASON')
            state['rejection']=data
        elif stage=='transport-error':
            if side!='client' or state['intended'] is None or state['response'] is not None:raise ValueError('APPLICATION_TRANSPORT_ORDER')
            state['transport_error']=data
        elif stage=='io':
            if side!='server' or state['tls'] is None or data['direction'] not in state['io']:raise ValueError('APPLICATION_IO_ORDER')
            state['io'][data['direction']]+=base64.b64decode(data['bytes'],validate=True)
        elif stage=='closed':
            if set(data)!={'error'}:raise ValueError('APPLICATION_CLOSE_FIELDS')
            state['closed']=True;state['error']=data['error']
        else:raise ValueError('APPLICATION_STAGE')
    for identity,state in attempts.items():
        if side=='server':
            try:sent,received=frames(state['io']['sent']),frames(state['io']['received'])
            except (AssertionError,ValueError):
                state.update(status='insufficient',reason='partial-application-frame');continue
            if len(sent)>2 or len(received)>1:raise ValueError('APPLICATION_FRAME_COUNT')
            if sent:
                verify(key_from(registry['server']),'challenge',sent[0]);state['challenge']=sent[0]
            if received:
                if not sent:raise ValueError('APPLICATION_REQUEST_BEFORE_CHALLENGE')
                actor=registry['auditor'+sent[0]['body']['actor']];request=received[0]
                body=verify(key_from(actor),request['kind'],request)
                if any(body.get(k)!=sent[0]['body'][k] for k in ('source','stream','actor','nonce','seq','cut','epoch','expires')):
                    raise ValueError('APPLICATION_SERVER_BINDING')
                state['request']=request
            if len(sent)==2:
                if not received and sent[1]['kind']!='error':raise ValueError('APPLICATION_RESPONSE_WITHOUT_REQUEST')
                verify(key_from(registry['server']),sent[1]['kind'],sent[1]);state['response']=sent[1]
        request=state['intended'] if side=='client' else state['request']
        response=state['response']
        if response and response['kind'] in ('response','lookup-response'):
            if request is None or response['body']['request']!=digest(request):raise ValueError('APPLICATION_RESPONSE_BINDING')
        state['status']='verified' if state['closed'] and state['tls'] and response else 'insufficient'
        if side=='server' and state['closed'] and state['tls'] and state['challenge'] and not state['io']['received'] and any(
                r['body']['stage']=='io' and r['body']['data']['direction']=='received' and r['body']['data']['bytes']=='' for r in state['records']):
            state['status']='verified-no-command'
        if side=='client' and state.get('rejection') and state['closed']:state['status']='verified-preflight-rejection'
        state['tail']=digest(state['records'][-1])
    return attempts


def key_from(identity):
    from anchor import public_key
    return public_key(identity)


def recover(state,lookup):
    """Resolve a missing reply with a separately observed original-ID lookup."""
    request=state['intended'];response=lookup['response']
    if state['status']!='insufficient' or request is None or lookup['status']!='verified':raise ValueError('APPLICATION_RECOVERY_STATE')
    if lookup['intended']['kind']!='lookup' or response['kind']!='lookup-response':raise ValueError('APPLICATION_RECOVERY_KIND')
    result=response['body']['result']
    if (lookup['intended']['body']['lookup_id']!=request['body']['request_id']
            or result['event']['request']!=request or result['request']!=digest(request)):
        raise ValueError('APPLICATION_RECOVERY_ID')
    return dict(status='recovered',original=state['tail'],evidence=lookup['tail'],ledger=digest(result['ledger']))


def server_recovery(client,server):
    if (client['status']!='insufficient' or server['status']!='verified'
            or client['intended']!=server['request'] or client['challenge']!=server['challenge']):
        raise ValueError('APPLICATION_SERVER_RECOVERY')
    return dict(status='recovered-outcome',original=client['tail'],evidence=server['tail'],
                response=digest(server['response']),client_received=False)
