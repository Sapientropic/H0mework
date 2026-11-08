"""Native actor births and paid objections on the original journal.

Registration is identity, never delegation. Material supply and a new scope
remain unavailable until their own source occurrence is admitted.
"""
from __future__ import annotations
import json
import time
from crypto import canonical, digest, verify
from anchor import public_key

_readers = {}


def close_readers():
    for engine in _readers.values():
        engine.close()
    _readers.clear()


def registration_bound(event):
    if ('registration' in event) != ('registration' in event['request']['body']):
        raise ValueError('NATIVE_REGISTRATION_OMITTED')
    if 'registration' in event and (event['type']!='disclosure' or event['request']['kind']!='audit'):
        raise ValueError('NATIVE_REGISTRATION_EVENT_KIND')


def rows_of(database, stream=None):
    if stream is None:
        return database.execute('SELECT id,previous,hash,message FROM events ORDER BY id').fetchall()
    return database.execute('SELECT seq,previous,hash,message FROM entries WHERE stream=? ORDER BY seq',(stream,)).fetchall()


def reader(config):
    from source_semantics import Engine
    settings = config.get('governance')
    if not settings:
        raise ValueError('NATIVE_GOVERNANCE_NOT_INSTALLED')
    key = digest(settings)
    if key not in _readers:
        _readers[key] = Engine(settings)
    engine = _readers[key]
    if engine.process is None or engine.process.poll() is not None:
        engine.start()
    return engine


def native_call(config, body):
    engine = reader(config)
    return engine.call(body, time.monotonic()+30)


def principal(key):
    if type(key) is not str or len(key)!=64 or bytes.fromhex(key).hex()!=key:
        raise ValueError('NATIVE_OWNER_KEY')
    return str(4+int.from_bytes(key.encode(),'big'))


def contents(rows):
    return [json.loads(row[3])['body'] for row in rows]


def registered(rows):
    return [event['registration'] for event in contents(rows)
            if event['type']=='disclosure' and 'registration' in event]


def response_at(rows):
    return next((event for event in contents(rows) if event['type']=='native-response'),None)


def member(config, rows, actor):
    for row in rows:
        event=json.loads(row[3])['body']
        if (event['type']=='disclosure' and str(event['record']['actor'])==actor and
                event['record']['access']=='admitted'):
            return {'seq':row[0],'head':row[2],'cut':event['record']['cut'],'party':int(actor)}
    raise ValueError('NATIVE_MEMBER_HAS_NO_SOURCE_ORIGIN')


def expected(config, rows, event, *, native=True):
    registration_bound(event)
    if response_at(rows):
        raise ValueError('NATIVE_NEW_SCOPE_REQUIRED')
    request=event['request']['body']
    source=config.get('source') or config['streams'][event['stream']]['source']
    if request['source']!=source or event['source']!=source:
        raise ValueError('NATIVE_SOURCE')
    settings=config.get('governance')
    if not settings:raise ValueError('NATIVE_GOVERNANCE_NOT_INSTALLED')
    parent={'seq':len(rows),'head':rows[-1][2] if rows else '0'*64}
    history=[{'cut':prior['record']['cut'],'query':prior['record']['query']}
             for prior in contents(rows) if prior['type']=='disclosure']
    births=[{'cut':entry['result']['cut'],'key':entry['result']['key']} for entry in registered(rows)]
    if event['type']=='disclosure':
        proof=request['registration']
        if set(proof)!= {'body','kind','signature'}:raise ValueError('NATIVE_OWNER_PROOF')
        identity=proof['body']['owner']
        owners=config['ha']['owners']
        body=verify(public_key(owners[identity]),'native-owner-registration',proof)
        key=owners[identity]['app'];principal(key)
        if body!={'source':source,'stream':event['stream'],'parent':parent,'owner':identity,'key':key,'role':'executor'}:
            raise ValueError('NATIVE_OWNER_SCOPE')
        if any(entry['result']['key']==key for entry in registered(rows)):
            raise ValueError('NATIVE_OWNER_ALREADY_REGISTERED')
        if event['registration']['proof']!=proof:raise ValueError('NATIVE_OWNER_PROOF_CHANGED')
        history.append({'cut':event['record']['cut'],'query':event['record']['query']})
        argument={'op':'registration','cut':event['record']['cut'],'history':history,'births':births,'key':key}
        supplied=event['registration']['result']
        if not native:
            if (supplied['key']!=key or supplied['cut']!=event['record']['cut'] or len(supplied['roles'])!=1
                    or supplied['roles'][0]['principal']!=principal(key) or supplied['labor']!='0'):
                raise ValueError('NATIVE_REGISTRATION_SCHEMA')
            return supplied
    elif event['type']=='native-response':
        if request['parent']!=parent:raise ValueError('NATIVE_PARENT')
        origin=member(config,rows,request['actor'])
        if request['member']!=origin:raise ValueError('NATIVE_MEMBER_ORIGIN')
        proposal=request['proposal']
        bad=verify(public_key(config['registry']['server']),'ledger',proposal)
        key=request['executor']
        if not any(entry['result']['key']==key for entry in registered(rows)):
            raise ValueError('NATIVE_EXECUTOR_NOT_REGISTERED')
        owner=next((entry['proof']['body']['owner'] for entry in registered(rows)
                    if entry['result']['key']==key),None)
        execution=verify(public_key(config['ha']['owners'][owner]),'native-owner-response',request['execution'])
        if execution!={'source':source,'stream':event['stream'],'parent':parent,'executor':key,
                      'proposal':digest(proposal),'member':origin,'cut':request['cut'],'epoch':request['epoch']}:
            raise ValueError('NATIVE_EXECUTOR_AUTHORIZATION')
        canonical_event=next((prior for prior in contents(rows) if prior['type']=='disclosure' and
                              prior['request']==bad['request']),None)
        if canonical_event is None or canonical_event['record']==bad['record']:
            raise ValueError('NATIVE_PROPOSAL_HAS_NO_DIFFERENT_ORIGINAL')
        votes=request['comparisons'];seen=set()
        trust=config['ha']['trust']
        for vote in votes:
            who=vote['member']
            if who in seen:raise ValueError('NATIVE_DUPLICATE_COMPARISON')
            witness=verify(public_key(trust['members'][who]),'source-semantic-decision',vote['proof'])
            if (witness['source']!=source or witness['stream']!=event['stream'] or witness['event']!=digest(proposal)
                    or witness['actual']!=bad['record'] or witness['expected']!=canonical_event['record']
                    or witness['classification']!='invalid'
                    or witness['descriptor']!=config['semantic_policy']):
                raise ValueError('NATIVE_COMPARISON_BINDING')
            seen.add(who)
        if len(seen)<3:raise ValueError('NATIVE_COMPARISON_INCOMPLETE')
        argument={'op':'response','cut':request['cut'],'history':history,'births':births,'key':key,
                  'observedCut':bad['record']['cut'],'alleged':bad['record'],'challenger':origin['party']}
        supplied=event['native']
        if not native:
            if (supplied['cut']!=request['cut'] or supplied['key']!=key
                    or supplied['before']['version']!=request['epoch']
                    or supplied['next']['cut']!=request['cut']+1
                    or len(supplied['roles'])!=1 or supplied['roles'][0]['principal']!=principal(key)):
                raise ValueError('NATIVE_RESPONSE_SCHEMA')
            return supplied
    else:raise ValueError('NATIVE_EVENT_KIND')
    actual=native_call(config,argument)
    if actual['before']['version']!=request['epoch'] or actual['cut']!=request['cut']:
        raise ValueError('NATIVE_SOURCE_CURRENT')
    if actual!=supplied:raise ValueError('NATIVE_SOURCE_MISMATCH')
    return actual


def produce(config, rows, event):
    # The same input decoder generates the event before the existing Store's
    # fsync-pending -> quorum intent -> source commit path.
    if event['type']=='disclosure':
        proof=event['request']['body']['registration'];key=proof['body']['key']
        history=[{'cut':prior['record']['cut'],'query':prior['record']['query']} for prior in contents(rows) if prior['type']=='disclosure']
        history.append({'cut':event['record']['cut'],'query':event['record']['query']})
        births=[{'cut':entry['result']['cut'],'key':entry['result']['key']} for entry in registered(rows)]
        result=native_call(config,{'op':'registration','cut':event['record']['cut'],'history':history,'births':births,'key':key})
        event['registration']={'proof':proof,'result':result}
    else:
        body=event['request']['body'];bad=body['proposal']['body']
        history=[{'cut':prior['record']['cut'],'query':prior['record']['query']} for prior in contents(rows) if prior['type']=='disclosure']
        births=[{'cut':entry['result']['cut'],'key':entry['result']['key']} for entry in registered(rows)]
        result=native_call(config,{'op':'response','cut':body['cut'],'history':history,'births':births,'key':body['executor'],
                                 'observedCut':bad['record']['cut'],'alleged':bad['record'],'challenger':member(config,rows,body['actor'])['party']})
        event['native']=result
    expected(config,rows,event)
    return event
