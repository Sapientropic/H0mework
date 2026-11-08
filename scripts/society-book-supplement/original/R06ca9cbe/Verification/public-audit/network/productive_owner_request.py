"""Registered actor intent -> original executor owner approval -> native result."""
from copy import deepcopy
import json
import secrets

from cryptography.exceptions import InvalidSignature

import anchor
from crypto import canonical,digest,sign,verify
import governance
import productive_regeneration as productive

INTENT='productive-isolated-intent'
APPROVAL='productive-owner-approval'
PURPOSE='isolated-source-execution'


def context(config):
    value=config['semantic']['governance_context']
    if (value['source']!=config['streams']['recovery']['source'] or value['stream']!='recovery'
            or value['productive']['descriptor']!=config['productive']['descriptor']
            or value['ha']['owners']!=config['ha']['owners']):
        raise ValueError('OWNER_SOURCE_CONTEXT')
    return value


def history(config,rows):
    source=config['streams']['recovery']['source'];previous=anchor.ZERO
    keys={config['registry'][name]['actor']:config['registry'][name] for name in ('auditor1','auditor2')}
    sequences={};seen=set()
    try:
        for index,(seq,before,head,text) in enumerate(rows,1):
            message=json.loads(text)
            if seq!=index or before!=previous or anchor.ledger_hash(before,message)!=head:
                raise ValueError('OWNER_PREFIX_CHAIN')
            event=verify(anchor.public_key(config['streams']['recovery']['writer']),'ledger',message)
            body=event['request']['body'];identity=keys[body['actor']]
            verify(anchor.public_key(identity),event['request']['kind'],event['request'])
            if (event['source']!=source or event['stream']!='recovery' or body['source']!=source
                    or body['seq']!=sequences.get(body['actor'],0)+1
                    or body['nonce'] in seen or body['request_id'] in seen):
                raise ValueError('OWNER_PREFIX_REQUEST')
            if event['type']=='rotation':
                new=event['new'];challenge={key:body[key] for key in ('source','stream','actor','nonce','seq','cut','epoch','expires')}
                proof=verify(anchor.public_key(new),'new-key',body['new_signature'])
                if (body['actor']!='2' or event['request']['kind']!='rotate'
                        or new!=config['registry']['rotated2'] or event['old']!=identity['fingerprint']
                        or body['rotation']!=new or proof!=dict(challenge=digest(challenge),rotation=new)):
                    raise ValueError('OWNER_PREFIX_ROTATION')
                keys[body['actor']]=new
            sequences[body['actor']]=body['seq'];seen.update((body['nonce'],body['request_id']));previous=head
    except InvalidSignature as problem:raise ValueError('OWNER_PREFIX_SIGNATURE') from problem
    return keys,sequences,seen


def registration(config,rows,owner='spark'):
    history(config,rows);matches=[];ctx=context(config)
    for index,row in enumerate(rows):
        event=json.loads(row[3])['body']
        if 'registration' not in event:continue
        try:governance.expected(ctx,rows[:index],event,native=False)
        except (InvalidSignature,KeyError,ValueError,TypeError) as problem:
            raise ValueError('OWNER_REGISTRATION_PROOF') from problem
        entry=event['registration']
        if entry['proof']['body']['owner']==owner:
            if entry['result']['key']!=config['ha']['owners'][owner]['app']:
                raise ValueError('OWNER_REGISTRATION_KEY')
            matches.append(entry)
    if len(matches)!=1:raise ValueError('OWNER_REGISTRATION_UNIQUE')
    return matches[0]


def draft(config,rows,actor,command,*,owner='spark'):
    entry=registration(config,rows,owner);ctx=context(config)
    _,scope,current=productive.context(ctx,rows);keys,sequences,_=history(config,rows)
    if actor not in keys:raise ValueError('OWNER_ACTOR')
    body=dict(source=ctx['source'],stream='recovery',actor=actor,seq=sequences.get(actor,0)+1,
              nonce=secrets.token_hex(32),request_id=secrets.token_hex(16),parent=dict(seq=len(rows),head=rows[-1][2]),
              member=governance.member(ctx,rows,actor),executor=entry['result']['key'],cut=current['cut'],
              epoch=current['version'],command=deepcopy(command),scope=scope,unit='energy')
    return dict(schema='productive-isolated-intent/v1',purpose=PURPOSE,owner=owner,
                owner_key=config['ha']['owners'][owner]['app'],request=body,
                authorization=productive.authorization(ctx,body))


def inspect(config,rows,intent):
    value=intent['body'];body=value['request'];owner=value['owner'];ctx=context(config)
    entry=registration(config,rows,owner);keys,sequences,seen=history(config,rows)
    try:verify(anchor.public_key(keys[body['actor']]),INTENT,intent)
    except (InvalidSignature,KeyError,ValueError,TypeError) as problem:raise ValueError('OWNER_INTENT_SIGNATURE') from problem
    _,scope,current=productive.context(ctx,rows)
    if (set(value)!={'schema','purpose','owner','owner_key','request','authorization'}
            or value['schema']!='productive-isolated-intent/v1' or value['purpose']!=PURPOSE
            or value['owner_key']!=config['ha']['owners'][owner]['app']):
        raise ValueError('OWNER_INTENT_BINDING')
    if (set(body)!={'source','stream','actor','seq','nonce','request_id','parent','member','executor','cut','epoch','command','scope','unit'}
            or body['source']!=ctx['source'] or body['stream']!='recovery' or body['unit']!='energy'
            or body['parent']!=dict(seq=len(rows),head=rows[-1][2]) or body['scope']!=scope
            or (body['cut'],body['epoch'])!=(current['cut'],current['version'])
            or body['executor']!=entry['result']['key'] or body['member']!=governance.member(ctx,rows,body['actor'])
            or body['seq']!=sequences.get(body['actor'],0)+1 or body['nonce'] in seen or body['request_id'] in seen
            or value['authorization']!=productive.authorization(ctx,body)):
        raise ValueError('OWNER_INTENT_CURRENT')
    return deepcopy(body)


def approval_point(config,rows,intent,authorization):
    value=intent['body']
    return dict(schema='productive-owner-approval/v1',purpose=PURPOSE,source=value['request']['source'],stream='recovery',
                parent=dict(seq=len(rows),head=rows[-1][2]),owner=value['owner'],owner_key=value['owner_key'],
                executor=value['request']['executor'],intent=digest(intent),authorization=digest(authorization),
                descriptor=config['productive']['descriptor'])


def approve(config,rows,intent,owner_key):
    body=inspect(config,rows,intent);owner=intent['body']['owner']
    if owner_key.public_key().public_bytes_raw().hex()!=config['ha']['owners'][owner]['app']:
        raise ValueError('OWNER_SIGNER')
    authorization=sign(owner_key,'native-productive-regeneration',productive.authorization(context(config),body))
    return dict(authorization=authorization,approval=sign(owner_key,APPROVAL,approval_point(config,rows,intent,authorization)))


def consume(config,rows,intent,packet):
    body=inspect(config,rows,intent);key=anchor.public_key(config['ha']['owners'][intent['body']['owner']])
    try:
        authorized=verify(key,'native-productive-regeneration',packet['authorization'])
        approved=verify(key,APPROVAL,packet['approval'])
    except (InvalidSignature,KeyError,TypeError,ValueError) as problem:raise ValueError('OWNER_APPROVAL_SIGNATURE') from problem
    if (authorized!=productive.authorization(context(config),body)
            or approved!=approval_point(config,rows,intent,packet['authorization'])):
        raise ValueError('OWNER_APPROVAL_BINDING')
    return body


def produce(config,rows,intent,packet,*,actor_key,writer_key):
    body=consume(config,rows,intent,packet);keys,_,_=history(config,rows)
    if (actor_key.public_key().public_bytes_raw().hex()!=keys[body['actor']]['app']
            or writer_key.public_key().public_bytes_raw().hex()!=config['streams']['recovery']['writer']['app']):
        raise ValueError('OWNER_REQUEST_SIGNERS')
    body['execution']=packet['authorization'];identity=keys[body['actor']]
    event=dict(type=productive.KIND,source=body['source'],stream='recovery',
               request=sign(actor_key,productive.KIND,body),peer=identity['fingerprint'],scope=body['scope'])
    productive.produce(context(config),rows,event)
    return sign(writer_key,'ledger',event)


def verify_message(config,rows,intent,packet,message):
    body=consume(config,rows,intent,packet);keys,_,_=history(config,rows)
    try:
        event=verify(anchor.public_key(config['streams']['recovery']['writer']),'ledger',message)
        actual=verify(anchor.public_key(keys[body['actor']]),productive.KIND,event['request'])
    except (InvalidSignature,KeyError,TypeError,ValueError) as problem:raise ValueError('OWNER_MESSAGE_SIGNATURE') from problem
    wanted={**body,'execution':packet['authorization']}
    if (canonical(actual)!=canonical(wanted) or event['type']!=productive.KIND
            or event['scope']!=body['scope'] or event['peer']!=keys[body['actor']]['fingerprint']):
        raise ValueError('OWNER_MESSAGE_INTENT')
    productive.expected(context(config),rows,event,native=False)
    return deepcopy(event['native'])
