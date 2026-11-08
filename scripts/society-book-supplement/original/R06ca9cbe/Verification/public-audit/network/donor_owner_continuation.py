"""A fresh original-owner permission for one source-generated donor attempt.

The admitted program and its cumulative input are retained. A permission changes
no stock or liability; Donor.Wire executes and pays from its own actual next.
"""
from copy import deepcopy
from fractions import Fraction
import secrets

from cryptography.exceptions import InvalidSignature

import anchor
from crypto import canonical, digest, sign, verify
import donor_arrival_live as donor
from productive_owner_request import history
import governance

PERMIT = 'original-donor-owner-continuation'
SCHEMA = 'original-donor-owner-continuation/v1'
FIELDS = {'source', 'stream', 'actor', 'seq', 'nonce', 'request_id', 'parent', 'member',
          'executor', 'cut', 'epoch', 'scope', 'unit', 'source_root', 'certificate', 'index', 'command'}
TRANSPORT = 'transport_intent'


def command(config, current):
    point = config['donor_admission']['point']
    clock = Fraction(current['clock'])
    if clock.denominator != 1 or point['donor'] != 'audit:3' or point['quantity'] != 6:
        raise ValueError('DONOR_CONTINUATION_SOURCE')
    return dict(kind='donate', quantity=point['quantity'], round=int(clock), signer=3, enabled=True)


def _point(config, rows, request, value, scope, current, plan):
    body = request['body']; original = config['donor_admission']['point']
    inner = body.get(TRANSPORT)
    if TRANSPORT in body:
        if (set(body) != FIELDS | {'continuation', 'expires', TRANSPORT} or
                not isinstance(inner, dict) or not isinstance(inner.get('body'), dict) or
                set(inner['body']) != FIELDS or type(body['expires']) not in (int, float)):
            raise ValueError('DONOR_CONTINUATION_TRANSPORT')
        bare = deepcopy(inner['body'])
        if any(canonical(body[key]) != canonical(bare[key]) for key in FIELDS - {'nonce'}):
            raise ValueError('DONOR_CONTINUATION_TRANSPORT_BINDING')
    else:
        bare = {key: deepcopy(item) for key, item in body.items() if key != 'continuation'}
    if (set(bare) != FIELDS or type(bare['index']) is not int or
            bare['index'] != len(value['commands']) or bare['index'] < len(plan['commands']) or
            canonical(bare['command']) != canonical(command(config, current))):
        raise ValueError('DONOR_CONTINUATION_GENERATED_REQUEST')
    keys, sequences, seen = history(donor.authority(config), rows)
    try:
        verify(anchor.public_key(keys[body['actor']]), donor.ACTION, request)
        if inner is not None:
            verify(anchor.public_key(keys[body['actor']]), donor.ACTION, inner)
    except (InvalidSignature, KeyError, TypeError, ValueError) as problem:
        raise ValueError('DONOR_CONTINUATION_ACTOR') from problem
    if (body['seq'] != sequences.get(body['actor'], 0)+1 or
            body['nonce'] in seen or bare['nonce'] in seen or body['request_id'] in seen):
        raise ValueError('DONOR_CONTINUATION_REPLAY')
    event = dict(type=donor.ACTION, source=body['source'], stream=body['stream'], request=request, scope=body['scope'])
    donor.request_binding(config, rows, event, current, scope)
    return dict(schema=SCHEMA, source=original['source'], stream=original['stream'],
                prefix=donor.prefix(rows), owner=original['owner'], executor=original['executor'],
                original_admission=digest(config['donor_admission']), program=deepcopy(config['donor']['descriptor']),
                cumulative_input=digest(value), current=deepcopy(current), scope=scope, request=digest(bare),
                disposition='authorize-one-source-generated-attempt')


def draft(config, rows, actor):
    """Generate a request from the actual poststate; accept no caller command/state."""
    value, scope, current, plan = donor.context(config, rows)
    if len(value['commands']) < len(plan['commands']):
        raise ValueError('DONOR_CONTINUATION_ORIGINAL_WORD_PENDING')
    keys, sequences, _ = history(donor.authority(config), rows)
    if actor not in keys:
        raise ValueError('DONOR_CONTINUATION_ACTOR')
    original = config['donor_admission']['point']
    return dict(source=original['source'], stream=original['stream'], actor=actor, seq=sequences.get(actor, 0)+1,
                nonce=secrets.token_hex(32), request_id=secrets.token_hex(16), parent=donor.prefix(rows),
                member=governance.member(config, rows, actor), executor=original['executor'],
                cut=current['cut'], epoch=current['version'], scope=scope, unit='energy', source_root=original['source_root'],
                certificate=digest(config['donor_admission']), index=len(value['commands']), command=command(config, current))


def approve(config, rows, request, owner_key):
    if 'continuation' in request['body']:
        raise ValueError('DONOR_CONTINUATION_ALREADY_ATTACHED')
    value, scope, current, plan = donor.context(config, rows)
    point = _point(config, rows, request, value, scope, current, plan)
    if owner_key.public_key().public_bytes_raw().hex() != point['executor']:
        raise ValueError('DONOR_CONTINUATION_OWNER')
    return sign(owner_key, PERMIT, point)


def _consume_at(config, rows, request, value, scope, current, plan):
    point = _point(config, rows, request, value, scope, current, plan)
    original = config['donor_admission']['point']
    try:
        actual = verify(anchor.public_key(config['ha']['owners'][original['owner']]), PERMIT,
                        request['body']['continuation'])
    except (InvalidSignature, KeyError, TypeError, ValueError) as problem:
        raise ValueError('DONOR_CONTINUATION_PERMISSION') from problem
    if actual != point:
        raise ValueError('DONOR_CONTINUATION_BINDING')
    return point


def transport_body(config, rows, intent, permission, challenge):
    """Wrap the unchanged approved intent in the original fresh TLS challenge."""
    if (set(intent['body']) != FIELDS or
            any(canonical(challenge.get(key)) != canonical(intent['body'][key])
                for key in ('source', 'stream', 'actor', 'seq', 'cut', 'epoch')) or
            'nonce' not in challenge or 'expires' not in challenge):
        raise ValueError('DONOR_CONTINUATION_CHALLENGE')
    value, scope, current, plan = donor.context(config, rows)
    point = _point(config, rows, intent, value, scope, current, plan)
    original = config['donor_admission']['point']
    if verify(anchor.public_key(config['ha']['owners'][original['owner']]), PERMIT, permission) != point:
        raise ValueError('DONOR_CONTINUATION_BINDING')
    return {**deepcopy(intent['body']), 'nonce': challenge['nonce'], 'expires': challenge['expires'],
            'continuation': deepcopy(permission), TRANSPORT: deepcopy(intent)}
