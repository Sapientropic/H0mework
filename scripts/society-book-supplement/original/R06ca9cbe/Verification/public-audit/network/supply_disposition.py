"""Source recomputation evidence for the original HA intent recovery path.

The complete native reply and generated scope are hashed together. Three literal
signatures fit the original TLS frame without repeating large financial states.
The rejected message remains in ha_rejected_intents; its request is not retired.
"""
from copy import deepcopy
import importlib
import re

from cryptography.exceptions import InvalidSignature

import anchor
from crypto import canonical, digest, verify

SCHEMA = 'native-supply-disposition/v1'
PROJECTION = 'complete-native-and-generated-next/v1'
FEATURES = {'energy-regeneration': ('regeneration', 'regeneration'),
            'energy-material': ('material_regeneration', 'refeed'),
            'energy-productive': ('productive_regeneration', 'productive'),
            'energy-arrival': ('arrival_regeneration', 'arrival'),
            'energy-donor': ('donor_arrival_live', 'donor')}


def reply(event):
    return {key: deepcopy(event[key]) for key in ('native', 'nextScope') if key in event}


def program(settings):
    local = {'cwd', 'lean_path', 'closure', 'exporter', 'error_log', 'native_call_seconds',
             'step_seconds', 'replay_seconds', 'warm_on_start', 'background_warmup'}
    value = {key: deepcopy(item) for key, item in settings.items() if key not in local}
    value['backend'] = ['compiler'] + ['exporter' if item == settings['exporter'] else item
                                      for item in settings['backend'][1:]]
    if 'private_exporter' in value:
        value['private_exporter']['contract'] = 'validated-contract'
    return value


def context_at(config):
    from quorum import membership
    context = config['semantic']['governance_context']
    if (config['semantic_policy'] != config['semantic']['descriptor'] or
            context['semantic']['descriptor'] != config['semantic_policy'] or
            config['ha']['trust'] != context['ha']['trust'] or
            config['ha']['owners'] != context['ha']['owners']):
        raise ValueError('SUPPLY_COMPARISON_POLICY')
    descriptor = config['semantic_policy']; stream = descriptor['stream']
    if (set(config['streams']) != {stream} or context.get('stream') != stream or
            context['source'] != descriptor['source'] or
            config['streams'][stream]['source'] != descriptor['source'] or
            config['streams'][stream]['writer'] != context['registry']['server'] or
            membership(config['ha']['trust']) != config['cluster']):
        raise ValueError('SUPPLY_COMPARISON_NAMESPACE')
    for _, name in FEATURES.values():
        installed = name in config
        if installed != (name in context):
            raise ValueError('SUPPLY_COMPARISON_SOURCE_POLICY')
        if installed:
            public = lambda value: {k: v for k, v in value.items() if k != 'error_log'}
            if public(config[name]) != public(context[name]):
                raise ValueError('SUPPLY_COMPARISON_SOURCE_POLICY')
    for name in ('server', 'auditor1', 'auditor2', 'rotated2'):
        if config['registry'][name] != context['registry'][name]:
            raise ValueError('SUPPLY_COMPARISON_PRINCIPALS')
    return context


def source_at(context, rows, message):
    from donor_arrival_live import authority
    from productive_owner_request import history
    from source_extension import guard
    from governance import registration_bound

    config = authority(context)
    event = message['body']; body = event['request']['body']; stream = event['stream']
    if event['type'] not in FEATURES or set(event) != {
            'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}:
        raise ValueError('SUPPLY_COMPARISON_EVENT')
    try:
        verify(anchor.public_key(config['streams'][stream]['writer']), 'ledger', message)
        keys, sequences, seen = history(config, rows)
        actor = body['actor']; identity = keys[actor]
        verify(anchor.public_key(identity), event['type'], event['request'])
    except (InvalidSignature, KeyError, TypeError, ValueError) as problem:
        raise ValueError('SUPPLY_COMPARISON_SIGNATURE') from problem
    if (event['source'] != config['streams'][stream]['source'] or body['source'] != event['source'] or
            body['stream'] != stream or event['request']['kind'] != event['type'] or
            event['peer'] != identity['fingerprint'] or body['seq'] != sequences.get(actor, 0) + 1 or
            body['nonce'] in seen or body['request_id'] in seen):
        raise ValueError('SUPPLY_COMPARISON_REQUEST')
    guard(context, rows, event)
    registration_bound(event)
    module_name, setting = FEATURES[event['type']]
    module = importlib.import_module(module_name)
    argument = module.argument(context, rows, event)
    return module, argument, program(context[setting])


def binding(context, descriptor, rows, message, argument, compiled):
    from quorum import membership
    event = message['body']
    return dict(schema=SCHEMA, projection=PROJECTION, event_kind=event['type'],
                source=event['source'], stream=event['stream'],
                prefix=dict(seq=len(rows), head=rows[-1][2] if rows else anchor.ZERO),
                event=digest(message), descriptor=deepcopy(descriptor),
                committee=membership(context['ha']['trust']), source_program=digest(compiled),
                source_input=digest(argument), actual=digest(reply(event)))


def compare(engine, rows, message):
    """Called after the original Engine.sync; no caller supplies an expected reply."""
    from source_semantics import Incomplete, Mismatch
    context = engine.config['governance_context']
    if (engine.descriptor != context['semantic']['descriptor'] or
            (engine.count, engine.head) != (len(rows), rows[-1][2] if rows else anchor.ZERO)):
        raise Incomplete('SUPPLY_COMPARISON_SOURCE_PREFIX')
    module, argument, compiled = source_at(context, rows, message)
    # Transport failure, source unavailability and timeout yield no invalid vote.
    result = module.native_call(context, argument)
    expected = deepcopy(message['body']); expected['native'] = result
    expected['nextScope'] = (module.scope_id(context, expected['request']['body']['parent'], result['nextScope'])
                             if result.get('opening') else None)
    module.expected(context, rows, expected, native=False)
    witness = binding(context, engine.descriptor, rows, message, argument, compiled)
    witness.update(classification='verified', expected=digest(reply(expected)))
    if witness['expected'] != witness['actual']:
        witness['classification'] = 'invalid'
        raise Mismatch(witness)
    return witness


def consume(config, rows, message, comparison):
    """Consume three independently signed computations at this exact source cut."""
    context = context_at(config)
    _, argument, compiled = source_at(context, rows, message)
    wanted = binding(context, config['semantic_policy'], rows, message, argument, compiled)
    wanted['classification'] = 'invalid'
    votes = comparison['votes']; members = [vote['member'] for vote in votes]
    if set(comparison) != {'votes'} or members != sorted(set(members)) or not 3 <= len(members) <= 4:
        raise ValueError('SUPPLY_COMPARISON_QUORUM')
    common = None
    for vote in votes:
        try:
            if set(vote) != {'member', 'receipt'}:
                raise ValueError('SUPPLY_COMPARISON_VOTE')
            value = verify(anchor.public_key(config['ha']['trust']['members'][vote['member']]),
                           'source-semantic-decision', vote['receipt'])
        except (InvalidSignature, KeyError, TypeError, ValueError) as problem:
            raise ValueError('SUPPLY_COMPARISON_VOTE_SIGNATURE') from problem
        if (set(value) != set(wanted) | {'expected'} or
                any(canonical(value.get(key)) != canonical(item) for key, item in wanted.items())):
            raise ValueError('SUPPLY_COMPARISON_BINDING')
        expected = value['expected']
        if not isinstance(expected, str) or re.fullmatch('[0-9a-f]{64}', expected) is None or expected == wanted['actual']:
            raise ValueError('SUPPLY_COMPARISON_NOT_DIFFERENT')
        if common is not None and common != expected:
            raise ValueError('SUPPLY_COMPARISON_EXPECTED_FORK')
        common = expected
    return common
