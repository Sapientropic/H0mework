"""Paid original pair -> normalized full window/CEM posterior and time law.

The physical restriction uses settings, herald and CEM bits.  Complete raw
rows remain bound to the restriction, while UID identity and PC timestamps
are not promoted into a quantum clock.  Hidden BSM patterns are summed.
"""
from dataclasses import dataclass
from fractions import Fraction as Q

import atomic_dipole as dipole
import atomic_full_forward as full
import joint_clock_observation as original
import window_cem_source as window
import window_receipt_programme as programme
from bsm_retry_source import PATTERNS


@dataclass(frozen=True)
class Encoding:
    click_tokens: tuple = ('1', '1')
    setting_zero_tokens: tuple = ('0', '0')
    herald_labels: tuple = ('Psi+', 'Psi-')

    def __post_init__(self):
        for tokens in (self.click_tokens, self.setting_zero_tokens):
            if type(tokens) is not tuple or len(tokens) != 2 or any(token not in ('0', '1') for token in tokens):
                raise ValueError('two raw binary token maps required')
        if type(self.herald_labels) is not tuple or sorted(self.herald_labels) != ['Psi+', 'Psi-']:
            raise ValueError('complete physical herald token bijection required')

    def record(self):
        return {'click_tokens': list(self.click_tokens), 'setting_zero_tokens': list(self.setting_zero_tokens),
                'herald_labels': list(self.herald_labels), 'raw_label_maps_uniquely_identified': False}


@dataclass(frozen=True)
class Posterior:
    source_interval: programme.Interval
    raw_encoding: dict
    original_pair: tuple
    original_rows: tuple
    physical_settings: tuple
    physical_herald: str
    physical_clicks: tuple
    conditional_probability_bounds: tuple
    unnormalized_trap_input: dict
    normalized_trap_input: dict
    normalizer_center: Q
    normalizer_bounds: tuple
    posterior_trace_norm_error: Q
    physical_restriction_certified: bool = True
    complete_record_clock_square_certified: bool = False
    actual_hardware_uniquely_identified: bool = False


def _trace(matrix):
    value = sum((value for (_, _, i, j), value in matrix.items() if i == j), dipole.ComplexRadical())
    if value.imag:
        raise ValueError('full posterior trace is not real')
    return value.real.as_rational()


def _norm(matrix):
    return sum((abs(value.real.as_rational())+abs(value.imag.as_rational()) for value in matrix.values()), Q(0))


def _combine(target, matrix):
    for key, value in matrix.items():
        window.local._add(target, key, value)


def _event_state(source, result, herald, clicks):
    selected, all_herald = {}, {}
    for pattern, report in enumerate(result.reports):
        if PATTERNS[pattern][0] != herald:
            continue
        for outcome in window.REGISTRATION_ORDER:
            state = source.coarsen(report, clicks=outcome)
            _combine(all_herald, state)
            if outcome == clicks:
                _combine(selected, state)
    return selected, all_herald


def decode_observation(first, second, admitted, pair_row, encoding=Encoding()):
    """Transport the original parser's indices, including literal Psi labels."""
    if type(encoding) is not Encoding:
        raise ValueError('original raw Encoding constructor required')
    first, second, trials = original._intake(first, second, admitted)
    if type(pair_row) is not int or not 1 <= pair_row <= len(trials):
        raise ValueError('original admitted pair row required')
    trial = trials[pair_row-1]
    rows = first.observations[trial.row_a], second.observations[trial.row_b]
    if any(row[2] not in ('0', '1') or row[3] not in ('0', '1') for row in rows):
        raise ValueError('original physical observation tokens required')
    raw_tokens = (rows[0][5], rows[0][2], rows[1][2], rows[0][3], rows[1][3])
    for field, token, bit in zip(('h', 'a', 'b', 'x', 'y'), raw_tokens,
                               (trial.h, trial.a, trial.b, trial.x, trial.y)):
        dictionary = admitted.token_dictionaries.get(field)
        allowed = (['Psi+', 'Psi-'], ['0', '1']) if field == 'h' else (['0', '1'],)
        if type(dictionary) is not list or dictionary not in allowed or dictionary[bit] != token:
            raise ValueError('original dictionary: raw tokens differ from the admitted pair')
    settings = tuple(int(row[2] != token) for row, token in zip(rows, encoding.setting_zero_tokens))
    clicks = tuple(int(row[3] == token) for row, token in zip(rows, encoding.click_tokens))
    herald = encoding.herald_labels[trial.h]
    return rows, original._origin(first.run, trial), settings, herald, clicks


def condition(producer, result, first, second, admitted, pair_row, *, encoding=Encoding()):
    if type(producer) is not programme.WindowReceiptProgramme or type(encoding) is not Encoding:
        raise ValueError('closed generated window programme and raw encoding required')
    rows, origin, settings, herald, clicks = decode_observation(first, second, admitted, pair_row, encoding)
    control = producer.public_control_binding
    if control is None or tuple(control['settings']) != settings:
        raise ValueError('observed nominal settings differ from the original applied control source')
    producer.verify(result)
    if result.receipt_interval != producer.law.support:
        raise ValueError('posterior normalizer requires the whole original receipt support')
    selected, total = _event_state(producer.source, result, herald, clicks)
    mass, herald_mass, error = _trace(selected), _trace(total), result.global_trace_norm_error
    lo, hi = max(Q(0), mass-error), mass+error
    h_lo, h_hi = max(Q(0), herald_mass-error), herald_mass+error
    if lo <= 0 or h_lo <= 0:
        raise ValueError('source enclosure cannot certify the observed-event normalizer is positive')
    normalized = {key: value*(1/mass) for key, value in selected.items()}
    normalized_error = error/lo+_norm(selected)*error/(lo*mass)
    probability = max(Q(0), lo/h_hi), min(Q(1), hi/h_lo)
    return Posterior(result, encoding.record(), origin, rows, settings, herald, clicks,
                     probability, selected, normalized, mass, (lo, hi), normalized_error)


def verify(posterior, producer, first, second, admitted):
    if type(posterior) is not Posterior:
        raise ValueError('complete generated posterior required')
    encoding = posterior.raw_encoding
    raw = Encoding(tuple(encoding['click_tokens']), tuple(encoding['setting_zero_tokens']), tuple(encoding['herald_labels']))
    if raw.record() != encoding:
        raise ValueError('raw encoding scope changed')
    expected = condition(producer, posterior.source_interval, first, second, admitted, posterior.original_pair[1], encoding=raw)
    if posterior != expected:
        raise ValueError('posterior state, time law, normalizer or original record changed')
    return True


def time_restriction(posterior, producer, first, second, admitted, left, right, *, trial_families=None, taylor_order=8):
    verify(posterior, producer, first, second, admitted)
    result = producer.interval(left, right, trial_families=trial_families, taylor_order=taylor_order)
    selected, _ = _event_state(producer.source, result, posterior.physical_herald, posterior.physical_clicks)
    denominator = posterior.normalizer_center
    error = result.global_trace_norm_error
    lo = posterior.normalizer_bounds[0]
    mass_error = posterior.source_interval.global_trace_norm_error
    price = error/lo+_norm(selected)*mass_error/(lo*denominator)
    return {'source_interval': result, 'normalizer_interval': posterior.source_interval,
            'conditional_trap_state_center': {key: value*(1/denominator) for key, value in selected.items()},
            'conditional_trace_norm_error': price, 'original_rows': posterior.original_rows,
            'time_state_measure_preserved': True, 'normalization_depends_on_interval': False,
            'complete_record_clock_square_certified': False, 'actual_hardware_uniquely_identified': False}


def next_reload_input(posterior, producer, first, second, admitted, reload_source):
    verify(posterior, producer, first, second, admitted)
    from joint_reload_source import JointReloadSource
    if type(reload_source) is not JointReloadSource:
        raise ValueError('original closed joint reload source required')
    reload = JointReloadSource.from_record(reload_source.record())
    return {'state': reload.intake(posterior.normalized_trap_input),
            'upstream_trace_norm_error': posterior.posterior_trace_norm_error,
            'original_pair': posterior.original_pair, 'original_rows': posterior.original_rows,
            'source_posterior': posterior, 'raw_reload_source': reload.record(),
            'conditional_full_poststate_consumed': True, 'clock_as_quantum_time': False}
