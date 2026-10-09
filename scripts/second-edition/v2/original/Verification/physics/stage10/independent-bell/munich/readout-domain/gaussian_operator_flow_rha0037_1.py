"""The same Gaussian source generates forward and reverse-right propagators.

For the reverse view W(u)=G(b,b-u)^T, W'=K(b-u)^T W and W(0)=I.
Transpose and clock reflection retain the original dissipative K identity.
No inverse flow, target operator or independent Hamiltonian enters the source.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import chebyshev_density_rha0032 as basis
import chebyshev_density_integer_rha0032_1 as arithmetic
import gaussian_atomic_pulse_source as gaussian

SCHEMA = 'stage10-source-Gaussian-two-time-operator-flow/rha0037.1'
DIRECTIONS = ('forward', 'reverse_right')
_ISSUED = {}


def require(value, reason):
    if not value: raise ValueError(reason)


def digest(value):
    return hashlib.sha256(gaussian.channel._canonical(value).encode()).hexdigest()


def _copy(value):
    return json.loads(gaussian.channel._canonical(value))


def transpose(matrix):
    return {(j, i): z for (i, j), z in matrix.items()}


def _parts_digest(parts):
    quiet, ek, drive, ev = parts
    return digest([[[i, j, str(a), str(b)] for (i, j), (a, b) in sorted(quiet.items())], str(ek),
                   [[i, j, str(a), str(b)] for (i, j), (a, b) in sorted(drive.items())], str(ev)])


def compiled_parts(raw, bits):
    quiet, ek, drive, ev, _ = gaussian._parts(raw, bits)
    h = gaussian._matrix(raw['complete_static_H_per_second'])
    d1 = [i for i, state in enumerate(gaussian.dipole.STATES) if state.family == 'D1']
    require(d1 and all((i in d1) == (j in d1) for i, j in h) and
            all(i not in d1 and j not in d1 for i, j in gaussian._matrix(raw['source_raising_operator_per_second'])),
            'the original D1 carrier must be a separate undriven source block')
    frequency = h.get((d1[0], d1[0]), gaussian.dipole.ComplexRadical()).real.as_rational()
    shifted = dict(quiet)
    for i in d1:
        a, b = shifted.get((i, i), (Q(0), Q(0))); shifted[i, i] = a, b+frequency
    rounded = gaussian.field._quantize(shifted, bits)
    # Remove the spectator optical carrier without removing its full33 block.
    ek += gaussian.field._difference(shifted, rounded)
    return (rounded, ek, drive, ev), frequency


class GaussianOperatorFlow:
    def __init__(self, pulse, start, stop, *, direction='forward', bits=192):
        require(type(pulse) is gaussian.GaussianAtomicPulseSource and direction in DIRECTIONS,
                'closed original Gaussian pulse and a registered direction required')
        raw = pulse.record(); a, b = map(Q, (start, stop)); gaussian._precision(bits)
        require(0 <= a < b and raw['duration_is_certification_horizon'] is True and
                raw['Gaussian_zero_at_endpoint_assumed'] is False and raw['hard_AOM_mask_installed'] is False,
                'positive interval of the original untruncated Gaussian field required')
        parts, d1_frequency = compiled_parts(raw, bits)
        quiet, eq, drive, ev = parts
        # Kbar differs from the physical K by an anti-Hermitian frame term.
        loss = gaussian._matrix(raw['complete_natural_R_per_second'])
        require(all(i == j and not z.imag and z.real.as_rational() >= 0 for (i, j), z in loss.items()),
                'the original complete natural R must be nonnegative diagonal')
        original_h = gaussian._matrix(raw['complete_static_H_per_second'])
        require(original_h == gaussian.dipole.matrix_adjoint(original_h), 'original complete H must be Hermitian')
        self._pulse, self._parts = pulse, (quiet, eq, drive, ev)
        self._view = _copy(raw)
        # This is a scalar view of g(t), not a new physical pulse source.
        self._view['centre_seconds'] = str(Q(raw['centre_seconds'])-a if direction == 'forward' else b-Q(raw['centre_seconds']))
        if direction == 'reverse_right':
            quiet, drive = transpose(quiet), transpose(drive)
        self._quiet, self._drive = quiet, drive
        self._value = {'schema': SCHEMA, 'original_Gaussian_source': raw,
            'source_interval_seconds': list(map(str, (a, b))), 'flow_interval_seconds': ['0', str(b-a)],
            'original_operator_certification_horizon_seconds': raw['duration_seconds'],
            'flow_interval_checked_by_its_own_full_residual': True, 'Gaussian_field_truncated': False,
            'direction': direction, 'coefficient_bits': bits,
            'D1_frame_frequency_per_second': str(d1_frequency),
            'D1_and_D2_optical_frames_retained_exactly': True,
            'source_clock': 'a+u' if direction == 'forward' else 'b-u',
            'candidate_coordinates': 'Gbar(a+u,a)' if direction == 'forward' else 'Gbar(b,b-u)^T',
            'source_scalar_centre_in_flow_coordinate': self._view['centre_seconds'],
            'source_K_view': 'original rotating K' if direction == 'forward' else 'transpose of the same rotating K',
            'original_H_R_and_Gaussian_preserved': True, 'non_Hermitian_operator_coefficients_allowed': True,
            'initial_operator_is_identity': True, 'inverse_propagator_used': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False}
        self._seal = digest(self._value); _ISSUED[id(self)] = pulse, self._seal, _parts_digest(self._parts)

    def record(self):
        require(type(self) is GaussianOperatorFlow and set(vars(self)) == {
                '_pulse', '_parts', '_view', '_quiet', '_drive', '_value', '_seal'} and
                _ISSUED.get(id(self)) == (self._pulse, self._seal, _parts_digest(self._parts)) and
                digest(self._value) == self._seal and self._pulse.record() == self._value['original_Gaussian_source'],
                'original Gaussian flow, source or direction changed')
        raw = self._value['original_Gaussian_source']; a, b = map(Q, self._value['source_interval_seconds'])
        expected_view = _copy(raw); expected_view['centre_seconds'] = str(
            Q(raw['centre_seconds'])-a if self._value['direction'] == 'forward' else b-Q(raw['centre_seconds']))
        quiet, _, drive, _ = self._parts
        if self._value['direction'] == 'reverse_right': quiet, drive = transpose(quiet), transpose(drive)
        require(self._view == expected_view and self._quiet == quiet and self._drive == drive,
                'source clock reflection or executed K columns changed')
        return _copy(self._value)

    def action(self, component, matrix):
        self.record(); require(component in ('quiet', 'drive'), 'original quiet or Gaussian drive component required')
        operator = self._quiet if component == 'quiet' else self._drive
        result = {}
        for (i, k), (a, b) in operator.items():
            for (j, l), (c, d) in matrix.items():
                if j == k:
                    old = result.get((i, l), (Q(0), Q(0)))
                    value = old[0]+a*c-b*d, old[1]+a*d+b*c
                    if value == (0, 0): result.pop((i, l), None)
                    else: result[i, l] = value
        return result


class IntegerColumns:
    def __init__(self, source):
        require(type(source) is GaussianOperatorFlow, 'closed full33 flow required')
        self.source, self.bits = source, source.record()['coefficient_bits']
        self.operators = {}
        for name, matrix in (('quiet', source._quiet), ('drive', source._drive)):
            rows = {}
            for (i, j), (a, b) in matrix.items():
                x, y = a*(1 << self.bits), b*(1 << self.bits)
                require(x.denominator == y.denominator == 1, 'same exact dyadic source parts required')
                rows.setdefault(j, []).append((i, x.numerator, y.numerator))
            self.operators[name] = rows

    def action(self, component, matrix):
        result = {}
        for (i, j), (a, b) in matrix.items():
            for k, c, d in self.operators[component].get(i, ()):
                r, s = result.get((k, j), (0, 0)); value = r+a*c-b*d, s+a*d+b*c
                if value == (0, 0): result.pop((k, j), None)
                else: result[k, j] = value
        return result


def piece(source, columns, value, current, elapsed, mode_bits, envelope_order=16):
    require(type(source) is GaussianOperatorFlow and type(columns) is IntegerColumns and columns.source is source,
            'the same full source flow and original columns required')
    source.record()
    require(type(value) is dict and set(value) == {'duration_seconds', 'chebyshev_coefficients'} and
            type(value['chebyshev_coefficients']) is list and 1 <= len(value['chebyshev_coefficients']) <= 65,
            'complete degree<=64 full33 operator piece required')
    width = Q(value['duration_seconds']); require(width > 0, 'positive original flow slice required')
    quantum = 1 << mode_bits
    matrices = [basis.density.fourier._coefficient(row, quantum) for row in value['chebyshev_coefficients']]
    integers = [{k: (int(a*quantum), int(b*quantum)) for k, (a, b) in m.items()} for m in matrices]
    scalar_bits = columns.bits; scalar_quantum = 1 << scalar_bits
    polynomial, tail = basis.gaussian_polynomial(source._view, elapsed, width, envelope_order, scalar_bits)
    scalars = []
    for coefficient in basis.monomial_to_chebyshev(polynomial):
        chosen = 0 if abs(coefficient) < Q(1, 1 << 96) else round(coefficient*scalar_quantum)
        tail += abs(coefficient-Q(chosen, scalar_quantum)); scalars.append(chosen)
    g_norm = Q(sum(map(abs, scalars)), scalar_quantum)
    scale = width.denominator*(1 << (columns.bits+mode_bits+scalar_bits+1))
    derivative_scale = width.denominator*(1 << (columns.bits+scalar_bits+1))
    quiet_scale = width.numerator*(1 << (scalar_bits+1)); residual = {}; input_norm = drive_norm = 0
    for n, matrix in enumerate(integers):
        input_norm += arithmetic.norm(matrix)
        for k, weight in basis.derivative_weights(n).items():
            arithmetic.add(residual.setdefault(k, {}), matrix, weight*derivative_scale)
        quiet = columns.action('quiet', matrix); drive = columns.action('drive', matrix)
        drive_norm += arithmetic.norm(drive); arithmetic.add(residual.setdefault(n, {}), quiet, -quiet_scale)
        for j, coefficient in enumerate(scalars):
            if coefficient:
                for k, weight in basis.product_weights(j, n).items():
                    twice = 2*weight; require(twice.denominator == 1, 'exact doubled Chebyshev product required')
                    arithmetic.add(residual.setdefault(k, {}), drive, -width.numerator*coefficient*twice.numerator)
    defect = Q(sum(arithmetic.norm(m) for m in residual.values()), scale)
    _, ek, _, ev = source._parts
    coefficient_price = width*(ek+(g_norm+tail)*ev)*Q(input_norm, quantum)
    gaussian_price = width*tail*Q(drive_norm, quantum*(1 << columns.bits))
    begin, end = basis.endpoint(matrices, False), basis.endpoint(matrices, True)
    join = basis.density.fourier._difference(begin, current)
    price = join+defect+coefficient_price+gaussian_price
    return width, end, price, {'flow_interval_seconds': list(map(str, (elapsed, elapsed+width))),
        'source_K_polynomial_defect': str(gaussian.field._price_upper(defect, columns.bits)),
        'source_K_coefficient_and_phase_price': str(gaussian.field._price_upper(coefficient_price, columns.bits)),
        'source_Gaussian_tail_price': str(gaussian.field._price_upper(gaussian_price, columns.bits)),
        'initial_join_price': str(gaussian.field._price_upper(join, columns.bits)),
        'whole_piece_operator_error': str(gaussian.field._price_upper(price, columns.bits)),
        'operator_Hermitian_projected': False, 'inverse_propagator_used': False,
        'complete_complex_coordinates': len(set().union(*(set(m) for m in matrices)))}
