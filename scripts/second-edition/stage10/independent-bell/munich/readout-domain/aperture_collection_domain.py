"""The quoted objective aperture bounds the original emitted q-mode transfer.

The normalized E1 radiation isometry is sqrt(3/(8*pi))*(I-n n*)d.
Restriction to a circular collection cone generates a Gram matrix before
any fibre, beam splitter or APD loss.  Every subsequent passive collection
map is bounded by this source Gram, including coherent q superpositions.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import atom_photon_source as photons
import bsm_retry_source as bsm
import common_optical_readout as common
import fluorescence_channel as channel


SCHEMA = 'stage10-quoted-objective-collection-domain/v1'
ZERO = dipole.ComplexRadical()
PUBLIC_SOURCE = {
    'url': 'https://xqp.physik.uni-muenchen.de/publications/files/theses_master/master_garthoff.pdf',
    'sha256': '8117baa61ccb7bfb26c2ce63ae6e5eaed1f7cbbae52a06300dacb21628a7438c',
    'year': 2015, 'printed_pages': [17, 18, 23],
    'objective': 'Mitutoyo G Plan Apo 50', 'numerical_aperture': '1/2',
    'objective_axis_defines_quantization_axis': True,
    'four_APD_model': 'Laser-Components Count-20C',
    'source_role': 'quoted optical design and topology; no independent efficiency confidence interval'}


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _bindings():
    paths = (Path(__file__), *(Path(module.__file__) for module in
              (dipole, full, photons, bsm, common, channel)))
    return {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def cone_gram(numerical_aperture):
    _check()
    aperture = full.exact(numerical_aperture)
    _require(0 <= aperture <= 1, 'one vacuum objective cone with NA in [0,1] required')
    cosine = dipole.sqrt_rational(1-aperture*aperture)
    cubed = cosine*(1-aperture*aperture)
    sigma = dipole.Radical(Q(1, 2))-Q(3, 8)*cosine-Q(1, 8)*cubed
    pi = dipole.Radical(Q(1, 2))-Q(3, 4)*cosine+Q(1, 4)*cubed
    _require(photons.radical_sign(sigma) >= 0 and photons.radical_sign(pi) >= 0 and
             photons.radical_sign(sigma-pi) >= 0, 'source angular restriction must be a positive contraction')
    return sigma, pi, sigma


def _psd(matrix):
    size = len(matrix)
    _require(all(len(row) == size for row in matrix), 'square source Gram required')
    _require(all(matrix[i][j] == matrix[j][i].conjugate() for i in range(size) for j in range(size)),
             'Hermitian source collection Gram required')
    residual = [list(row) for row in matrix]
    pivots = []
    for k in range(size):
        value = residual[k][k]
        sign = photons.radical_sign(value.real)
        _require(not value.imag and sign >= 0, 'collection exceeds its objective aperture Gram')
        pivots.append(value.serialize())
        if not sign:
            _require(not any(residual[k][j] for j in range(k+1, size)),
                     'zero aperture PSD pivot has a nonzero coherent row')
            continue
        inverse = photons.radical_inverse(value.real)
        for i in range(k+1, size):
            for j in range(k+1, size):
                residual[i][j] -= residual[i][k]*residual[k][j]*inverse
    return pivots


def _gram(matrix):
    return tuple(tuple(sum((row[i].conjugate()*row[j] for row in matrix), ZERO)
                       for j in range(len(matrix[0]))) for i in range(len(matrix[0])))


def _budget(aperture, aligned):
    values = cone_gram(aperture)
    # An unknown source-axis orientation retains the invariant largest
    # cone eigenvalue.  Aligned q coordinates retain the full anisotropy.
    return values if aligned else (values[0],)*3


def _prepared_member(domain, source):
    import prepared_retarded_source as prepared
    _require(prepared._guard is prepared._GUARD_FUNCTION and prepared._guard.__code__ is prepared._GUARD_CODE,
             'prepared source execution changed')
    prepared._GUARD_FUNCTION()
    _require(type(source) is prepared.PreparedRetardedSource,
             'closed source-issued PreparedRetardedSource required')
    geometry = ApertureCollectionDomain.record(domain)
    raw = prepared.PreparedRetardedSource.record(source)
    optical = geometry['common_optical_source']
    _require(raw['common_optical_owner_record'] == optical and raw['shared_optical_source'] == optical and
             raw['common_atomic_programme'] == optical['common_atomic_owner'],
             'objective domain and prepared history must have the same optical and atomic source')
    field = raw['field_kernel']
    collections = tuple(common._read_matrix(rows) for rows in field['raw_collection'])
    splitter = common._read_matrix(field['raw_splitter'])
    transfer = bsm.optical_transfer(*collections, splitter, tuple(map(Q, field['raw_efficiencies'])))
    _require(transfer == common._read_matrix(optical['generated_four_by_six_transfer']) and
             field['common_atomic_programme'] == raw['common_atomic_programme'] and
             raw['raw_shared_four_port_background_rates'] == optical['background_rates'],
             'source field, objective transfer, natural spectrum or BG changed')
    original = prepared.FieldOffPhotonKernel.signal_input_contraction(source._kernel)
    maxima = tuple(cone_gram(Q(aperture))[0] for aperture in geometry['numerical_apertures'])
    product = maxima[0]*maxima[1]
    centre, rounding = full.radical_midpoint(product, 160)
    bound = min(Q(1), max(Q(0), centre+rounding))
    contraction = {'original_gate_source_bound': original,
        'objective_leg_operator_norm_squares': [value.serialize() for value in maxima],
        'objective_two_leg_bound': product.serialize(),
        'objective_two_leg_bound_centre': str(centre), 'objective_two_leg_bound_rounding': str(rounding),
        'objective_two_leg_bound_upper': str(bound),
        'whole_four_pattern_input_contraction_upper': str(
            Q(original['whole_four_pattern_input_contraction_upper'])*bound),
        'operator_law': 'Gamma_2(T* T) <= Gamma_2(blockdiag(U_A identity, U_B identity)); on the one-signal-per-arm sector the latter is U_A U_B identity',
        'time_law': 'the passive optical map preserves the original photon time modes; both emissions must occur inside the whole original gate',
        'full_33_squared_and_number_coherent_inputs_covered': True,
        'BG_packet_multiplied_by_objective_bound': False}
    parameter = _copy(raw['parameter_domain'])
    parameter['objective_collection_domain'] = geometry
    return geometry, raw, contraction, parameter


class ApertureCollectionDomain:
    def __init__(self, source, *, numerical_apertures=(Q(1, 2), Q(1, 2)), axes_aligned=(False, False)):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('objective collection executed source changed')
        _CHECK()
        _require(type(source) is common.CommonOpticalReadout, 'closed common native/BSM optical source required')
        _require(type(numerical_apertures) is tuple and len(numerical_apertures) == 2 and
                 type(axes_aligned) is tuple and len(axes_aligned) == 2 and all(type(bit) is bool for bit in axes_aligned),
                 'two original side apertures and explicit axis charts required')
        for name in vars(source):
            _require(not callable(vars(source)[name]), 'common source operations cannot be instance callbacks')
        raw = common.CommonOpticalReadout.record(source)
        apertures = tuple(map(full.exact, numerical_apertures))
        budgets = tuple(_budget(aperture, aligned) for aperture, aligned in zip(apertures, axes_aligned))
        collections = tuple(common._read_matrix(raw[name]) for name in ('collection_a', 'collection_b'))
        checks = []
        for matrix, budget in zip(collections, budgets):
            gram = _gram(matrix)
            residue = tuple(tuple(dipole.ComplexRadical(budget[i] if i == j else 0)-gram[i][j]
                                   for j in range(3)) for i in range(3))
            checks.append({'collection_gram': common._matrix(gram), 'cone_remainder': common._matrix(residue),
                           'exact_PSD_pivots': _psd(residue)})
        transfer = common._read_matrix(raw['generated_four_by_six_transfer'])
        total = _gram(transfer)
        diagonal = tuple(value for budget in budgets for value in budget)
        remainder = tuple(tuple(dipole.ComplexRadical(diagonal[i] if i == j else 0)-total[i][j]
                                for j in range(6)) for i in range(6))
        self._record = {'schema': SCHEMA, 'common_optical_source': raw,
            'numerical_apertures': list(map(str, apertures)), 'axes_aligned': list(axes_aligned),
            'source_mode_order': [[side, q] for side in ('A', 'B') for q in dipole.Q_COMPONENTS],
            'cone_eigenvalues': [[value.serialize() for value in cone_gram(aperture)] for aperture in apertures],
            'collection_budgets': [[value.serialize() for value in budget] for budget in budgets],
            'side_collection_checks': checks, 'full_detected_transfer_gram': common._matrix(total),
            'full_detected_cone_remainder': common._matrix(remainder), 'full_detected_PSD_pivots': _psd(remainder),
            'source_law': 'C_s* C_s <= objective cone Gram; T* T <= blockdiag(cone_A,cone_B)',
            'normalization': 'full 4pi normalized E1 q radiation; source natural jump normalization is unchanged',
            'quoted_design_source': _copy(PUBLIC_SOURCE),
            'quoted_NA_half_design_applied': apertures == (Q(1, 2), Q(1, 2)),
            'all_shared_native_BSM_readouts_constrained': True,
            'pi_coupling_forced_to_zero': False, 'raw_aperture_is_an_independent_95pct_interval': False,
            'actual_optical_parameters_uniquely_identified': False,
            'new_confidence_budget_spent': False, 'source_bindings': _bindings(), 'controller_advance': False}
        self._source, self._seal = source, channel._canonical(self._record)

    def record(self):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('objective collection executed source changed')
        _CHECK()
        _require(type(self) is ApertureCollectionDomain and set(vars(self)) == {'_record', '_source', '_seal'} and
                 self._seal == channel._canonical(self._record) and self._record['source_bindings'] == _bindings() and
                 common.CommonOpticalReadout.record(self._source) == self._record['common_optical_source'],
                 'objective/source/axis or transfer domain changed')
        return _copy(self._record)

    def native_parameters(self, port_mask=common.ALL_PORTS):
        self.record()
        return common.CommonOpticalReadout._parameters(self._source, port_mask)

    @classmethod
    def from_record(cls, record):
        _require(cls is ApertureCollectionDomain and type(record) is dict and record.get('schema') == SCHEMA,
                 'closed original objective domain record required')
        result = cls(common.CommonOpticalReadout.from_record(record['common_optical_source']),
            numerical_apertures=tuple(map(Q, record['numerical_apertures'])),
            axes_aligned=tuple(record['axes_aligned']))
        _require(ApertureCollectionDomain.record(result) == record,
                 'objective source, aperture or coherent transfer budget changed')
        return result

    def admit_prepared(self, source):
        geometry, raw, contraction, parameter = _prepared_member(self, source)
        return {'schema': SCHEMA+'/prepared-admission', 'objective_collection_domain': geometry,
            'parameter_domain': parameter, 'source_support_word': _copy(raw['source_support_word']),
            'source_signal_input_contraction': contraction,
            'native_time_state_mother': _copy(raw['native_time_state_mother']),
            'full_retarded_receipt_time_mother': _copy(raw['full_retarded_receipt_time_mother']),
            'native_ready_relative_time_recipe': _copy(raw['native_ready_relative_time_recipe']),
            'source_scope': raw['native_inlet_kind'],
            'actual_hardware_uniquely_identified': False, 'new_confidence_budget_spent': False}

    def prepared_interval(self, source, left=None, right=None, *, bits=160):
        import prepared_retarded_source as prepared
        geometry, raw, contraction, parameter = _prepared_member(self, source)
        report = prepared.PreparedRetardedSource.interval(source, left, right, bits=bits)
        _require(report['source_preparation_record'] == raw,
                 'objective admission and receipt must restrict the same source occurrence')
        old = Q(report['old_whole_input_error_paid_once'])
        payment = old*Q(contraction['whole_four_pattern_input_contraction_upper'])
        signal_error = payment+Q(report['whole_local_scalar_error'])
        _require(old == Q(raw['upstream_trace_norm_error']), 'whole source input error must be consumed once')
        report['before_objective_global_trace_norm_error'] = report['global_trace_norm_error']
        report['before_objective_signal_input_error_payment'] = report['signal_input_error_payment']
        report['signal_input_error_payment'] = str(payment)
        report['source_objective_signal_contraction'] = contraction
        report['global_trace_norm_error'] = str(signal_error+Q(report['source_BG_scalar_error'])+
                                                Q(report['source_positive_BG_receipt_remainder_mass_upper']))
        survival = Q(report['source_BG_free_gate_probability_center'])
        survival_error = Q(report['source_BG_free_gate_probability_error'])
        # The numerical states already include p0.  Recover the original
        # signal centres solely from the source-produced scalar, never from
        # a caller normalizer or the positive BG packet.
        _require(survival > 0, 'finite source gate must have a positive no-BG centre')
        states = tuple({(i,j):channel._complex_record(value)*(1/survival) for i,j,value in row}
                       for row in report['four_pattern_poststates'])
        report['source_event_mass_lower'] = prepared._positive_packet_mass_lower(
            states, signal_error, survival, survival_error, bits)
        report['source_pattern_mass_lowers'] = [{'pattern': index, **prepared._positive_packet_mass_lower(
            (state,), signal_error, survival, survival_error, bits)} for index,state in enumerate(states)]
        report['parameter_domain'] = parameter
        report['objective_collection_domain'] = geometry
        report['schema'] = SCHEMA+'/prepared-first-receipt'
        return report

    def verify_prepared_interval(self, source, report):
        _require(type(report) is dict and report.get('schema') == SCHEMA+'/prepared-first-receipt',
                 'closed objective-constrained prepared receipt required')
        left,right = report['restriction_seconds']
        _require(ApertureCollectionDomain.prepared_interval(self, source, left, right, bits=report['scalar_bits']) == report,
                 'objective source, time restriction, whole input price or BG packet changed')
        return True


def _signature():
    functions = (_require, _copy, _bindings, cone_gram, _psd, _gram, _budget, _prepared_member, _signature, _check,
        ApertureCollectionDomain.__init__, ApertureCollectionDomain.record, ApertureCollectionDomain.native_parameters,
        ApertureCollectionDomain.from_record.__func__, ApertureCollectionDomain.admit_prepared,
        ApertureCollectionDomain.prepared_interval, ApertureCollectionDomain.verify_prepared_interval,
        common.CommonOpticalReadout.record, common.CommonOpticalReadout._parameters,
        common.CommonOpticalReadout.from_record.__func__, common._read_matrix, bsm.optical_transfer,
        full.radical_midpoint, photons.radical_sign, photons.radical_inverse)
    return tuple((id(function), id(function.__code__)) for function in functions)


def _check():
    if _signature is not _SIGNATURE or _signature.__code__ is not _SIGNATURE_CODE or _signature() != _EXPECTED:
        raise ValueError('objective collection executed source changed')


_SIGNATURE = _signature
_SIGNATURE_CODE = _signature.__code__
_CHECK = _check
_CHECK_CODE = _check.__code__
_EXPECTED = _signature()
