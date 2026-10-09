"""Whole-future first-receipt coimages from one original forty-attempt block.

The occupation matrix and every native phase/gate curve are untrusted.
First-receipt rate integrals are distinct from gate-end success states.
Only their time integrals are approximated here; the mother and exact
shifted J K^n recipe retain the complete physical time measure.
"""
from fractions import Fraction as Q

import atomic_dipole as dipole
import atomic_modes as modes
import bsm_background_tail as background
import bsm_retry_source as bsm
import fluorescence_channel as channel
import joint_reload_resolvent as native
import projected_history_law as component
import projected_reload_continuation as continuation
import projected_window_cem as projected
import stopped_bsm_programme as stopped
import stopped_history_law as history


WITNESS_SCHEMA = 'stage10-native-BSM-block-occupation-witness/v1'
SCHEMA = 'stage10-native-BSM-whole-first-receipt-resolvent/v1'
DIRECT_SCHEMA = 'stage10-native-ready-whole-BSM-receipt-law/v1'


def posterior_encoding(record):
    import complete_history_posterior as complete
    import conditioned_window_history as observed
    import window_posterior_support as support
    channel._require(type(record) is dict, 'closed original posterior record required for encoding transport')
    if record.get('schema') == support.SCHEMA:
        channel._require(type(record.get('complete_parent_posterior')) is dict,
                         'closed SupportedHistoryPosterior must retain its complete parent')
        record = record['complete_parent_posterior']
    channel._require(record.get('schema') == complete.SCHEMA,
                     'encoding must come from the original closed CompleteHistoryPosterior')
    raw = record['raw_encoding']
    value = observed.Encoding(tuple(raw['click_tokens']), tuple(raw['setting_zero_tokens']), tuple(raw['herald_labels']))
    channel._require(value.record() == raw, 'complete original encoding identity required')
    return value.record()


def _encode_rows(rows, encoding):
    encoded = []
    for row in rows:
        item = dict(row)
        item['h'] = encoding['herald_labels'].index(component.HERALDS[row['h']])
        for side, setting_key, click_key in ((0, 'a', 'x'), (1, 'b', 'y')):
            item[setting_key] ^= int(encoding['setting_zero_tokens'][side] == '1')
            item[click_key] ^= int(encoding['click_tokens'][side] == '0')
        encoded.append(item)
    return sorted(encoded, key=lambda row: tuple(row[k] for k in ('h', 'a', 'b', 'x', 'y')))


def _source(value):
    channel._require(type(value) is stopped.StoppedBSMProgramme,
                     'closed original forty-attempt StoppedBSMProgramme required')
    return background._from_record('programme', stopped.StoppedBSMProgramme.record(value))


def contraction(raw_source):
    raw = _source(raw_source)
    bg = background.certify(raw)
    delta = Q(bg['background_success_lower'])
    # Keep the geometric power symbolic.  Even a fixed power forty can
    # produce huge decimal integers when a raw BG rate is extremely small.
    upper = 1/(1+bsm.BURST_CYCLES*delta)
    return {'background_source_certificate': bg,
            'one_block_geometric_pending_operator_upper': {'base': str(1-delta), 'exponent': bsm.BURST_CYCLES},
            'one_block_pending_operator_upper': str(upper),
            'one_block_absorption_lower': str(1-upper),
            'bound_rule': '(1-delta)^40 <= 1/(1+40*delta)',
            'strict_contraction_produced': delta > 0}


def herald_support(raw_source):
    """Strict first-gate support on every positive normalized source input."""
    raw = _source(raw_source)
    gate, atom_laws = raw.gate, []
    R = Q(0)
    for atom in gate.source.sources:
        channel._require(not any(atom.program.ion_rates.values()), 'BSM herald support uses the original vacancy-preserving natural baths')
        loss = {}
        for jump in atom.jumps:
            product = dipole.matrix_product(dipole.matrix_adjoint(jump.matrix), jump.matrix)
            native._add(loss, product, atom.program.gammas[jump.label[:2]])
        expected = {(i, i): dipole.ComplexRadical(rate) for i, rate in enumerate(atom.outgoing) if rate}
        channel._require(loss == expected, 'six-mode natural source Kraus loss does not equal original outgoing rates')
        R += max(atom.outgoing)
        atom_laws.append({'natural_Kraus_loss': channel._input_record(loss),
                          'max_outgoing': str(max(atom.outgoing))})
    # The passive complement supplies I-T*T >= 0 in each environment group.
    # Tensoring the six local raw modes then gives C_detected <= Omega_A+Omega_B,
    # including coherent cross-side APD terms, so no factor two is introduced.
    quantum = background._quantum_law(gate)
    patterns = []
    for index, (herald, ports) in enumerate(bsm.PATTERNS):
        mark = gate.target(gate.target(bsm.INITIAL, ports[0]), ports[1])
        channel._require(mark.receipt == index, 'the isolated raw BG pair must generate its original first herald')
        x, y = (gate.background_rates[p]*gate.duration for p in ports)
        pair = x/(1+x)*y/(1+y)
        other = sum((rate for p, rate in enumerate(gate.background_rates) if p not in ports), Q(0))
        argument = (R+other)*gate.duration
        lower, scalar, radius, precision = Q(0), None, None, None
        if pair:
            for bits in (256, 512, 1024):
                value, error = modes.complex_exponential(-argument, 0, bits=bits)
                lower = max(Q(0), value[0]-error)
                scalar, radius, precision = value[0], error, bits
                if lower:
                    break
        patterns.append({'pattern_index': index, 'herald': herald, 'ports': list(ports),
                         'raw_pair_BG_path_lower': str(pair), 'no_APD_and_other_BG_exponent': str(argument),
                         'strict_exponential_center': None if scalar is None else str(scalar),
                         'strict_exponential_error': None if radius is None else str(radius),
                         'exponential_bits': precision, 'first_herald_operator_lower': str(pair*lower)})
    groups = []
    for herald in component.HERALDS:
        selected = max((p for p in patterns if p['herald'] == herald),
                       key=lambda p: Q(p['first_herald_operator_lower']))
        groups.append({'herald': herald, 'pattern_index': selected['pattern_index'],
                       'first_gate_normalized_input_mass_lower': selected['first_herald_operator_lower']})
    return {'raw_source': raw.record(), 'atomic_loss_identities': atom_laws,
            'observed_Gram_completeness_and_passive_complement': quantum,
            'optical_APD_total_rate_upper': str(R), 'patterns': patterns, 'heralds': groups,
            'proof': 'no optical APD path trace >= exp(-R*T); isolated independent BG pair, no other BG, generates its unique first herald',
            'coherent_APD_rate_bound': 'T*T<=I in every raw environment group; sum six raw-mode losses is Omega_A+Omega_B<=R*I',
            'normalized_input_required': True, 'normalizer_supplied_by_caller': False}


def _curve_price(certificate, gate):
    rate = sum(max(atom.outgoing) for atom in gate.source.sources)+sum(gate.background_rates)
    price, integrated = Q(certificate['initial_radical_error']), Q(0)
    for piece, paid in zip(certificate['trial_pieces'], certificate['piece_error_records']):
        price += sum((Q(paid[key]) for key in ('initial_join_error', 'source_residual_error',
                          'radical_coefficient_error', 'scalar_exponential_error')), Q(0))
        integrated += rate*Q(piece['duration'])*price
    return integrated


def _joint_price(raw, run):
    phases = iter(run.phase_certificates)
    def group(values):
        price = Q(0)
        for phase in values:
            if phase.duration:
                price = Q(next(phases)['trace_norm_error_bound'])
        return price
    rows, joint_price, extra_returns, terminal = [], Q(0), Q(0), Q(0)
    for index, certificate in enumerate(run.gate_certificates):
        cycle = index+1
        pre = group(raw.preparation+raw.excitation+raw.arrival_delay)
        success_returns = sum((group(raw.return_phases) for _ in bsm.PATTERNS), Q(0))
        failed = group(raw.return_phases+(raw.recooling if cycle == bsm.BURST_CYCLES else ()))
        gate = Q(certificate['trace_norm_error_bound'])
        curve = _curve_price(certificate, raw.gate)
        joint_price += pre+gate+curve+failed
        terminal += pre+gate+success_returns+failed
        extra_returns += success_returns
        rows.append({'cycle': cycle, 'preparation_excitation_arrival_price': str(pre),
                     'whole_gate_endpoint_price': str(gate), 'whole_first_receipt_curve_price': str(curve),
                     'failure_return_and_recooling_price': str(failed),
                     'unused_gate_end_success_return_price': str(success_returns),
                     'fortieth_failure_recooling_consumed': cycle == bsm.BURST_CYCLES})
    channel._require(next(phases, None) is None, 'all and only original block phase prices required')
    result = run.programme_result
    channel._require(terminal == result.global_terminal_error and
                     joint_price+extra_returns == result.global_time_error,
                     'the native whole time/terminal induction prices do not match their source operation groups')
    return {'cycle_prices': rows, 'whole_receipt_plus_failure_price': str(joint_price),
            'native_global_time_price': str(result.global_time_error),
            'native_global_terminal_price': str(result.global_terminal_error),
            'extra_gate_end_success_return_price': str(extra_returns),
            'joint_price_proof': 'pending pre-CP map; first-receipt time instrument plus failure; pending return/40th recool. Existing prefix error contracts once.',
            'gate_joint_price': 'gate endpoint price covers failure; integral B*curve_error covers the whole four-pattern first-receipt time measure; add these new prices',
            'individual_receipt_inherited_errors_summed': False,
            'gate_end_success_states_substituted_for_receipt_states': False}


def certify(raw_source, initial, witness, *, upstream_error=0):
    raw = _source(raw_source)
    rho = channel._initial(initial, projected.reload.DIMENSION)
    channel._require(type(witness) is dict and set(witness) ==
                     {'schema', 'occupation_matrix', 'phase_certificates', 'gate_certificates', 'multitone_bits'} and
                     witness['schema'] == WITNESS_SCHEMA,
                     'raw occupation matrix and complete source curves only; target receipts are not input')
    channel._require(type(witness['gate_certificates']) is list and len(witness['gate_certificates']) == bsm.BURST_CYCLES,
                     'exactly the original forty gates, including fortieth-failure recooling, required')
    occupation = channel._read_input(witness['occupation_matrix'], projected.reload.DIMENSION)
    source_bound = contraction(raw)
    bg = source_bound['background_source_certificate']
    delta = Q(bg['background_success_lower'])
    channel._require(delta > 0, 'no positive supported raw BG pair; preserve the original BSM tail')
    pending_upper = Q(source_bound['one_block_pending_operator_upper'])
    block_delta = 1-pending_upper
    ingress = {'raw_burst': raw.record(), 'multitone_bits': witness['multitone_bits'],
               'phase_certificates': witness['phase_certificates'], 'gate_certificates': witness['gate_certificates'],
               'parent_input_identity': {'raw_source': raw.record(), 'untrusted_occupation_matrix': witness['occupation_matrix']},
               'parent_journal': []}
    # Zero is a local block coordinate, never a mother receipt timestamp.
    run = projected._replay_bsm_ingress(ingress, occupation, 0, 0)
    result = run.programme_result
    audit = _joint_price(raw, run)
    flux = tuple({} for _ in bsm.PATTERNS)
    for snapshot in result.stops:
        native._add(flux[snapshot.pattern_index], snapshot.poststate_at_receipt)
    residual = dict(rho)
    native._add(residual, result.remaining_pair)
    native._add(residual, occupation, -1)
    norm = native._entry_norm_upper(residual, 160)
    joint_error = Q(audit['whole_receipt_plus_failure_price'])
    inherited = channel.full.nonnegative(upstream_error)
    numerical = norm+joint_error
    return projected._copy({'schema': SCHEMA, 'raw_source': raw.record(),
            'initial_matrix': channel._input_record(rho), 'untrusted_occupation_witness': witness,
            'background_source_certificate': bg,
            'one_block_geometric_pending_operator_upper': source_bound['one_block_geometric_pending_operator_upper'],
            'one_block_pending_operator_upper': str(pending_upper), 'one_block_absorption_lower': str(block_delta),
            'inverse_trace_norm_upper': str(1/block_delta), 'joint_price_audit': audit,
            'generated_pending_KX': channel._input_record(result.remaining_pair),
            'generated_receipt_JX': [channel._input_record(matrix) for matrix in flux],
            'residual_matrix': channel._input_record(residual), 'residual_entry_norm_upper': str(norm),
            'whole_joint_receipt_and_failure_error': str(joint_error),
            'upstream_trace_norm_error': str(inherited), 'new_whole_receipt_error': str(numerical),
            'whole_receipt_trace_norm_error': str(inherited+numerical),
            'occupation_trace_norm_error': str((inherited+numerical)/block_delta),
            'error_rule': 'old whole E + residual norm + new joint time-receipt/failure price; F=J(I-K)^-1 is CPTP',
            'fixed_block_duration': str(result.remaining_time),
            'one_block_receipt_supports': [list(map(str, law.support)) for law in result.first_receipt_laws],
            'full_relative_time_measure_recipe': {
                'raw_block': raw.record(), 'block_duration': str(result.remaining_time),
                'measure': 'sum_n shifted first-receipt J K^n on the original input time/state measure',
                'Laplace_recipe': 'J(z)*(I-exp(-z*block_duration)*K)^-1',
                'one_block_supports': [list(map(str, law.support)) for law in result.first_receipt_laws],
                'fortieth_failure_recooling_retained': True},
            'receipt_matrices_are_time_integrated': True, 'time_resolved_numerical_measure_certified': False,
            'folded_occupation_supports_are_actual_receipt_times': False,
            'all_four_patterns_and_forty_attempts_consumed': True,
            'numerical_centres_assumed_CP': False, 'solver_reexecuted_by_checker': False,
            'target_receipt_matrix_supplied': False, 'actual_scalar_clock_created': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False})


def verify_certificate(report, raw_source=None, initial=None, *, upstream_error=None):
    channel._require(type(report) is dict and report.get('schema') == SCHEMA,
                     'whole native BSM first-receipt resolvent certificate required')
    source = background._from_record('programme', report['raw_source']) if raw_source is None else _source(raw_source)
    rho = channel._read_input(report['initial_matrix'], projected.reload.DIMENSION) if initial is None else channel._initial(initial, projected.reload.DIMENSION)
    channel._require(source.record() == report['raw_source'] and channel._input_record(rho) == report['initial_matrix'],
                     'same raw burst and complete source input required')
    error = report['upstream_trace_norm_error'] if upstream_error is None else upstream_error
    channel._require(Q(error) == Q(report['upstream_trace_norm_error']), 'same whole mother error required')
    expected = certify(source, rho, report['untrusted_occupation_witness'], upstream_error=error)
    channel._require(expected == report, 'native BSM residual, receipt coimage, joint price or clock recipe changed')
    return True


def from_ready_absorption(parent, ready_report, witness):
    channel._require(type(parent) is continuation.ProjectedReloadContinuation,
                     'closed same-posterior native reload mother required')
    native.verify_absorption(ready_report, parent)
    parent_record = continuation.ProjectedReloadContinuation.record(parent)
    original = parent.posterior.source
    raw_record = original.component.mother.burst_ingress['raw_burst']
    raw = projected._burst(raw_record, witness['multitone_bits'])
    hardware = original.hardware_record()
    hardware_burst = projected._copy(raw.record())
    for field in ('gate_start', 'gate_end', 'interval_start'):
        hardware_burst['gate'].pop(field)
    channel._require(hardware_burst == hardware['raw_burst_hardware'] and raw.gate.seconds_per_unit == parent.seconds_per_unit,
                     'whole reload/BSM action must keep the original raw hardware and same source unit')
    rho = channel._read_input(ready_report['complete_future_ready_matrix'], projected.reload.DIMENSION)
    proof = certify(raw, rho, witness, upstream_error=ready_report['global_trace_norm_error'])
    return projected._copy({'schema': DIRECT_SCHEMA, 'source_record': parent_record,
            'same_parent_ready_absorption': ready_report, 'source_resolvent': proof,
            'complete_future_receipt_matrices': proof['generated_receipt_JX'],
            'global_trace_norm_error': proof['whole_receipt_trace_norm_error'],
            'old_whole_error_paid_once': proof['upstream_trace_norm_error'],
            'new_whole_receipt_error': proof['new_whole_receipt_error'],
            'original_shared_hardware': hardware,
            'time_state_mother_record': ready_report['time_state_mother_record'],
            'complete_relative_time_measure_recipe': {
                'mother_ready_measure': ready_report['complete_relative_time_measure_recipe'],
                'BSM_first_receipt_measure': proof['full_relative_time_measure_recipe'],
                'composition': 'apply shifted original BSM J K^n to every original full native Ready time restriction'},
            'both_native_reload_and_BSM_pending_absorbed': True,
            'whole_source_error_paid_once': True, 'receipt_matrices_are_time_integrated': True,
            'time_resolved_numerical_measure_certified': False, 'actual_scalar_clock_created': False,
            'literal_cohort_reconstructed': False, 'actual_hardware_uniquely_identified': False,
            'controller_advance': False})


def verify_from_ready(report, parent=None):
    channel._require(type(report) is dict and report.get('schema') == DIRECT_SCHEMA,
                     'same-mother whole BSM receipt certificate required')
    mother = continuation.ProjectedReloadContinuation.from_record(report['source_record']) if parent is None else parent
    proof, ready = report['source_resolvent'], report['same_parent_ready_absorption']
    channel._require(report['source_record'] == continuation.ProjectedReloadContinuation.record(mother) and
                     report['complete_future_receipt_matrices'] == proof['generated_receipt_JX'] and
                     report['global_trace_norm_error'] == proof['whole_receipt_trace_norm_error'] and
                     report['time_state_mother_record'] == ready['time_state_mother_record'],
                     'same Ready mother, complete receipt coimage or shared error changed')
    expected = from_ready_absorption(mother, report['same_parent_ready_absorption'],
                                    report['source_resolvent']['untrusted_occupation_witness'])
    channel._require(expected == report, 'same Ready mother, complete receipt coimage or shared error changed')
    return True


def cem_setting_responses(parent, receipt_report, *, trial_provider=None, taylor_order=6,
                          mode_bits=60, coefficient_bits=160, exponential_bits=160):
    """The original four command CP maps consume this same complete new mu."""
    verify_from_ready(receipt_report, parent)
    source = parent.posterior.source
    measure = {'poststates': tuple(channel._read_input(matrix, projected.reload.DIMENSION)
                                  for matrix in receipt_report['complete_future_receipt_matrices']),
               'global_trace_norm_error': Q(receipt_report['global_trace_norm_error'])}
    reports = [history.StoppedHistoryLaw._window(source, settings, measure,
                trial_provider=trial_provider, taylor_order=taylor_order,
                mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
                for settings in component.SETTINGS]
    raw = projected._burst(receipt_report['source_resolvent']['raw_source'],
                           receipt_report['source_resolvent']['untrusted_occupation_witness']['multitone_bits'])
    support = herald_support(raw)
    normalizers = []
    for herald in component.HERALDS:
        matrix = component._sum(m for index, m in enumerate(measure['poststates']) if bsm.PATTERNS[index][0] == herald)
        mass, radical = projected._trace(matrix)
        error = measure['global_trace_norm_error']+radical
        generated = next(item for item in support['heralds'] if item['herald'] == herald)
        source_lower = Q(generated['first_gate_normalized_input_mass_lower'])
        low, high = max(source_lower, mass-error), min(Q(1), mass+error)
        channel._require(0 < low <= high, 'raw source has not produced a positive complete-herald normalizer')
        normalizers.append({'herald': herald, 'center': str(mass), 'error': str(error),
                            'source_first_gate_lower': str(source_lower), 'lower': str(low), 'upper': str(high),
                            'positive_lower_certified': True,
                            'true_ready_trace_one_source': 'verified normalized positive CompleteHistoryPosterior followed by complete native CPTP absorption'})
    rows, payments = [], []
    for settings, report in zip(component.SETTINGS, reports):
        payment = component._price(source.component.measurement.compile(settings), measure)
        payments.append(str(payment))
        event_error = measure['global_trace_norm_error']+Q(report['window_local_error'])+payment
        for h, normalizer in enumerate(normalizers):
            for clicks in projected.window.REGISTRATION_ORDER:
                matrix = component._selected(report, normalizer['herald'], clicks)
                mass, radical = projected._trace(matrix)
                low = max(Q(0), (mass-event_error-radical)/Q(normalizer['upper']))
                high = min(Q(1), (mass+event_error+radical)/Q(normalizer['lower']))
                channel._require(low <= high, 'whole source CEM probability enclosure is empty')
                rows.append({'h': h, 'a': settings[0], 'b': settings[1], 'x': clicks[0], 'y': clicks[1],
                             'probability_interval': list(map(str, (low, high))),
                             'event_center': str(mass), 'event_error': str(event_error+radical)})
    rows.sort(key=lambda row: tuple(row[k] for k in ('h', 'a', 'b', 'x', 'y')))
    table = component.ProjectedHistoryLaw._table(rows)
    encoding = posterior_encoding(receipt_report['source_record']['original_posterior'])
    encoded = _encode_rows(rows, encoding)
    return projected._copy({'schema': 'stage10-whole-BSM-four-command-CEM-responses/v1',
            'same_parent_whole_receipt_report': receipt_report, 'setting_reports': reports,
            'source_herald_support': support, 'source_probability_enclosures': rows,
            'command_substitution_payments': payments,
            'herald_normalizers': normalizers, 'complete_contexts': len(table),
            'precision': [mode_bits, coefficient_bits, exponential_bits],
            'raw_encoding': encoding, 'raw_probability_enclosures': encoded,
            'all_four_commands_and_outcomes_generated': True,
            'receipt_measure_is_entire_future': True, 'positive_unknown_BSM_tail_upper': '0',
            'source_normalizer_supplied_by_caller': False,
            'conditional_probability_assembly_ready': all(item['positive_lower_certified'] for item in normalizers),
            'actual_hardware_uniquely_identified': False, 'controller_advance': False})


def verify_cem_responses(report, parent=None):
    channel._require(type(report) is dict and report.get('schema') == 'stage10-whole-BSM-four-command-CEM-responses/v1',
                     'whole first-receipt four-command CEM certificate required')
    receipt = report['same_parent_whole_receipt_report']
    mother = continuation.ProjectedReloadContinuation.from_record(receipt['source_record']) if parent is None else parent
    saved = {}
    for item in report['setting_reports']:
        settings = tuple(item['settings'])
        for packet in item['packets']:
            key = settings, packet['pattern_index'], tuple(packet['entering_occupancy'])
            channel._require(key not in saved, 'all original command/pattern/occupancy packets exactly once required')
            saved[key] = packet
    def trials(settings, pattern, mask, phase, matrix):
        return saved[settings, pattern, mask]['phase_certificates'][phase]['trial_pieces']
    bits = report['precision']
    expected = cem_setting_responses(mother, receipt, trial_provider=trials,
                mode_bits=bits[0], coefficient_bits=bits[1], exponential_bits=bits[2])
    channel._require(expected == report, 'whole source CEM probabilities, positive normalizer or hardware changed')
    return True
