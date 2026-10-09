"""Source-generated whole-future BSM tail bound from independent background clocks.

The four raw background channels have quantum leg r_p*identity and the same
native Mark target as photons.  For a supported pair, one event of each clock
forces a latched receipt.  Extra photons cannot remove it.  The universal
failure effect is therefore bounded by (1-delta)I, independently of the atom
state.  Only exact raw sources enter; no stopping probability or effect does.
"""
from fractions import Fraction as Q
from itertools import product
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import atom_photon_source as optics
import bsm_retry_source as bsm
import joint_fluorescence_presence as joint
import optical_multitone as optical
import stopped_bsm_programme as programme


SCHEMA = "stage10-raw-BSM-background-whole-future-tail/v1"


def _require(condition, reason):
    if not condition:
        raise ValueError(reason)


def _complex(value):
    return dipole.ComplexRadical(*(dipole.Radical({int(root): full.exact(coefficient)
                                                 for root, coefficient in value[part].items()})
                                  for part in ("real", "imag")))


def _phase(record):
    _require(type(record) is dict and set(record) == {"raw_segments", "model_trace_norm_error", "origin"},
             "closed raw pair-phase record required")
    _require(type(record["raw_segments"]) is list and len(record["raw_segments"]) == 2,
             "two complete raw phase Segments required")
    result = programme.RawPairPhase(*(full.Segment.from_record(item) for item in record["raw_segments"]))
    price = full.nonnegative(record["model_trace_norm_error"])
    origin = record["origin"]
    if origin is None:
        _require(price == 0, "plain raw phase cannot import a model-error certificate")
    else:
        _require(type(origin) is dict and set(origin) == {"multitone_programmes", "source_cells"} and
                 len(origin["multitone_programmes"]) == len(origin["source_cells"]) == 2,
                 "source-owned multitone phase origin required")
        for raw, cell, segment in zip(origin["multitone_programmes"], origin["source_cells"], (result.first, result.second)):
            tones = [optical.Tone(item["name"], item["line"], item["angular_frequency_in_common_reciprocal_time_unit"],
                                 {int(q): _complex(value) for q, value in item["field_at_local_time_zero"].items()})
                     for item in raw["tones"]]
            source = optical.Programme(full.Segment.from_record(raw["base"]), tones)
            _require(source.record() == raw and cell["raw_segment"] == segment.record(), "multitone raw-source phase mismatch")
            start, end = full.exact(cell["start"]), full.exact(cell["end"])
            _require(0 <= start < end <= source.base.duration and end-start == result.duration,
                     "multitone cell changes the source duration")
            base, actual = source.base.record(), segment.record()
            for item in (base, actual):
                for name in ("duration", "fields_r", "fields_c"):
                    item.pop(name)
            _require(base == actual, "multitone cell changes the source bath or static atomic law")
        _require(price == sum((full.nonnegative(cell["cptp_duhamel_trace_norm_error"]) for cell in origin["source_cells"]), Q(0)),
                 "multitone phase price differs from its source cells")
        object.__setattr__(result, "model_error", price)
        object.__setattr__(result, "origin", json.loads(json.dumps(origin)))
    _require(result.record() == record, "noncanonical raw pair-phase record")
    return result


def _from_record(kind, record):
    if kind == "gate":
        return bsm.BSMSource.from_record(record)
    _require(kind == "programme" and type(record) is dict and record.get("schema") == "rb87-source-stopped-bsm-programme/v1",
             "closed raw stopped-BSM programme record required")
    source = programme.StoppedBSMProgramme(*(
        tuple(_phase(item) for item in record[name]) for name in ("preparation", "excitation")),
        bsm.BSMSource.from_record(record["gate"]),
        *(tuple(_phase(item) for item in record[name]) for name in ("return_phases", "recooling_phases")),
        arrival_delay_phases=tuple(_phase(item) for item in record["arrival_delay_phases"]),
        control_policy=record["return_endpoint_policy"])
    _require(source.record() == record, "raw stopped programme clock or source scope mismatch")
    return source


def _source(value):
    if type(value) is bsm.BSMSource:
        return "gate", _from_record("gate", value.record())
    _require(type(value) is programme.StoppedBSMProgramme,
             "closed raw BSMSource or StoppedBSMProgramme required; a port tuple or target effect is not a source")
    return "programme", _from_record("programme", value.record())


def _mark_record(mark):
    return {"counts": list(mark.counts), "receipt": mark.receipt}


def _mark_law(gate):
    marks = []
    for counts in product((0, 1, 2), repeat=4):
        for receipt in (None, 0, 1, 2, 3):
            try:
                marks.append(bsm.Mark(counts, receipt))
            except ValueError:
                continue
    positions = {mark: index for index, mark in enumerate(marks)}
    rows, pair_paths = [], []
    for index, mark in enumerate(marks):
        for port in range(4):
            target = gate.target(mark, port)
            counts = tuple(min(value+int(i == port), 2) for i, value in enumerate(mark.counts))
            receipt = mark.receipt
            if receipt is None:
                for pattern in gate.pattern_priority:
                    left, right = bsm.PATTERNS[pattern][1]
                    if counts[left] and counts[right]:
                        receipt = pattern
                        break
            _require(target == bsm.Mark(counts, receipt) and all(a <= b for a, b in zip(mark.counts, target.counts)),
                     "native BSM target is not monotone in all retained source marks")
            _require(mark.receipt is None or target.receipt == mark.receipt, "native photons or background erase a first receipt")
            rows.append([index, port, positions[target]])
        for pattern, (_, ports) in enumerate(bsm.PATTERNS):
            _require(len(ports) == 2 and ports[0] != ports[1] and all(type(port) is int and 0 <= port < 4 for port in ports),
                     "original supported physical APD pair required")
            for order in (ports, ports[::-1]):
                target = gate.target(gate.target(mark, order[0]), order[1])
                _require(target.receipt is not None, "a supported pair of background events need not stop the source")
                pair_paths.append([index, pattern, list(order), positions[target]])
    return {"marks": [_mark_record(mark) for mark in marks], "targets": rows,
            "supported_pair_paths": pair_paths, "legal_marks": len(marks), "target_edges": len(rows),
            "receipt_event": "any original latched pattern; its first pattern identity is retained"}


def _schur(matrix):
    values, pivots = [list(row) for row in matrix], []
    for pivot in range(len(values)):
        value = values[pivot][pivot]
        sign = optics.radical_sign(value.real)
        _require(not value.imag and sign >= 0, "passive optical complement is not positive")
        pivots.append({"index": pivot, "pivot": value.serialize(), "sign": sign})
        if sign == 0:
            _require(not any(values[pivot][i] for i in range(pivot+1, len(values))), "zero PSD pivot has a nonzero source row")
        else:
            inverse = optics.radical_inverse(value.real)
            for i in range(pivot+1, len(values)):
                for j in range(pivot+1, len(values)):
                    values[i][j] -= values[i][pivot]*values[pivot][j]*inverse
    return pivots


def _atomic_law(atom):
    _require(dipole.matrix_adjoint(atom.hamiltonian) == atom.hamiltonian, "raw atomic Hamiltonian is not Hermitian")
    feed = {}
    for (a, b, i, j), value in atom.recycling.items():
        if a == b:
            bsm.local._add(feed, (i, j), value)
    expected = {(i, i): dipole.ComplexRadical(rate) for i, rate in enumerate(atom.outgoing) if rate}
    _require(feed == expected, "full-complex atomic loss/recycling trace identity failed")
    _require(all(value >= 0 for value in atom.program.gammas.values()) and
             all(value >= 0 for value in atom.program.ion_rates.values()), "raw atomic jump has a negative rate")
    return {"hamiltonian_nonzero_coordinates": len(atom.hamiltonian),
            "trace_identity_coordinates": full.COMPLEX_COORDINATES,
            "outgoing_rates": list(map(str, atom.outgoing)),
            "recycled_trace_coefficients": [[i, j, value.serialize()] for (i, j), value in sorted(feed.items())]}


def _quantum_law(gate):
    transfer = bsm.optical_transfer(*gate.collections, gate.splitter, gate.efficiencies)
    transfer, gram, complement = joint.passive_transfer(transfer)
    _require(all(gram[i][j]+complement[i][j] == dipole.ComplexRadical(int(i == j))
                 for i in range(6) for j in range(6)), "observed/unobserved source Gram completeness failed")
    pivots = _schur(complement)
    _require(all(value == complement for value in gate.source.undetected_grams.values()),
             "original environment groups do not share the source passive complement")
    atoms = [_atomic_law(atom) for atom in gate.source.sources]
    # Rebuild the zero-background source, rather than trusting a caller's G.
    record = gate.record(); record["background_rates"] = ["0"]*4
    without_background = bsm.BSMSource.from_record(record)
    dimension = joint.DIMENSION
    matrix = {(0, dimension-1): dipole.ComplexRadical(Q(2, 7), Q(3, 5)),
              (dimension-1, 0): dipole.ComplexRadical(Q(2, 7), Q(-3, 5)),
              (33*8+17, 33*8+17): dipole.ComplexRadical(Q(1, 3)),
              (33*31+4, 33*9+30): dipole.ComplexRadical(Q(-1, 11), Q(5, 13))}
    for port, rate in enumerate(gate.background_rates):
        actual = gate.port_action(matrix, port)
        optical_part = without_background.port_action(matrix, port)
        for key, value in optical_part.items():
            bsm.local._add(actual, key, -value)
        expected = {key: rate*value for key, value in matrix.items() if rate*value}
        _require(actual == expected, "native background operation differs from its scalar quantum identity leg")
    return {"full_pair_dimension": dimension, "atomic_sources": atoms,
            "passive_complement": [[value.serialize() for value in row] for row in complement],
            "passive_schur_pivots": pivots, "environment_groups": len(gate.source.undetected_grams),
            "background_quantum_legs": [{"port": port, "raw_rate": str(rate), "operator": "identity on full33 tensor full33"}
                                        for port, rate in enumerate(gate.background_rates)],
            "clock_generator": "sum_p r_p*(native Mark target_p - identity); independent Poisson drivers",
            "quantum_mark_form": "passive observed/unobserved GKSL split; deterministic trace-preserving classical targets",
            "native_full_complex_background_probe_coordinates": len(matrix)}


def _phase_laws(source, kind):
    if kind == "gate":
        return []
    records, cache = [], {}
    for name, phases in (("preparation", source.preparation), ("excitation", source.excitation),
                         ("arrival_delay", source.arrival_delay), ("return", source.return_phases), ("recooling", source.recooling)):
        for index, phase in enumerate(phases):
            native = joint.JointCounterGenerator(phase.first, phase.second, threshold=1, background_rate=0,
                                                 collection=((0, 0, 0, 0, 0, 0),))
            atoms = []
            for atom in native.sources:
                key = json.dumps(atom.program.record(), sort_keys=True, separators=(",", ":"))
                if key not in cache:
                    cache[key] = _atomic_law(atom)
                atoms.append(cache[key])
            records.append({"phase": name, "index": index, "duration": str(phase.duration), "atoms": atoms,
                            "continuation_trace_factor": "1", "approximation_price_needed_for_uniform_tail": False,
                            "multitone_Hermitian_source": phase.origin is not None})
    return records


def _power(base, exponent):
    return {"base": str(base), "exponent": exponent}


def certify(raw_source, *, background_seconds_per_unit=None):
    kind, source = _source(raw_source)
    gate = source if kind == "gate" else source.gate
    _require(gate.interval_start == gate.gate_start and
             gate.duration == gate.gate_end-gate.gate_start and gate.duration*gate.seconds_per_unit == bsm.GATE_SECONDS,
             "complete original 120 ns arrival gate required; a half gate has a different stopping contract")
    unit = gate.seconds_per_unit if background_seconds_per_unit is None else bsm._positive(background_seconds_per_unit)
    _require(unit == gate.seconds_per_unit, "background rates must use the same raw source clock unit")
    mark_law, quantum_law = _mark_law(gate), _quantum_law(gate)
    phase_laws = _phase_laws(source, kind)
    pair_bounds = []
    for index, (herald, ports) in enumerate(bsm.PATTERNS):
        x, y = (gate.background_rates[port]*gate.duration for port in ports)
        left, right = x/(1+x), y/(1+y)
        delta = left*right
        pair_bounds.append({"pattern_index": index, "herald": herald, "ports": list(ports),
                            "Poisson_parameters": [str(x), str(y)], "at_least_one_lower_bounds": [str(left), str(right)],
                            "pair_success_probability_lower": str(delta),
                            "exact_path_probability": "(1-exp(-x))*(1-exp(-y))",
                            "success_scope": "any first receipt; the sufficient pair does not select its first herald",
                            "source_identity": "x=r_p*T, y=r_q*T; distinct independent raw background clocks"})
    selected = max(range(len(pair_bounds)), key=lambda index: (Q(pair_bounds[index]["pair_success_probability_lower"]), -index))
    delta = Q(pair_bounds[selected]["pair_success_probability_lower"])
    contraction = 1-delta
    positive = delta > 0
    return {"schema": SCHEMA, "source_kind": kind, "raw_source": source.record(),
            "seconds_per_source_unit": str(gate.seconds_per_unit), "background_seconds_per_unit": str(unit),
            "raw_background_rates": list(map(str, gate.background_rates)), "raw_gate_duration": str(gate.duration),
            "gate_seconds": str(bsm.GATE_SECONDS), "patterns": [[name, list(ports)] for name, ports in bsm.PATTERNS],
            "mark_law": mark_law, "quantum_law": quantum_law, "continuation_phase_laws": phase_laws,
            "pair_bounds": pair_bounds, "selected_pattern": selected if positive else None,
            "background_success_lower": str(delta), "one_attempt_failure_operator_upper": str(contraction),
            "forty_cycle_failure_operator_upper": _power(contraction, bsm.BURST_CYCLES),
            "burst_cycles": bsm.BURST_CYCLES,
            "status": "strict_source_stopping_contraction" if positive else "no_positive_supported_background_pair",
            "all_future_tail": {"limit": "0" if positive else None,
                                "positive_delta": str(delta) if positive else None,
                                "induction_bound": "(1-delta)^n <= 1/(1+n*delta)",
                                "epsilon_stage_rule": "N=max(1,ceil((1/epsilon-1)/delta))" if positive else None},
            "failure_effect_scope": "universal CP failure effect on every positive full-pair input; no quantum state is supplied",
            "programme_scope": "fixed raw source repeated without an external intervention" if kind == "programme" else
                               "repetition of this same full-gate instrument",
            "background_bound_rule": "exp(x)>=1+x for x>=0; 1-exp(-x)>=x/(1+x)",
            "target_stop_probability_supplied": False, "target_failure_effect_supplied": False,
            "finite_polynomial_centres_assumed_CP": False, "actual_background_calibrated": False,
            "actual_clock_identified": False, "new_empirical_records_read": 0,
            "actual_hardware_uniquely_identified": False, "controller_advance": False}


def verify_certificate(report, raw_source=None):
    _require(type(report) is dict and report.get("schema") == SCHEMA, "raw BSM background-tail certificate required")
    source = _from_record(report["source_kind"], report["raw_source"])
    if raw_source is not None:
        kind, expected_source = _source(raw_source)
        _require(kind == report["source_kind"] and expected_source.record() == source.record(), "background-tail raw source mismatch")
    expected = certify(source, background_seconds_per_unit=report["background_seconds_per_unit"])
    _require(expected == report, "background-tail source certificate mismatch")
    return True


def finite_tail(report, attempts, *, start_attempt_ordinal=0):
    _require(type(attempts) is int and attempts >= 0 and type(start_attempt_ordinal) is int and start_attempt_ordinal >= 0,
             "nonnegative integer source attempt counts and ordinals required")
    verify_certificate(report)
    delta, contraction = Q(report["background_success_lower"]), Q(report["one_attempt_failure_operator_upper"])
    end = start_attempt_ordinal+attempts
    has_programme = report["source_kind"] == "programme"
    return {"failure_operator_upper": _power(contraction, attempts),
            "rational_failure_upper": str(1/(1+attempts*delta)),
            "start_attempt_ordinal": start_attempt_ordinal, "end_attempt_ordinal": end,
            "next_block": end//bsm.BURST_CYCLES, "next_cycle": end%bsm.BURST_CYCLES+1,
            "recoolings_in_interval": end//bsm.BURST_CYCLES-start_attempt_ordinal//bsm.BURST_CYCLES if has_programme else None,
            "last_forty_attempt_recooling_already_consumed": end > 0 and end%bsm.BURST_CYCLES == 0 if has_programme else None,
            "cursor_scope": "source recurrence address; no realised stopping event or history is selected",
            "full_gate_used_each_attempt": True}


def epsilon_stage(report, epsilon):
    """Produce an arbitrarily small tail without expanding huge rational powers."""
    epsilon = full.exact(epsilon)
    _require(0 < epsilon < 1, "positive tail tolerance strictly below one required")
    verify_certificate(report)
    delta = Q(report["background_success_lower"])
    if not delta:
        return {"stage_produced": False, "reason": "no_positive_supported_background_pair", "retained_failure_tail_upper": "1"}
    required = (1/epsilon-1)/delta
    attempts = max(1, -(-required.numerator//required.denominator))
    upper = 1/(1+attempts*delta)
    _require(upper <= epsilon and 0 < delta <= 1, "generated stage fails the source tail inequality")
    return {"stage_produced": True, "attempts": attempts, "complete_blocks": attempts//bsm.BURST_CYCLES,
            "extra_cycles": attempts%bsm.BURST_CYCLES, "epsilon": str(epsilon), "rational_tail_upper": str(upper),
            "geometric_tail_upper": _power(1-delta, attempts),
            "induction_identity": "(1-delta)*(1+(n+1)*delta) = 1+n*delta-(n+1)*delta^2"}


def _weighted_trace_upper(p_center, b_center, global_error, radical_error, q):
    """Pure arithmetic for diag(I_pending,q*I_BSM); this certifies no source.

    A non-PSD numerical centre is allowed.  The functional has norm one on
    the true positive direct sum, so its one global trace-norm price is not
    multiplied by q or recharged for each component.
    """
    p_center, b_center, q = map(full.exact, (p_center, b_center, q))
    global_error, radical_error = map(full.nonnegative, (global_error, radical_error))
    _require(0 <= q <= 1, "positive contraction weight within [0,1] required")
    return max(Q(0), p_center+q*b_center+global_error+radical_error)


def history_tail_refinement(history_source, n):
    """Refine the exact history source's tail after n additional BSM attempts.

    Original matrices and clocks stay at their checked prefix.  The returned
    scalar bounds the uncomputed continuation; intermediate new receipts are
    still part of its unresolved measure.  A forecast using a longer prefix
    must generate that prefix's receipt measure before using this smaller tail.
    """
    _require(type(n) is int and n >= 0, "nonnegative integer additional BSM attempts required")
    # These history modules can consume this producer without an import cycle.
    import all_ready_history_law as all_ready
    import stopped_history_law as stopped_history
    import projected_window_cem as projected
    import fluorescence_channel as channel

    _require(type(history_source) in (stopped_history.StoppedHistoryLaw, all_ready.AllReadyHistoryLaw),
             "exact closed StoppedHistoryLaw or AllReadyHistoryLaw required")
    kind = "all_ready" if type(history_source) is all_ready.AllReadyHistoryLaw else "stopped"
    # Recheck source provenance and the original numerical witnesses once at
    # this mouth; never trust the caller's pending_tail method or cached weight.
    fresh = type(history_source).from_record(history_source.record())
    tail = fresh.pending_tail()
    components = fresh.components if kind == "all_ready" else (fresh,)
    bsm_tails = tail["BSM_pending"] if kind == "all_ready" else (tail,)
    certificates, certificate_keys, addresses = [], {}, []
    contractions, original_cursors, next_cursors = [], [], []
    for index, (source, pending) in enumerate(zip(components, bsm_tails)):
        raw_record = source.ingress["raw_burst"]
        _require(pending["raw_continuation_programme"] == raw_record,
                 "pending BSM tail must retain its original raw continuation programme")
        key = json.dumps(raw_record, sort_keys=True, separators=(",", ":"))
        if key not in certificate_keys:
            raw = _from_record("programme", raw_record)
            certificate_keys[key] = len(certificates)
            certificates.append(certify(raw))
        certificate_index = certificate_keys[key]
        certificate = certificates[certificate_index]
        _require(Q(certificate["seconds_per_source_unit"]) == source.component.mother.source.seconds_per_unit ==
                 Q(pending["seconds_per_source_unit"]), "history continuation and BG source must share one clock unit")
        contractions.append(Q(certificate["background_success_lower"]))
        ordinal = pending["attempt_ordinal"]
        original_cursor = stopped_history.continuation_cursor(ordinal)
        _require(all(pending[name] == value for name, value in original_cursor.items()),
                 "history tail cursor differs from its original checked attempt prefix")
        next_cursor = stopped_history.continuation_cursor(ordinal+n)
        original_cursors.append(original_cursor)
        next_cursors.append(next_cursor)
        addresses.append({"ready_index": index if kind == "all_ready" else source.component.mother.ready_index,
                          "background_certificate": certificate_index})
    _require(len(components) == len(bsm_tails) and contractions and len(set(contractions)) == 1,
             "every original ready BSM continuation must have the same raw background contraction")
    delta = contractions[0]
    q = 1/(1+n*delta)
    old_upper = full.nonnegative(tail["future_receipt_mass_upper"])
    if kind == "stopped":
        refined = q*old_upper
        prices = {"rule": "contraction times the original positive-tail trace upper",
                  "old_positive_tail_upper": str(old_upper), "BG_tail_upper": str(q),
                  "continued_BSM_tail_upper": str(refined),
                  "original_global_terminal_error": tail["global_terminal_error"]}
    else:
        b_matrix = {}
        for source in components:
            b_matrix = bsm.local._sum(b_matrix, source.programme.remaining_pair)
        p_matrix = {}
        for pending in tail["native_reload_pending"]:
            p_matrix = bsm.local._sum(p_matrix, channel._read_input(pending["complete_matrix"], joint.DIMENSION))
        p_center, p_radical = projected._trace(p_matrix)
        b_center, b_radical = projected._trace(b_matrix)
        weighted = bsm.local._sum(p_matrix, {key: q*value for key, value in b_matrix.items() if q*value})
        center, radical = projected._trace(weighted)
        _require(center == p_center+q*b_center and radical <= p_radical+q*b_radical,
                 "weighted full-source trace or radical enclosure lost linearity")
        root_error = full.nonnegative(fresh.root_error)
        terminal_prices = tuple(full.nonnegative(source.programme.global_terminal_error-root_error) for source in components)
        global_error = root_error+sum(terminal_prices, Q(0))
        _require(global_error == fresh.global_terminal_error == Q(tail["global_terminal_error"]),
                 "history whole-root error must be paid once across ready restrictions")
        weighted_upper = _weighted_trace_upper(p_center, b_center, global_error, radical, q)
        # The old tail also bounds the continued positive mass.  This preserves
        # refinement when a signed centre has a negative BSM trace.
        refined = min(old_upper, weighted_upper) if delta else old_upper
        prices = {"rule": "diag(I_reload_pending,q_BG*I_BSM_pending) has operator norm one",
                  "native_reload_trace_center": str(p_center), "native_reload_trace_radical_error": str(p_radical),
                  "BSM_trace_center": str(b_center), "BSM_trace_radical_error": str(b_radical),
                  "BG_tail_upper": str(q), "weighted_trace_center": str(center),
                  "weighted_trace_radical_error": str(radical), "common_parent_error": str(root_error),
                  "new_BSM_terminal_prices": list(map(str, terminal_prices)), "global_error_paid_once": str(global_error),
                  "weighted_functional_upper": str(weighted_upper), "intersected_with_original_tail_upper": str(old_upper),
                  "numerical_center_PSD_assumed": False, "component_error_views_summed": False}
    return {"schema": "stage10-original-history-BSM-tail-refinement/v1", "history_kind": kind,
            "history_source_record": fresh.record(), "original_pending_tail": json.loads(json.dumps(tail)),
            "background_source_certificates": certificates, "BSM_component_addresses": addresses,
            "additional_BSM_attempts": n, "background_success_lower": str(delta), "BG_tail_upper": str(q),
            "original_future_receipt_mass_upper": str(old_upper), "continued_tail_mass_upper": str(refined),
            "weighted_trace_price": prices, "original_BSM_cursors": original_cursors,
            "continuation_cursor_addresses": next_cursors,
            "common_continuation_cursor": next_cursors[0] if all(item == next_cursors[0] for item in next_cursors) else None,
            "strict_BG_stopping_contract_produced": delta > 0,
            "native_reload_pending_refined_by_BG": False, "original_matrices_times_stages_and_controls_retained": True,
            "new_receipt_measure_generated": False, "new_quantum_state_generated": False, "new_clock_mapped": False,
            "forecast_requires_matching_extended_receipt_prefix": True,
            "current_mu_extended": False, "cursor_scope": "conditional source recurrence addresses; no new event selected",
            "actual_hardware_uniquely_identified": False, "controller_advance": False}
