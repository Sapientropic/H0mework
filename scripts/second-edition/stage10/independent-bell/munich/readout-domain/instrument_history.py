"""Original Bell source -> complete joint CEM poststates -> shared APD intake.

The two full-atom instrument images come from the same raw command programmes
as the existing Born calculation.  The pair state retains neutral/ion and
magnetic coherence; its next observation is not inferred from a scalar click.
"""
from fractions import Fraction as Q
from itertools import product
from dataclasses import replace

import atomic_dipole as dipole
import atomic_full_forward as full
import raw_command_family as family


DIMENSION = full.DIMENSION ** 2


def _add(target, source, coefficient=1):
    for key, (real, imag) in source.items():
        full._add(target, key, coefficient * real, coefficient * imag)


def _tensor(first, second):
    result = {}
    for (i, j), (a, b) in first.items():
        for (k, l), (c, d) in second.items():
            full._add(result, (full.DIMENSION*i+k, full.DIMENSION*j+l), a*c-b*d, a*d+b*c)
    return result


def _bell_image(left, right, h):
    result, error = [], Q(0)
    terms = (("00", "11", Q(1, 2)), ("11", "00", Q(1, 2)),
             ("01", "10", Q(2*h-1, 2)), ("10", "01", Q(2*h-1, 2)))
    for a, b, coefficient in terms:
        result.append({"coefficient": str(coefficient), "left": left[a], "right": right[b]})
        ea, eb = Q(left[a]["trace_norm_error_bound"]), Q(right[b]["trace_norm_error_bound"])
        # A CP trace-nonincreasing instrument contracts trace norm, including E_ij.
        error += abs(coefficient) * (ea + eb + ea*eb)
    return result, error


def _product_trace(terms, neutral_a=False, neutral_b=False):
    result = (Q(0), Q(0))
    for term in terms:
        traces = []
        for item, neutral in ((term["left"], neutral_a), (term["right"], neutral_b)):
            matrix = family._density(item)
            traces.append(tuple(sum((pair[k] for (i, j), pair in matrix.items()
                                     if i == j and (not neutral or i != dipole.ION)), Q(0)) for k in (0, 1)))
        (a, b), (c, d) = traces
        coefficient = Q(term["coefficient"])
        result = result[0]+coefficient*(a*c-b*d), result[1]+coefficient*(a*d+b*c)
    if result[1]:
        raise ValueError("original Bell poststate trace is not real")
    return result[0]


def _record(terms, error):
    trace = _product_trace(terms)
    neutral_a, neutral_b = _product_trace(terms, True), _product_trace(terms, False, True)
    both_neutral = _product_trace(terms, True, True)
    return {"tensor_terms": terms, "trace_norm_error_bound": str(error),
            "trace_center": str(trace),
            "probability_interval": family.Interval(trace-error, trace+error).probability_domain().record(),
            "neutral_A_trace_interval": family.Interval(neutral_a-error, neutral_a+error).probability_domain().record(),
            "neutral_B_trace_interval": family.Interval(neutral_b-error, neutral_b+error).probability_domain().record(),
            "both_neutral_trace_interval": family.Interval(both_neutral-error, both_neutral+error).probability_domain().record()}


def _validate_side(side, name, setting):
    if type(side) is not family.SidePrediction or side.side != name or setting not in (0, 1) or type(setting) is not int:
        raise ValueError("original ordered side and binary setting required")
    family.probability(side.d)
    family.probability(side.eta)
    program, report = side.programs[setting], side.reports[setting]
    command_bits = max(64, *(endpoint.denominator.bit_length()-1
                            for interval in program.command.bounds for endpoint in interval))
    expected = family.compile_commands(program.transfer, tuple(
        replace(segment, fields_r=dict.fromkeys(dipole.Q_COMPONENTS, 0))
        for segment in program.segments), family.SIDE_ANGLES[name][setting],
        command_bits=command_bits)
    if program.record() != expected.record():
        raise ValueError("side setting belongs to a different raw command source")
    full.verify_certificate(report, program.segments)
    instrument = family.post_instrument(report, program.command_trace_norm_error, side.d, side.eta)
    if instrument != side.instruments[setting]:
        raise ValueError("CEM poststate differs from its raw detector source")
    effect = family.detector_effect(report, program.command_trace_norm_error, side.d, side.eta)
    if effect != side.effects[setting]:
        raise ValueError("Born effect differs from its raw detector source")
    return family.instrument_maps(instrument)


def pair_poststates(alice, bob, *, h, a, b):
    if type(h) is not int or h not in (0, 1):
        raise ValueError("original binary herald required")
    left, right = _validate_side(alice, "alice", a), _validate_side(bob, "bob", b)
    total, total_error = _bell_image(left["Phi"], right["Phi"], h)
    branches = []
    for x, y in product((0, 1), repeat=2):
        state, error = _bell_image(left["click" if x else "noclick"],
                                   right["click" if y else "noclick"], h)
        born = family.tensor_born(alice.effects[a], bob.effects[b], h, x, y)
        record = _record(state, error)
        first, second = map(Q, record["probability_interval"])
        lo, hi = map(Q, born["probability_interval"])
        if max(first, lo) > min(second, hi):
            raise ValueError("joint poststate trace and original tensor Born disagree")
        branches.append({"x": x, "y": y, **record, "original_tensor_born": born})
    for maps in (left, right):
        for unit in ("00", "11", "01", "10"):
            if family._sum(family._density(maps["click"][unit]), family._density(maps["noclick"][unit])) != family._density(maps["Phi"][unit]):
                raise ValueError("same source local CEM sum fails; tensor distributivity unavailable")
    trace = _product_trace(total)
    if not trace-total_error <= 1 <= trace+total_error:
        raise ValueError("unconditional Bell pair trace envelope excludes one")
    return {"schema": "stage10-bell-joint-poststate-history/v1", "h": h, "a": a, "b": b,
            "physical_dimension_per_atom": full.DIMENSION, "pair_hilbert_dimension": DIMENSION,
            "tensor_address": "33 * Alice_state + Bob_state; original atomic_dipole inventory",
            "source_input_basis": ["u_x", "d_x"],
            "source_cross_coefficient": str(Q(2*h-1, 2)),
            "density_representation": "complete four-term operator tensor sum; no coordinate or coherence is discarded",
            "raw_programs": {"alice": alice.programs[a].record(), "bob": bob.programs[b].record()},
            "detectors": {"alice": {"d": str(alice.d), "eta": str(alice.eta)},
                          "bob": {"d": str(bob.d), "eta": str(bob.eta)}},
            "branches": branches, "unconditional_poststate": _record(total, total_error),
            "complete_CEM_sum_checked": True, "original_Born_intersections_checked": True,
            "source_cp_trace_norm_contraction_used": True, "center_complete_positivity_claimed": False,
            "actual_clock_programme_identified": False, "actual_hardware_uniquely_identified": False,
            "controller_advance": False}


def counter_input(branch):
    """Literal same-state intake for a joint fluorescence counter source."""
    matrix = {}
    for term in branch["tensor_terms"]:
        first, second = family._density(term["left"]), family._density(term["right"])
        if any(not 0 <= i < 33 or not 0 <= j < 33 for i, j in set(first)|set(second)):
            raise ValueError("complete original pair density addresses required")
        _add(matrix, _tensor(first, second), full.exact(term["coefficient"]))
    return {key: dipole.ComplexRadical(*pair) for key, pair in matrix.items()}


def matrix_entry(branch, row, column):
    if any(type(i) is not int or not 0 <= i < DIMENSION for i in (row, column)):
        raise ValueError("complete original pair density addresses required")
    a, b = divmod(row, full.DIMENSION)
    c, d = divmod(column, full.DIMENSION)
    result = dipole.ComplexRadical()
    for term in branch["tensor_terms"]:
        left = family._density(term["left"]).get((a, c), (0, 0))
        right = family._density(term["right"]).get((b, d), (0, 0))
        result += full.exact(term["coefficient"]) * dipole.ComplexRadical(*left) * dipole.ComplexRadical(*right)
    return result
