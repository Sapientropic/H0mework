"""Independent full-mark BSM poststate and first-receipt residual checker.

The address is count_base3 + 81*receipt_code; receipt_code zero means pending
and 1..4 names the four original patterns.  The ambient 405 slots have 161
legal Mark values.  The inherited threshold attribute is an address bound,
never a photon threshold or BSM success test.  Only BSMSource.from_record can
generate the action.  Search curves remain untrusted; no solver is imported.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import atomic_dipole as dipole
import atomic_full_forward as full
import bsm_retry_source as bsm
import fluorescence_channel as channel


SCHEMA = "stage10-bsm-full-mark-poststate-enclosure/v1"
MARK_SLOTS = 405
ZERO = dipole.ComplexRadical()


def mark_index(mark):
    channel._require(type(mark) is bsm.Mark, "original source BSM Mark required")
    return sum(value*3**port for port, value in enumerate(mark.counts)) + 81*(0 if mark.receipt is None else mark.receipt+1)


def index_mark(index):
    channel._require(type(index) is int and 0 <= index < MARK_SLOTS, "closed BSM mark address required")
    receipt, count = divmod(index, 81)
    counts = tuple(count//3**port % 3 for port in range(4))
    return bsm.Mark(counts, None if receipt == 0 else receipt-1)


def _inventory():
    result = []
    for index in range(MARK_SLOTS):
        try:
            mark = index_mark(index)
        except ValueError:
            continue
        result.append((index, mark))
    return tuple(result)


MARK_INVENTORY = _inventory()


class _MarkProjection:
    def __init__(self, record):
        self.bsm = bsm.BSMSource.from_record(record)
        self.duration, self.threshold = self.bsm.duration, MARK_SLOTS-1

    def record(self):
        return self.bsm.record()

    def action(self, matrix):
        raw = {(index_mark(c), i, j): value for (c, i, j), value in matrix.items()}
        return {(mark_index(mark), i, j): value for (mark, i, j), value in self.bsm.action(raw).items()}


class SourceKernel(channel.SourceKernel):
    def __init__(self, generator, coefficient_bits=160):
        channel._require(type(generator) is bsm.BSMSource, "closed raw BSMSource constructor required; arbitrary G is not input")
        channel._require(type(coefficient_bits) is int and 64 <= coefficient_bits <= 512,
                         "registered coefficient precision required")
        self.source = _MarkProjection(generator.record())
        self.dimension, self.threshold = bsm.joint.DIMENSION, MARK_SLOTS-1
        self.bits, self.columns, self.exact_columns, self.errors = coefficient_bits, {}, {}, {}


def _initial_marked(matrix):
    channel._require(type(matrix) is dict, "same-source full marked input required")
    result = {}
    for key, value in matrix.items():
        channel._require(type(key) is tuple and len(key) == 3 and type(key[0]) is bsm.Mark,
                         "original BSM Mark and full pair matrix addresses required")
        c, i, j = mark_index(key[0]), key[1], key[2]
        channel._key((c, i, j), bsm.joint.DIMENSION, MARK_SLOTS-1)
        value = dipole.complex_exact(value)
        if value:
            result[c, i, j] = value
    channel._require(all(result.get((c, j, i), ZERO) == value.conjugate() for (c, i, j), value in result.items()),
                     "Hermitian full marked source input required")
    return result


def _initial_record(matrix):
    return [[c, i, j, value.serialize()] for (c, i, j), value in sorted(matrix.items())]


def _read_initial(record):
    channel._require(type(record) is list, "complete marked input record required")
    result = {}
    for item in record:
        channel._require(type(item) is list and len(item) == 4, "marked source input entry required")
        c, i, j, value = item
        key = index_mark(c), i, j
        channel._require(key not in result, "duplicate marked input address")
        result[key] = channel._complex_record(value)
    _initial_marked(result)
    return result


def _observations(source, center, error, bits, elapsed):
    failure, success, total = {}, {}, {}
    patterns, blocks = tuple({} for _ in range(4)), []
    raw = {}
    for index, mark in MARK_INVENTORY:
        matrix = {(i, j): value for (c, i, j), value in center.items() if c == index}
        blocks.append({"mark_index": index, "counts": list(mark.counts), "receipt": mark.receipt,
                       **channel._observation(matrix, error)})
        destination = failure if mark.receipt is None else success
        for key, (a, b) in matrix.items():
            full._add(destination, key, a, b)
            full._add(total, key, a, b)
            if mark.receipt is not None:
                full._add(patterns[mark.receipt], key, a, b)
            raw[mark, *key] = dipole.ComplexRadical(a, b)
    exact_rates = tuple({} for _ in range(4))
    for item in source.success_flux(raw, at_time=source.interval_start+elapsed):
        for key, value in item["poststate_rate"].items():
            bsm.local._add(exact_rates[item["target_mark"].receipt], key, value)
    rate_centers, rounding = [], Q(0)
    for matrix in exact_rates:
        midpoint, remainder = full._midpoint_matrix(matrix, bits)
        rate_centers.append(midpoint)
        rounding += sum(remainder.values(), Q(0))
    bound = sum(max(atom.outgoing) for atom in source.source.sources)+sum(source.background_rates)
    rate_error = bound*error+rounding
    return {"mark_blocks": blocks, "failure": channel._observation(failure, error),
            "success": channel._observation(success, error),
            "first_receipt_CDF": {**channel._observation(success, error),
                                  "atomic_state_coordinate": "evaluation time; trace is cumulative first-receipt probability"},
            "patterns": [{"pattern_index": p, "herald": bsm.PATTERNS[p][0], **channel._observation(matrix, error)}
                         for p, matrix in enumerate(patterns)], "unconditional": channel._observation(total, error),
            "first_receipt_density": {"at_raw_source_time": str(source.interval_start+elapsed),
                "patterns": [{"pattern_index": p, "herald": bsm.PATTERNS[p][0],
                              **channel._observation(matrix, rate_error)} for p, matrix in enumerate(rate_centers)],
                "global_trace_norm_error_bound": str(rate_error), "CP_rate_norm_upper": str(bound),
                "radical_midpoint_error": str(rounding),
                "atomic_state_coordinate": "first receipt event time; CP rate, not an integrated snapshot",
                "error_scope": "whole four-pattern CP-rate direct sum, including omitted mark/matrix coordinates"}}


def _bindings(source):
    records = {item["path"]: item for item in channel._bindings(source.source)}
    for path in (Path(__file__).resolve(), Path(bsm.__file__).resolve()):
        relative = str(path.relative_to(full.ROOT))
        records[relative] = {"path": relative, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    return [records[path] for path in sorted(records)]


def certify_marked(generator, initial, pieces, *, upstream_error=0, mode_bits=60,
                   coefficient_bits=160, exponential_bits=160, evaluation_duration=None):
    channel._require(type(mode_bits) is int and 32 <= mode_bits <= 256, "registered trial-mode precision required")
    channel._require(type(exponential_bits) is int and 64 <= exponential_bits <= 1024, "registered scalar precision required")
    channel._require(type(pieces) is list, "complete source-time trial pieces required")
    kernel = SourceKernel(generator, coefficient_bits)
    source = kernel.source.bsm
    duration = source.duration if evaluation_duration is None else full.nonnegative(evaluation_duration)
    channel._require(duration <= source.duration, "BSM query exceeds its raw source interval")
    initial, inherited = _initial_marked(initial), full.nonnegative(upstream_error)
    center, initial_error = {}, Q(0)
    for key, value in initial.items():
        a, da = full.radical_midpoint(value.real, coefficient_bits)
        b, db = full.radical_midpoint(value.imag, coefficient_bits)
        full._add(center, key, a, b)
        initial_error += da+db
    error, elapsed, records = inherited+initial_error, Q(0), []
    for piece in pieces:
        width, begin, end, errors, diagnostics = channel._piece(kernel, piece, mode_bits, exponential_bits)
        gap = channel._difference(begin, center)
        error += gap+sum(errors.values(), Q(0))
        elapsed += width
        channel._require(elapsed <= duration, "trial pieces extend beyond queried BSM time")
        records.append({"duration": str(width), "initial_join_error": str(gap),
                        **{key: str(value) for key, value in errors.items()}, "modes": diagnostics})
        center = end
    channel._require(elapsed == duration, "trial pieces must cover the whole queried BSM interval")
    raw_source, raw_initial = source.record(), _initial_record(initial)
    return {"schema": SCHEMA, "certified": True, "physical_dimension": kernel.dimension,
            "ambient_mark_slots": MARK_SLOTS, "legal_mark_slots": len(MARK_INVENTORY),
            "mark_index_encoding": "count_base3 + 81*receipt_code; 0 pending, 1..4 original pattern+1",
            "mark_complex_coordinates": len(MARK_INVENTORY)*kernel.dimension**2,
            "duration": str(duration), "raw_source_duration": str(source.duration),
            "raw_source": raw_source, "raw_source_sha256": channel._digest(raw_source),
            "initial_marked_state": raw_initial, "initial_state_sha256": channel._digest(raw_initial),
            "upstream_trace_norm_error": str(inherited), "initial_radical_error": str(initial_error),
            "trial_pieces": json.loads(channel._canonical(pieces)), "piece_error_records": records,
            "mode_bits": mode_bits, "coefficient_bits": coefficient_bits, "exponential_bits": exponential_bits,
            "source_columns_checked": len(kernel.columns), "trace_norm_error_bound": str(error),
            "counter_poststate_center": [[c, i, j, str(a), str(b)] for (c, i, j), (a, b) in sorted(center.items())],
            **_observations(source, center, error, coefficient_bits, elapsed), "source_bindings": _bindings(source),
            "source_time_coverage_complete": True, "whole_raw_interval_covered": duration == source.duration,
            "source_mark_trace_preservation_checked": True, "complete_poststate_enclosure": True,
            "omitted_entries_covered_by_global_error": True, "upstream_error_counted_once": True,
            "mark_address_is_photon_threshold": False, "success_defined_by_last_address": False,
            "receipt_stops_atomic_dynamics": False, "solver_reexecuted_by_checker": False,
            "eigenvector_correctness_assumed": False, "input_positivity_certified_here": False,
            "physical_probability_interpretation_requires_positive_input": True,
            "first_receipt_CDF_includes_initial_receipts": True,
            "error_transport": "Hermitian whole-mark CPTP contraction; projections share one global budget",
            "actual_programme_identified": False, "actual_hardware_identity_asserted": False,
            "controller_advance": False, "propagation_performed": True}


def certify(generator, initial, pieces, *, initial_mark=bsm.INITIAL, **kwargs):
    channel._require(type(initial_mark) is bsm.Mark, "original initial BSM Mark required")
    initial = channel._initial(initial, bsm.joint.DIMENSION)
    return certify_marked(generator, {(initial_mark, i, j): value for (i, j), value in initial.items()}, pieces, **kwargs)


def verify_certificate(report, generator=None, initial=None, *, initial_mark=bsm.INITIAL, upstream_error=None):
    channel._require(type(report) is dict and report.get("schema") == SCHEMA, "BSM residual source certificate required")
    source = bsm.BSMSource.from_record(report["raw_source"]) if generator is None else SourceKernel(generator).source.bsm
    channel._require(source.record() == report["raw_source"], "raw BSM programme or mark source mismatch")
    if initial is None:
        initial = _read_initial(report["initial_marked_state"])
    elif type(initial) is dict and all(type(key) is tuple and len(key) == 2 for key in initial):
        channel._require(type(initial_mark) is bsm.Mark, "original initial BSM Mark required")
        matrix = channel._initial(initial, bsm.joint.DIMENSION)
        initial = {(initial_mark, i, j): value for (i, j), value in matrix.items()}
    channel._require(_initial_record(_initial_marked(initial)) == report["initial_marked_state"], "initial marked source state mismatch")
    inherited = report["upstream_trace_norm_error"] if upstream_error is None else upstream_error
    channel._require(full.nonnegative(inherited) == full.nonnegative(report["upstream_trace_norm_error"]), "upstream error binding mismatch")
    expected = certify_marked(source, initial, report["trial_pieces"], upstream_error=inherited,
                mode_bits=report["mode_bits"], coefficient_bits=report["coefficient_bits"],
                exponential_bits=report["exponential_bits"], evaluation_duration=report["duration"])
    channel._require(expected == report, "BSM residual source certificate mismatch")
    return True


def counter_poststate(report):
    return {(index_mark(c), i, j): dipole.ComplexRadical(full.exact(a), full.exact(b))
            for c, i, j, a, b in report["counter_poststate_center"]}, full.nonnegative(report["trace_norm_error_bound"])


def poststate(report, branch="failure"):
    channel._require(branch in ("failure", "success", "unconditional", "Psi-", "Psi+"), "physical BSM branch required")
    if branch in ("Psi-", "Psi+"):
        matrix = {}
        for item in report["patterns"]:
            if item["herald"] == branch:
                for i, j, a, b in item["poststate_center"]:
                    full._add(matrix, (i, j), full.exact(a), full.exact(b))
    else:
        matrix = {(i, j): (full.exact(a), full.exact(b)) for i, j, a, b in report[branch]["poststate_center"]}
    return {key: dipole.ComplexRadical(*value) for key, value in matrix.items()}, full.nonnegative(report["trace_norm_error_bound"])


def at_time(report, elapsed):
    """Pure-checker prefix CDF/density; no solver or external endpoint is input."""
    verify_certificate(report)
    elapsed = full.nonnegative(elapsed)
    channel._require(elapsed <= full.exact(report["duration"]), "source-time prefix exceeds certified interval")
    pieces, covered = [], Q(0)
    for piece in report["trial_pieces"]:
        if covered == elapsed:
            break
        width = full.exact(piece["duration"])
        take = min(width, elapsed-covered)
        if take == width:
            pieces.append(piece)
        else:
            scaled = []
            for mode in piece["modes"]:
                matrices = []
                for k, matrix in enumerate(mode["coefficients"]):
                    values = []
                    for c, i, j, real, imag in matrix:
                        factor = (take/width)**k
                        a, b = real*factor, imag*factor
                        r, s = (full._round_nearest(value.numerator, value.denominator) for value in (a, b))
                        if r or s:
                            values.append([c, i, j, r, s])
                    matrices.append(values)
                scaled.append({"lambda": mode["lambda"], "coefficients": matrices})
            pieces.append({"duration": str(take), "modes": scaled})
        covered += take
    return certify_marked(bsm.BSMSource.from_record(report["raw_source"]), _read_initial(report["initial_marked_state"]),
            pieces, upstream_error=report["upstream_trace_norm_error"], mode_bits=report["mode_bits"],
            coefficient_bits=report["coefficient_bits"], exponential_bits=report["exponential_bits"], evaluation_duration=elapsed)
