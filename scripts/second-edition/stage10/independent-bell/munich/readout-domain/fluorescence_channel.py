"""Complete fluorescence-counter poststates from raw source residual curves.

A trial piece is sum_j exp(lambda_j*t) sum_k M_jk*(t/Delta)^k.
Its source residual coefficients are G M_jk-lambda_j M_jk-
(k+1) M_j,k+1/Delta.  The checker uses the exact source action, outward
radical bounds and CPTP contraction on the Hermitian trial curve.  It never
assumes eigenvectors, reruns the solver or accepts a target count effect.
"""
from fractions import Fraction as Q
import hashlib
import importlib
import json
from pathlib import Path

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as modes
import atom_photon_source as photons
import fluorescence_presence as presence


SCHEMA = "stage10-fluorescence-poststate-enclosure/v1"
ZERO = dipole.ComplexRadical()


def _require(condition, reason):
    if not condition:
        raise ValueError(reason)


def _canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _digest(value):
    return hashlib.sha256(_canonical(value).encode()).hexdigest()


def _complex_record(value):
    _require(type(value) is dict and set(value) == {"real", "imag"}, "exact complex source coefficient required")
    def radical(item):
        _require(type(item) is dict, "exact radical source coefficient required")
        return dipole.Radical({int(root): full.exact(coefficient) for root, coefficient in item.items()})
    return dipole.ComplexRadical(radical(value["real"]), radical(value["imag"]))


def source_from_record(record):
    _require(type(record) is dict, "raw fluorescence source record required")
    if record.get("schema") == "rb87-fluorescence-counter-source/v1":
        program = full.Segment.from_record(record["probe_programme"])
        collection = record["collection"]
        if collection["mode"] == "coherent_2x3":
            raw = {tuple(item["label"]): tuple(tuple(_complex_record(value) for value in row)
                                                    for row in item["matrix"])
                   for item in collection["groups"]}
            generator = presence.CounterGenerator(program, threshold=record["threshold"],
                                                  background_rate=record["background_rate"], collection=raw)
        elif collection["mode"] == "diagonal_original_channels":
            raw = {tuple(item["label"]): full.exact(item["efficiency"]) for item in collection["channels"]}
            generator = presence.CounterGenerator(program, threshold=record["threshold"],
                                                  background_rate=record["background_rate"], efficiencies=raw)
        else:
            raise ValueError("registered source collection mode required")
    else:
        joint = importlib.import_module("joint_fluorescence_presence")
        generator = joint.JointCounterGenerator.from_record(record)
    _require(generator.record() == record, "raw source record does not reconstruct the same generator")
    return generator


def _source(generator):
    allowed = type(generator) is presence.CounterGenerator
    if not allowed and type(generator).__module__ == "joint_fluorescence_presence":
        joint = importlib.import_module("joint_fluorescence_presence")
        allowed = type(generator) is joint.JointCounterGenerator
    _require(allowed, "registered raw fluorescence source constructor required")
    return source_from_record(generator.record())


def _duration(source):
    return full.nonnegative(source.duration if hasattr(source, "duration") else source.program.duration)


def _key(key, dimension, threshold):
    _require(type(key) is tuple and len(key) == 3 and all(type(n) is int for n in key)
             and 0 <= key[0] <= threshold and 0 <= key[1] < dimension and 0 <= key[2] < dimension,
             "original counter/atom matrix address required")


def _initial(matrix, dimension):
    _require(type(matrix) is dict, "original sparse atomic input matrix required")
    result = {}
    for key, value in matrix.items():
        _require(type(key) is tuple and len(key) == 2 and all(type(n) is int and 0 <= n < dimension for n in key),
                 "original atomic input matrix address required")
        value = dipole.complex_exact(value)
        if value:
            result[key] = value
    _require(all(result.get((j, i), ZERO) == value.conjugate() for (i, j), value in result.items()),
             "Hermitian source input required; matrix units must be decomposed before propagation")
    return result


def _input_record(matrix):
    return [[i, j, value.serialize()] for (i, j), value in sorted(matrix.items())]


def _read_input(record, dimension):
    _require(type(record) is list, "complete initial source matrix record required")
    matrix = {}
    for item in record:
        _require(type(item) is list and len(item) == 3, "initial matrix record entry required")
        i, j, value = item
        _require((i, j) not in matrix, "duplicate initial matrix address")
        matrix[i, j] = _complex_record(value)
    return _initial(matrix, dimension)


def _add(matrix, key, real, imag):
    full._add(matrix, key, real, imag)


def _hermitian(matrix):
    answer = {}
    for c, i, j in set(matrix) | {(c, j, i) for c, i, j in matrix}:
        a, b = matrix.get((c, i, j), (Q(0), Q(0)))
        u, v = matrix.get((c, j, i), (Q(0), Q(0)))
        _add(answer, (c, i, j), (a + u) / 2, (b - v) / 2)
    return answer


def _difference(first, second):
    return sum((abs(first.get(key, (0, 0))[0] - second.get(key, (0, 0))[0]) +
                abs(first.get(key, (0, 0))[1] - second.get(key, (0, 0))[1])
                for key in set(first) | set(second)), Q(0))


def _entry_norm(matrix):
    return sum((abs(a) + abs(b) for a, b in matrix.values()), Q(0))


class SourceKernel:
    """Lazy exact source columns, including every output outside a trial space."""
    def __init__(self, generator, coefficient_bits=160):
        _require(type(coefficient_bits) is int and 64 <= coefficient_bits <= 512,
                 "registered coefficient precision required")
        self.source = _source(generator)
        self.dimension = self.source.record()["physical_dimension"]
        self.threshold = self.source.threshold
        self.bits, self.columns, self.exact_columns, self.errors = coefficient_bits, {}, {}, {}

    def column(self, key):
        _key(key, self.dimension, self.threshold)
        if key not in self.columns:
            exact = self.source.action({key: dipole.ComplexRadical(1)})
            total = ZERO
            center, error = {}, Q(0)
            for target, value in exact.items():
                _key(target, self.dimension, self.threshold)
                value = dipole.complex_exact(value)
                if target[1] == target[2]:
                    total += value
                a, da = full.radical_midpoint(value.real, self.bits)
                b, db = full.radical_midpoint(value.imag, self.bits)
                if a or b:
                    center[target] = a, b
                error += da + db
            _require(not total, "raw source counter action fails total trace conservation")
            self.exact_columns[key], self.columns[key], self.errors[key] = exact, center, error
        return self.columns[key]

    def action(self, matrix):
        answer = {}
        for key, (a, b) in matrix.items():
            for target, (r, s) in self.column(key).items():
                _add(answer, target, r * a - s * b, r * b + s * a)
        return answer

    def coefficient_error(self, matrix):
        answer = Q(0)
        for key, (a, b) in matrix.items():
            self.column(key)
            answer += (abs(a) + abs(b)) * self.errors[key]
        return answer

    def reachable(self, keys, max_coordinates=50000):
        _require(type(max_coordinates) is int and max_coordinates > 0, "positive sparse-coordinate budget required")
        pending = list(keys)
        known = set(pending)
        _require(len(known) <= max_coordinates, "source reachable-coordinate budget exceeded")
        while pending:
            key = pending.pop()
            self.column(key)
            for target, value in self.exact_columns[key].items():
                if value and target not in known:
                    known.add(target)
                    _require(len(known) <= max_coordinates, "source reachable-coordinate budget exceeded")
                    pending.append(target)
        return tuple(sorted(known))


def _coefficient(record, quantum, kernel):
    _require(type(record) is list, "sparse trial coefficient matrix required")
    result = {}
    for item in record:
        _require(type(item) is list and len(item) == 5 and all(type(n) is int for n in item),
                 "dyadic counter/atom coefficient entry required")
        c, i, j, real, imag = item
        key = c, i, j
        _key(key, kernel.dimension, kernel.threshold)
        _require(key not in result and (real or imag), "canonical nonzero trial coefficient required")
        result[key] = Q(real, quantum), Q(imag, quantum)
    return result


def _piece(kernel, item, mode_bits, exponential_bits):
    _require(type(item) is dict and set(item) == {"duration", "modes"},
             "source trial piece identity required; target poststate is not input")
    duration = full.nonnegative(item["duration"])
    _require(duration > 0 and type(item["modes"]) is list and item["modes"], "positive-duration trial piece required")
    quantum = 1 << mode_bits
    begin, end = {}, {}
    residual, coefficient, exponential = Q(0), Q(0), Q(0)
    records = []
    for mode in item["modes"]:
        _require(type(mode) is dict and set(mode) == {"lambda", "coefficients"}, "exponential-polynomial mode required")
        exponent = mode["lambda"]
        _require(type(exponent) is list and len(exponent) == 2 and all(type(n) is int for n in exponent),
                 "dyadic complex exponent required")
        lr, li = (Q(n, quantum) for n in exponent)
        _require(lr * duration <= Q(1, 2), "bounded mode growth required")
        _require(type(mode["coefficients"]) is list and mode["coefficients"], "complete polynomial coefficients required")
        matrices = [_coefficient(value, quantum, kernel) for value in mode["coefficients"]]
        norms, residuals = [], []
        for k, matrix in enumerate(matrices):
            action = kernel.action(matrix)
            following = matrices[k + 1] if k + 1 < len(matrices) else {}
            defect = Q(0)
            for key in set(matrix) | set(action) | set(following):
                a, b = matrix.get(key, (Q(0), Q(0)))
                r, s = action.get(key, (Q(0), Q(0)))
                u, v = following.get(key, (Q(0), Q(0)))
                defect += abs(r - lr * a + li * b - (k + 1) * u / duration)
                defect += abs(s - li * a - lr * b - (k + 1) * v / duration)
            residual += defect
            coefficient += kernel.coefficient_error(matrix)
            norms.append(_entry_norm(matrix))
            residuals.append(defect)
        scalar, scalar_error = modes.complex_exponential(lr * duration, li * duration, bits=exponential_bits)
        for key, (a, b) in matrices[0].items():
            _add(begin, key, a, b)
        for matrix in matrices:
            for key, (a, b) in matrix.items():
                _add(end, key, a * scalar[0] - b * scalar[1], a * scalar[1] + b * scalar[0])
        exponential += sum(norms, Q(0)) * scalar_error
        records.append({"degree": len(matrices) - 1, "coefficient_entry_norms": list(map(str, norms)),
                        "residual_entry_norms": list(map(str, residuals)), "scalar_exponential_error": str(scalar_error)})
    return duration, _hermitian(begin), _hermitian(end), {
        "source_residual_error": 2 * duration * residual,
        "radical_coefficient_error": 2 * duration * coefficient,
        "scalar_exponential_error": exponential,
    }, records


def _center_record(matrix):
    return [[i, j, str(a), str(b)] for (i, j), (a, b) in sorted(matrix.items())]


def _observation(matrix, error):
    trace = sum((a for (i, j), (a, _) in matrix.items() if i == j), Q(0))
    return {"poststate_center": _center_record(matrix), "trace_norm_error_bound": str(error),
            "trace_bounds": [str(trace - error), str(trace + error)], "omitted_entry_center": "0"}


def _observations(center, error, threshold):
    below, above, total = {}, {}, {}
    blocks = []
    for counter in range(threshold + 1):
        matrix = {(i, j): value for (c, i, j), value in center.items() if c == counter}
        blocks.append(dict(counter=counter, **_observation(matrix, error)))
        branch = above if counter == threshold else below
        for key, (a, b) in matrix.items():
            _add(branch, key, a, b)
            _add(total, key, a, b)
    return {"counter_blocks": blocks, "below_N": _observation(below, error),
            "at_least_N": _observation(above, error), "unconditional": _observation(total, error)}


def _bindings(source):
    paths = {Path(__file__).resolve(), Path(presence.__file__).resolve(), Path(full.__file__).resolve(),
             Path(dipole.__file__).resolve(), Path(modes.__file__).resolve(), Path(photons.__file__).resolve()}
    if type(source).__module__ == "joint_fluorescence_presence":
        paths.add(Path(importlib.import_module("joint_fluorescence_presence").__file__).resolve())
    return [{"path": str(path.relative_to(full.ROOT)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            for path in sorted(paths)]


def certify(generator, initial, pieces, *, initial_counter=0, upstream_error=0,
            mode_bits=60, coefficient_bits=160, exponential_bits=160):
    _require(type(mode_bits) is int and 32 <= mode_bits <= 256, "registered trial-mode precision required")
    _require(type(exponential_bits) is int and 64 <= exponential_bits <= 1024, "registered scalar precision required")
    _require(type(pieces) is list, "complete source-time trial pieces required")
    kernel = SourceKernel(generator, coefficient_bits)
    source, duration = kernel.source, _duration(kernel.source)
    _key((initial_counter, 0, 0), kernel.dimension, kernel.threshold)
    initial = _initial(initial, kernel.dimension)
    upstream_error = full.nonnegative(upstream_error)
    center, initial_radical_error = {}, Q(0)
    for (i, j), value in initial.items():
        a, da = full.radical_midpoint(value.real, coefficient_bits)
        b, db = full.radical_midpoint(value.imag, coefficient_bits)
        _add(center, (initial_counter, i, j), a, b)
        initial_radical_error += da + db
    error, elapsed, records = upstream_error + initial_radical_error, Q(0), []
    for item in pieces:
        width, begin, end, errors, diagnostics = _piece(kernel, item, mode_bits, exponential_bits)
        gap = _difference(begin, center)
        error += gap + sum(errors.values(), Q(0))
        elapsed += width
        _require(elapsed <= duration, "trial pieces extend beyond raw programme duration")
        records.append({"duration": str(width), "initial_join_error": str(gap),
                        **{name: str(value) for name, value in errors.items()}, "modes": diagnostics})
        center = end
    _require(elapsed == duration, "trial pieces must cover the whole raw programme duration")
    observations = _observations(center, error, kernel.threshold)
    raw_source, raw_initial = source.record(), _input_record(initial)
    return {"schema": SCHEMA, "certified": True, "physical_dimension": kernel.dimension,
            "counter_levels": kernel.threshold + 1, "duration": str(duration),
            "counter_complex_coordinates": (kernel.threshold + 1) * kernel.dimension ** 2,
            "raw_source": raw_source, "raw_source_sha256": _digest(raw_source),
            "initial_state": raw_initial, "initial_state_sha256": _digest(raw_initial),
            "initial_counter": initial_counter, "upstream_trace_norm_error": str(upstream_error),
            "initial_radical_error": str(initial_radical_error),
            "trial_pieces": json.loads(_canonical(pieces)), "piece_error_records": records,
            "mode_bits": mode_bits, "coefficient_bits": coefficient_bits, "exponential_bits": exponential_bits,
            "source_columns_checked": len(kernel.columns), "trace_norm_error_bound": str(error),
            "counter_poststate_center": [[c, i, j, str(a), str(b)] for (c, i, j), (a, b) in sorted(center.items())],
            **observations, "source_bindings": _bindings(source),
            "error_transport": "CPTP trace-norm contraction on Hermitian trial curves",
            "local_coordinate": "u=t/Delta; polynomial derivative divided by Delta",
            "source_time_coverage_complete": True, "source_counter_trace_preservation_checked": True,
            "complete_poststate_enclosure": True, "omitted_entries_covered_by_global_error": True,
            "counter_saturation_stops_atomic_dynamics": False, "solver_reexecuted_by_checker": False,
            "eigenvector_correctness_assumed": False, "physical_probability_interpretation_requires_positive_input": True,
            "input_positivity_certified_here": False, "actual_presence_programme_identified": False,
            "actual_clock_encoder_identified": False, "actual_hardware_identity_asserted": False,
            "controller_advance": False, "propagation_performed": True}


def verify_certificate(report, generator=None, initial=None, *, upstream_error=None):
    _require(type(report) is dict and report.get("schema") == SCHEMA, "fluorescence channel certificate required")
    source = source_from_record(report["raw_source"]) if generator is None else _source(generator)
    _require(source.record() == report["raw_source"], "raw fluorescence programme or counter mismatch")
    matrix = _read_input(report["initial_state"], source.record()["physical_dimension"]) if initial is None else _initial(
        initial, source.record()["physical_dimension"])
    _require(_input_record(matrix) == report["initial_state"], "original source input matrix mismatch")
    inherited = report["upstream_trace_norm_error"] if upstream_error is None else upstream_error
    _require(full.nonnegative(inherited) == full.nonnegative(report["upstream_trace_norm_error"]),
             "upstream error binding mismatch")
    expected = certify(source, matrix, report["trial_pieces"], initial_counter=report["initial_counter"],
                       upstream_error=inherited, mode_bits=report["mode_bits"],
                       coefficient_bits=report["coefficient_bits"], exponential_bits=report["exponential_bits"])
    _require(expected == report, "source fluorescence residual certificate mismatch")
    return True


def poststate(report, branch="unconditional"):
    """Return the complete source continuation center and its inherited error."""
    _require(branch in ("below_N", "at_least_N", "unconditional"), "named threshold branch required")
    observed = report[branch]
    matrix = {(i, j): dipole.ComplexRadical(full.exact(a), full.exact(b))
              for i, j, a, b in observed["poststate_center"]}
    return matrix, full.nonnegative(observed["trace_norm_error_bound"])
