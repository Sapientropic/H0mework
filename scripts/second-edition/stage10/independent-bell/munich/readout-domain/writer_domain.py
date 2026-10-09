"""Exact observer restrictions of the source writer's ceil/floor clock square.

No event-time table is admitted as a clock source.  The producer consumes full
paid local histories and admitted pair addresses, preserves all nine fields,
and eliminates the common signal-return time from fixed-clock subfamilies.
Affine hulls give exact positive period/rate domains in O(n log n).  A concrete
writer point is checked on all rows with the raw measurement's own durations.
Only scientific-frozen callers may consume the named actual observers.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import atomic_full_forward as full
import counter_mapping as counters
import fluorescence_channel as channel
import history_feed as history
import joint_clock_observation as joint_clock
import measurement_programme as measurement
import record_programme_source as writer
import uid_stride as stride


SCHEMA = "stage10-source-writer-clock-domain/v1"
POINT_SCHEMA = "stage10-source-writer-clock-point/v1"


def _require(condition, reason):
    if not condition:
        raise ValueError(reason)


def _canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _digest(value):
    return hashlib.sha256(_canonical(value).encode()).hexdigest()


def _origin(value, row):
    return [value.run, value.role, row[0], row[-1]]


def _binding(value):
    rows = stride._history(value)
    joint_clock._history(value, value.role)
    return {"run": value.run, "role": value.role, "records": len(rows),
            "complete_nine_fields_sha256": _digest(rows),
            "original_row_sequence_sha256": hashlib.sha256(b"".join(
                f"{row[0]}:{row[-1]}\n".encode("ascii") for row in rows)).hexdigest(),
            "paired_view_rows": sorted(value.paired_rows), "all_original_rows_retained": True}


def _row_clock(value, row):
    uid, unix = counters.uid(row[4]), counters.unix_ms(row[1])
    reasons = []
    if uid is None:
        reasons.append("invalid_UID_token")
    elif row[4] != str(uid):
        reasons.append("noncanonical_UID_not_emitted_by_str_int_writer")
    if unix is None:
        reasons.append("invalid_Unix_token")
    elif unix.denominator != 1:
        reasons.append("noninteger_Unix_not_emitted_by_floor_ms_writer")
    return uid, unix, {"origin": _origin(value, row), "raw_row": list(row), "reasons": reasons}


def source_bindings():
    paths = {Path(__file__).resolve(), Path(writer.__file__).resolve(), Path(measurement.__file__).resolve(),
             Path(channel.__file__).resolve(), Path(counters.__file__).resolve(), Path(history.__file__).resolve(),
             Path(joint_clock.__file__).resolve(), Path(stride.__file__).resolve(), history.PARSER_PATH}
    return [{"path": str(path.relative_to(full.ROOT)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            for path in sorted(paths)]


def _hull(lines):
    """Upper envelope, exact intersections and original-first tie ownership."""
    winners = {}
    for ordinal, (slope, intercept, origin) in enumerate(lines):
        slope, intercept = Q(slope), Q(intercept)
        old = winners.get(slope)
        if old is None or intercept > old[1]:
            winners[slope] = slope, intercept, origin, ordinal
    hull = []
    for line in sorted(winners.values(), key=lambda item: item[0]):
        start = None
        while hull:
            previous = hull[-1][1]
            start = (previous[1] - line[1]) / (line[0] - previous[0])
            if len(hull) == 1 or start > hull[-1][0]:
                break
            hull.pop()
        hull.append((start if hull else None, line))
    return hull


def _line_record(item):
    start, (slope, intercept, origin, ordinal) = item
    return {"starts_at": None if start is None else str(start), "slope": str(slope),
            "intercept": str(intercept), "origin": origin, "original_ordinal": ordinal}


def _active(hull, point, index):
    while index + 1 < len(hull) and hull[index + 1][0] <= point:
        index += 1
    return index, hull[index][1]


def affine_strip_domain(lower, upper):
    """Eliminate z from all L_i(r)<z<U_i(r), r>0; return its entire open r-domain.

    Closed lower bounds with open upper bounds have the same nonempty-domain
    condition.  Witness z is interior, so both ceil and floor cases are covered.
    """
    _require(type(lower) is list and type(upper) is list and len(lower) == len(upper), "complete affine strip inventory required")
    if not lower:
        return {"status": "unconstrained", "lower": "0", "upper": None,
                "lower_open": True, "upper_open": True, "witness": {"parameter": "1", "shift": "0"},
                "lower_hull": [], "negative_upper_hull": [], "segments": []}
    low, negative_up = _hull(lower), _hull([(-m, -b, origin) for m, b, origin in upper])
    cuts = sorted({Q(0)} | {start for hull in (low, negative_up) for start, _ in hull if start is not None and start > 0})
    lo_index, up_index, segments, feasible = 0, 0, [], []
    for index, begin in enumerate(cuts):
        end = cuts[index + 1] if index + 1 < len(cuts) else None
        lo_index, lo = _active(low, begin, lo_index)
        up_index, up = _active(negative_up, begin, up_index)
        slope, intercept = lo[0] + up[0], lo[1] + up[1]
        left, right = begin, end
        if slope > 0:
            root = -intercept / slope
            right = root if right is None else min(right, root)
        elif slope < 0:
            left = max(left, -intercept / slope)
        elif intercept >= 0:
            right = left
        valid = right is None or left < right
        if valid:
            feasible.append((left, right))
        segments.append({"lower": str(begin), "upper": None if end is None else str(end),
                         "gap_slope": str(slope), "gap_intercept": str(intercept),
                         "lower_origin": lo[2], "upper_origin": up[2],
                         "feasible_lower": str(left) if valid else None,
                         "feasible_upper": None if not valid or right is None else str(right), "feasible": valid})
    if feasible:
        begin = min(left for left, _ in feasible)
        end = None if any(right is None for _, right in feasible) else max(right for _, right in feasible)
        point = begin + 1 if end is None else (begin + end) / 2
        maximum = max(Q(m) * point + Q(b) for m, b, _ in lower)
        minimum = min(Q(m) * point + Q(b) for m, b, _ in upper)
        _require(maximum < minimum, "affine envelope did not generate an interior witness")
        witness = {"parameter": str(point), "shift": str((maximum + minimum) / 2),
                   "strict_margin": str((minimum - maximum) / 2)}
    else:
        begin = end = None
        witness = None
    return {"status": "nonempty" if feasible else "rejected", "lower": None if begin is None else str(begin),
            "upper": None if end is None else str(end), "lower_open": True, "upper_open": True,
            "witness": witness, "lower_hull": list(map(_line_record, low)),
            "negative_upper_hull": list(map(_line_record, negative_up)), "segments": segments}


def contains(domain, parameter):
    value = full.exact(parameter)
    return (domain["status"] != "rejected" and value > 0 and
            value > Q(domain["lower"]) and (domain["upper"] is None or value < Q(domain["upper"])))


def _spread(values):
    if not values:
        return {"records": 0, "min": None, "max": None, "width": None, "min_origin": None, "max_origin": None}
    smallest, largest = min(values, key=lambda item: item[0]), max(values, key=lambda item: item[0])
    return {"records": len(values), "min": str(smallest[0]), "max": str(largest[0]),
            "width": str(largest[0] - smallest[0]), "min_origin": smallest[1], "max_origin": largest[1]}


def local_period_domain(value):
    """Fixed measurement-duration projection: rho=q*P, all rows, stride1.

    Ceil and floor elimination gives t-rho*u <= z < t+1+rho-rho*u.
    A common raw measurement duration is absorbed by z, not fitted per row.
    """
    binding, lower, upper, invalid = _binding(value), [], [], []
    for row in value.observations:
        uid, unix, status = _row_clock(value, row)
        if status["reasons"]:
            invalid.append(status)
        if uid is not None and unix is not None:
            origin = _origin(value, row)
            lower.append((-uid, unix, origin))
            upper.append((1 - uid, unix + 1, origin))
    domain = affine_strip_domain(lower, upper)
    return {**binding, "parameter": "rho=milliseconds_per_unit*sample_period; UID stride=1",
            "duration_scope": "one source-fixed common measurement duration, independent of row/settings",
            "period_domain": domain, "invalid_records": invalid,
            "strict_floor_ms_model_rejected": bool(invalid) or domain["status"] == "rejected",
            "candidate_20ns_sample_period_in_domain": contains(domain, Q(1, 50000)) and not invalid,
            "unpaired_flags_and_comments_preserved": True}


def serial_window_support(first, second, admitted, *, minimum_gap_ms=40):
    """Necessary support of fresh-window serialized source plus fixed Unix writers.

    Only original same-next-admitted identities are inspected.  Two positive UID
    increments orient the fixed-latency samplers; archive order alone does not.
    A 40ms source gap forces floor-ms output differences >=floor(40ms).
    """
    first, second, _ = joint_clock._intake(first, second, admitted)
    gap = full.nonnegative(minimum_gap_ms)
    required = gap.numerator // gap.denominator
    counts = {"same_next_admitted": 0, "oriented_by_both_positive_UID": 0, "invalid_or_unoriented": 0, "contradictions": 0}
    witness, digest = None, hashlib.sha256()
    for event in joint_clock.observations(first, second, admitted):
        digest.update((_canonical(event) + "\n").encode())
        if event[4][3] is not True:
            continue
        counts["same_next_admitted"] += 1
        a, b = event[1], event[2]
        oriented = a[8] == b[8] == "positive"
        usable = all(item[6] in ("positive", "zero_clock_retained", "negative_clock_retained") for item in (a, b))
        if not oriented or not usable:
            counts["invalid_or_unoriented"] += 1
            continue
        counts["oriented_by_both_positive_UID"] += 1
        if any(Q(item[7]) < required for item in (a, b)):
            counts["contradictions"] += 1
            if witness is None:
                witness = {"origin": list(event[0]), "next_origin": list(event[3][0]),
                           "complete_joint_event": event, "local_Unix_gaps_ms": [a[7], b[7]],
                           "local_UID_increments": [a[9], b[9]], "required_floor_ms_gap": required}
    return {"family": "fresh integrated-count reset after every CEM; serialized successors; fixed Unix-rate/offset/latency",
            "minimum_physical_gap_ms": str(gap), "required_floor_ms_gap": required, **counts,
            "ordered_joint_events_sha256": digest.hexdigest(), "status": "rejected" if witness else "no_support_contradiction_found",
            "first_contradiction": witness,
            "generated_next_model": ("retain source-generated APD history; rolling/reused presence window plus physical sampling/handover latency"
                                     if witness else None),
            "raw_next_order_used_as_physical_next": False, "long_gap_used_as_ion_label": False}


def derive(first, second, admitted, *, stride_certificates, minimum_gap_ms=40):
    first, second, trials = joint_clock._intake(first, second, admitted)
    _require(type(stride_certificates) is tuple and len(stride_certificates) == 2, "both paid UID stride certificates required")
    for certificate, value in zip(stride_certificates, (first, second)):
        stride.verify_certificate(certificate, value)
    stride_one = all(item["conditional_positive_integer_stride"] == "1" for item in stride_certificates)
    uid_low, uid_up, unix_low, unix_up, uid_diffs, unix_diffs, pair_rows = [], [], [], [], [], [], []
    invalid = []
    for trial in trials:
        a, b = first.observations[trial.row_a], second.observations[trial.row_b]
        ua, ta, sa = _row_clock(first, a)
        ub, tb, sb = _row_clock(second, b)
        origin = [first.run, trial.row, _origin(first, a), _origin(second, b), trial.h, trial.a, trial.b, trial.x, trial.y]
        pair_rows.append([origin, list(a), list(b)])
        if sa["reasons"] or sb["reasons"]:
            invalid.append({"origin": origin, "local1": sa, "local2": sb})
        if ua is not None and ub is not None:
            uid_low.append((-ub, ua - 1, origin))
            uid_up.append((1 - ub, ua, origin))
            uid_diffs.append((ub - ua, origin))
        if ta is not None and tb is not None:
            unix_low.append((-ta - 1, tb, origin))
            unix_up.append((-ta, tb + 1, origin))
            unix_diffs.append((tb - ta, origin))
    uid_range, unix_range = _spread(uid_diffs), _spread(unix_diffs)
    same_uid_rejected = stride_one and uid_range["width"] is not None and Q(uid_range["width"]) >= 2
    same_unix_rejected = unix_range["width"] is not None and Q(unix_range["width"]) >= 2
    independent_period = affine_strip_domain(uid_low, uid_up)
    independent_pc = affine_strip_domain(unix_low, unix_up)
    next_clock = {}
    if same_uid_rejected:
        next_clock["sampling"] = ("independent raw periods in the generated ratio domain" if independent_period["status"] != "rejected"
                                  else "source-generated oscillator period/request-delay variation; DriftClockSource supplies period recurrence")
    if same_unix_rejected:
        next_clock["PC"] = ("independent raw PC rates in the generated ratio domain" if independent_pc["status"] != "rejected"
                            else "source-generated PC frequency/write-delay variation; DriftClockSource supplies PC phase recurrence")
    return {"schema": SCHEMA, "run": first.run, "complete_local_observers": [_binding(first), _binding(second)],
            "public_records": len(first.observations) + len(second.observations), "admitted_pairs": len(trials),
            "complete_paired_nine_fields_and_contexts_sha256": _digest(pair_rows),
            "stride_certificates_sha256": [_digest(item) for item in stride_certificates],
            "UID_stride_one_certified_in_integer_encoder_family": stride_one,
            "local_period_domains": [local_period_domain(first), local_period_domain(second)],
            "paired_UID_difference": uid_range, "paired_Unix_difference_ms": unix_range,
            "shared_period_fixed_request_latency_family_rejected": same_uid_rejected,
            "shared_Unix_rate_fixed_write_latency_family_rejected": same_unix_rejected,
            "relative_UID_phase_excursion_in_sample_periods_strictly_greater_than":
                str(max(Q(0), Q(uid_range["width"]) - 2)) if same_uid_rejected else None,
            "relative_PC_offset_excursion_ms_strictly_greater_than":
                str(max(Q(0), Q(unix_range["width"]) - 2)) if same_unix_rejected else None,
            "excursion_bound_scope": "shared-period/shared-PC-rate continuations; independent raw slopes are checked in their own generated domains",
            "independent_period_ratio_domain": independent_period,
            "independent_PC_frequency_ratio_domain": independent_pc,
            "observation_generated_next_clock_family": next_clock,
            "invalid_pair_clock_records": invalid, "serial_window_support": serial_window_support(first, second, admitted, minimum_gap_ms=minimum_gap_ms),
            "UID_family": "r=P_B/P_A; uA-r*uB-1<relative_phase< uA-r*uB+r; paid stride1",
            "Unix_family": "R=PC_rate_B/PC_rate_A; tB-R*tA-R<relative_offset<tB+1-R*tA",
            "clock_projection_only": True, "event_time_witnesses_used_as_clock_source": False,
            "free_target_clock_kernel_accepted": False, "physical_master_implies_common_UID_counter": False,
            "actual_hardware_uniquely_identified": False, "controller_advance": False, "source_bindings": source_bindings()}


def verify_domain(report, first, second, admitted, *, stride_certificates):
    _require(type(report) is dict and report.get("schema") == SCHEMA, "source writer domain certificate required")
    expected = derive(first, second, admitted, stride_certificates=stride_certificates,
                      minimum_gap_ms=report["serial_window_support"]["minimum_physical_gap_ms"])
    _require(expected == report, "source writer clock domain certificate mismatch")
    return True


@dataclass(frozen=True)
class Interval:
    lower: Q
    upper: Q
    lower_closed: bool
    upper_closed: bool


def intersect(intervals):
    _require(type(intervals) in (tuple, list) and intervals, "source time interval inventory required")
    lower, upper = max(item.lower for item in intervals), min(item.upper for item in intervals)
    closed_lower = all(item.lower_closed for item in intervals if item.lower == lower)
    closed_upper = all(item.upper_closed for item in intervals if item.upper == upper)
    if lower > upper or lower == upper and not (closed_lower and closed_upper):
        return None
    return Interval(lower, upper, closed_lower, closed_upper)


def uid_interval(encoder, uid):
    _require(type(encoder) is writer.LabEncoder and type(uid) is int and uid >= 0, "raw LabEncoder and integer source UID required")
    difference = uid - encoder.uid_origin
    if difference % encoder.uid_stride:
        return None
    index = difference // encoder.uid_stride
    top = encoder.sample_phase + index * encoder.sample_period - encoder.request_latency
    return Interval(top - encoder.sample_period, top, False, True)


def unix_interval(source, side, unix, duration):
    _require(type(source) is writer.RecordWriterSource and type(side) is int and side in (0, 1), "raw writer side required")
    unix, duration = full.exact(unix), full.nonnegative(duration)
    if unix.denominator != 1:
        return None
    encoder, rate = source.encoders[side], 1000 * source.seconds_per_unit
    begin = (unix - encoder.unix_origin_ms) / rate - duration - encoder.write_latency
    return Interval(begin, begin + 1 / rate, True, False)


def _interval_record(item):
    return None if item is None else {"lower": str(item.lower), "upper": str(item.upper),
                                     "lower_closed": item.lower_closed, "upper_closed": item.upper_closed}


def _wait_cover(source, side, uid, active_wait, sample_interval):
    encoder = source.encoders[side]
    index = (uid - encoder.uid_origin) // encoder.uid_stride
    selected_strobe = encoder.sample_phase + index * encoder.sample_period
    return Interval(selected_strobe - active_wait, sample_interval.upper, True, sample_interval.upper_closed)


def check_writer_point(raw_writer, raw_measurement, first, second, admitted):
    """Exact full-row clock projection, retaining source durations and both ceil/floor edges."""
    _require(type(raw_writer) is writer.RecordWriterSource and type(raw_measurement) is measurement.PairMeasurementSource,
             "raw writer and full pair measurement source constructors required")
    source = writer.RecordWriterSource.from_record(raw_writer.record())
    readout = measurement.PairMeasurementSource.from_record(raw_measurement.record())
    first, second, trials = joint_clock._intake(first, second, admitted)
    durations, waits = {}, {}
    for a in (0, 1):
        for b in (0, 1):
            programmes = readout.compile((a, b))
            durations[a, b] = sum((item.duration for item in programmes[0].segments), Q(0))
            wait = Q(0)
            for first_segment, second_segment in zip(programmes[0].segments, programmes[1].segments):
                segments = first_segment, second_segment
                if (any(segment.r * value for segment in segments for value in segment.fields_r.values()) or
                        any(segment.c * value for segment in segments for value in segment.fields_c.values()) or
                        any(rate for segment in segments for rate in segment.ion_rates.values())):
                    break
                wait += first_segment.duration
            waits[a, b] = wait
    failures, digest = [], hashlib.sha256()
    paired = (set(), set())
    for trial in trials:
        rows = first.observations[trial.row_a], second.observations[trial.row_b]
        intervals = []
        settings = tuple(0 if row[2] == encoder.setting_zero_token else
                         1 if row[2] == str(1 - int(encoder.setting_zero_token)) else None
                         for row, encoder in zip(rows, source.encoders))
        duration = None if None in settings else durations[settings]
        for side, (value, row) in enumerate(zip((first, second), rows)):
            paired[side].add(row[0])
            uid, unix, status = _row_clock(value, row)
            atom = None if status["reasons"] else uid_interval(source.encoders[side], uid)
            stamp = None if status["reasons"] or duration is None else unix_interval(source, side, unix, duration)
            cover = None if atom is None or duration is None else _wait_cover(source, side, uid, waits[settings], atom)
            intervals.extend((atom, stamp, cover))
        answer = None if any(item is None for item in intervals) else intersect(intervals)
        origin = [first.run, trial.row, trial.row_a, trial.row_b, trial.h, trial.a, trial.b, trial.x, trial.y]
        digest.update((_canonical([origin, rows, list(map(_interval_record, intervals)), _interval_record(answer)]) + "\n").encode())
        if answer is None:
            failures.append({"kind": "same_event_pair_clock_contradiction", "origin": origin, "rows": rows,
                             "source_intervals": list(map(_interval_record, intervals))})
    unpaired_count = 0
    for side, value in enumerate((first, second)):
        encoder = source.encoders[side]
        for row in value.observations:
            if row[0] in paired[side]:
                continue
            unpaired_count += 1
            uid, unix, status = _row_clock(value, row)
            own_setting = 0 if row[2] == encoder.setting_zero_token else 1 if row[2] == str(1 - int(encoder.setting_zero_token)) else None
            alternatives = []
            if not status["reasons"] and own_setting is not None:
                sample = uid_interval(encoder, uid)
                if sample is not None:
                    for other_setting in (0, 1):
                        key = (own_setting, other_setting) if side == 0 else (other_setting, own_setting)
                        stamp = unix_interval(source, side, unix, durations[key])
                        if stamp is not None:
                            alternatives.append(intersect((sample, stamp, _wait_cover(source, side, uid, waits[key], sample))))
            feasible = any(item is not None for item in alternatives)
            digest.update((_canonical([_origin(value, row), row, list(map(_interval_record, alternatives))]) + "\n").encode())
            if not feasible:
                failures.append({"kind": "unpaired_local_clock_contradiction", "origin": _origin(value, row), "row": row})
    return {"schema": POINT_SCHEMA, "status": "clock_projection_feasible" if not failures else "rejected",
            "raw_writer": source.record(), "raw_measurement": readout.record(),
            "measurement_durations": [[a, b, str(duration)] for (a, b), duration in sorted(durations.items())],
            "measurement_active_waits": [[a, b, str(wait)] for (a, b), wait in sorted(waits.items())],
            "complete_local_observers": [_binding(first), _binding(second)], "admitted_pairs": len(trials),
            "unpaired_rows_checked": unpaired_count, "complete_clock_interval_checks_sha256": digest.hexdigest(),
            "contradictions": len(failures), "first_contradiction": failures[0] if failures else None,
            "necessary_clock_projection_of_full_programme": True, "source_event_time_law_certified": False,
            "raw_writer_sample_wait_cover_checked": True,
            "event_time_witnesses_used_as_clock_source": False, "actual_hardware_uniquely_identified": False,
            "controller_advance": False, "source_bindings": source_bindings()}


class DriftClockSource:
    """Raw oscillator/PC clock refinement generated by recurrences, never a target table.

    Sample strobes obey T(n+1)=T(n)+P(n), P(n+1)=P(n)+drift.
    The PC phase is the integral of rate(t)=rate0+rate_drift*t.
    Positive rates are checked over the declared finite source support.
    """
    def __init__(self, raw_writer, *, period_drifts=(0, 0), pc_rate_factors=(1, 1), pc_rate_drifts=(0, 0),
                 sample_index_support=((0, 100), (0, 100)), time_support=(0, 1)):
        _require(type(raw_writer) is writer.RecordWriterSource, "raw writer seed constructor required")
        self.seed = writer.RecordWriterSource.from_record(raw_writer.record())
        for values in (period_drifts, pc_rate_factors, pc_rate_drifts, sample_index_support):
            _require(type(values) is tuple and len(values) == 2, "two raw side oscillator sources required")
        self.period_drifts = tuple(map(full.exact, period_drifts))
        self.pc_rate_factors = tuple(map(full.exact, pc_rate_factors))
        self.pc_rate_drifts = tuple(map(full.exact, pc_rate_drifts))
        _require(type(time_support) is tuple and len(time_support) == 2, "finite source clock time support required")
        self.time_support = tuple(map(full.exact, time_support))
        _require(self.time_support[0] < self.time_support[1], "positive source clock support required")
        self.index_support = sample_index_support
        for side, bounds in enumerate(sample_index_support):
            _require(type(bounds) is tuple and len(bounds) == 2 and all(type(n) is int for n in bounds) and bounds[0] <= bounds[1],
                     "finite source oscillator index support required")
            encoder = self.seed.encoders[side]
            _require(min(encoder.sample_period + self.period_drifts[side] * n for n in (bounds[0] - 1, bounds[1])) > 0,
                     "raw oscillator period must remain positive on source support")
            rate = 1000 * self.seed.seconds_per_unit * self.pc_rate_factors[side]
            _require(min(rate + self.pc_rate_drifts[side] * (t + encoder.write_latency) for t in self.time_support) > 0,
                     "raw PC clock frequency must remain positive on source support")

    def sample_time(self, side, index):
        _require(type(side) is int and side in (0, 1) and type(index) is int, "source side and strobe index required")
        encoder = self.seed.encoders[side]
        return encoder.sample_phase + encoder.sample_period * index + self.period_drifts[side] * index * (index - 1) / 2

    def sample_at(self, side, signal_return):
        _require(type(side) is int and side in (0, 1), "source clock side required")
        signal_return = full.exact(signal_return)
        _require(self.time_support[0] <= signal_return <= self.time_support[1], "signal return outside source clock support")
        encoder, (begin, end) = self.seed.encoders[side], self.index_support[side]
        request = signal_return + encoder.request_latency
        _require(self.sample_time(side, begin - 1) < request <= self.sample_time(side, end), "request outside source strobe support")
        lo, hi = begin - 1, end
        while hi - lo > 1:
            middle = (lo + hi) // 2
            if self.sample_time(side, middle) < request:
                lo = middle
            else:
                hi = middle
        uid = encoder.uid_origin + encoder.uid_stride * hi
        _require(uid >= 0, "raw oscillator generated a negative UID")
        return self.sample_time(side, hi), uid

    def unix_at(self, side, pulse_end):
        _require(type(side) is int and side in (0, 1), "source clock side required")
        pulse_end = full.exact(pulse_end)
        _require(self.time_support[0] <= pulse_end <= self.time_support[1], "pulse end outside source clock support")
        encoder = self.seed.encoders[side]
        time = pulse_end + encoder.write_latency
        phase = (encoder.unix_origin_ms + 1000 * self.seed.seconds_per_unit * self.pc_rate_factors[side] * time +
                 self.pc_rate_drifts[side] * time * time / 2)
        _require(phase >= 0, "raw PC phase generated a negative Unix timestamp")
        return phase.numerator // phase.denominator

    def record(self):
        return {"schema": "source-generated-oscillator-PC-drift-clock/v1", "raw_writer_seed": self.seed.record(),
                "period_drifts": list(map(str, self.period_drifts)), "pc_rate_factors": list(map(str, self.pc_rate_factors)),
                "pc_rate_drifts": list(map(str, self.pc_rate_drifts)), "sample_index_support": [list(item) for item in self.index_support],
                "time_support": list(map(str, self.time_support)), "strobe_law": "T(n+1)=T(n)+P(n); P(n+1)=P(n)+raw_period_drift",
                "PC_law": "phase'=raw_rate+raw_rate_drift*time; emit floor milliseconds",
                "target_clock_vector_supplied": False, "event_table_supplied": False,
                "physical_source_clock_refinement": True, "actual_clock_identified": False, "controller_advance": False}

    @classmethod
    def from_record(cls, record):
        _require(type(record) is dict and record.get("schema") == "source-generated-oscillator-PC-drift-clock/v1",
                 "registered raw drift clock source record required")
        source = cls(writer.RecordWriterSource.from_record(record["raw_writer_seed"]),
                     period_drifts=tuple(record["period_drifts"]), pc_rate_factors=tuple(record["pc_rate_factors"]),
                     pc_rate_drifts=tuple(record["pc_rate_drifts"]),
                     sample_index_support=tuple(tuple(item) for item in record["sample_index_support"]),
                     time_support=tuple(record["time_support"]))
        _require(source.record() == record, "drift clock source identity or claim scope changed")
        return source
