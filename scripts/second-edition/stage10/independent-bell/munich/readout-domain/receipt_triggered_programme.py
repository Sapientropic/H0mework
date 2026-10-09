"""Same first-receipt state measure -> local SI response -> full CEM cohorts.

The response is a fixed map in receipt-relative time, so every original time
restriction mu(B) is transported as Phi(mu(B)).  Absolute receipt time remains
in the original law.  The registered waveform family stops ionization before
each local CEM window closes; its fragment sectors then permit deferred CEM.
No UID codec, Unix oscillator, target state, or new BDF solve is supplied.
"""
from dataclasses import dataclass, replace
from fractions import Fraction as Q
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import bsm_retry_source as bsm
import cem_pair_source as cem
import certified_bsm_programme as certified
import fluorescence_channel as channel
import measurement_programme as measurement
import trap_reload_source as trap


NS = Q(1, 10**9)


def _require(condition, reason):
    if not condition:
        raise ValueError(reason)


def _canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _digest(value):
    return hashlib.sha256(_canonical(value).encode()).hexdigest()


class PublicResponseTiming:
    """One raw point in the published SI response timing intervals."""
    def __init__(self, *, seconds_per_unit, transmission_seconds=(Q(5, 2)*NS, 3717*NS),
                 CU_wait_seconds=(10740*NS, 7000*NS), RN_output_delay_seconds=(59*NS, 56*NS),
                 AOM_delay_seconds=(217*NS, 204*NS), ion_window_end_delay_seconds=(570*NS, 725*NS),
                 CEM_logic_delay_seconds=(80*NS, 84*NS), FPGA_trigger_delay_seconds=0):
        self.seconds_per_unit = full.exact(seconds_per_unit)
        self.FPGA_trigger_delay_seconds = full.nonnegative(FPGA_trigger_delay_seconds)
        _require(self.seconds_per_unit > 0, "positive common physical time unit required")
        for name, values in (("transmission_seconds", transmission_seconds), ("CU_wait_seconds", CU_wait_seconds),
                             ("RN_output_delay_seconds", RN_output_delay_seconds), ("AOM_delay_seconds", AOM_delay_seconds),
                             ("ion_window_end_delay_seconds", ion_window_end_delay_seconds), ("CEM_logic_delay_seconds", CEM_logic_delay_seconds)):
            _require(type(values) is tuple and len(values) == 2, "two side-owned primitive SI timing values required")
            setattr(self, name, tuple(map(full.nonnegative, values)))
        bounds = {"transmission_seconds": ((Q(23, 10)*NS, Q(27, 10)*NS), (3710*NS, 3724*NS)),
                  "CU_wait_seconds": ((10740*NS,)*2, (7000*NS,)*2),
                  "RN_output_delay_seconds": ((59*NS,)*2, (56*NS,)*2),
                  "AOM_delay_seconds": ((213*NS, 221*NS), (200*NS, 208*NS)),
                  "ion_window_end_delay_seconds": ((567*NS, 573*NS), (722*NS, 728*NS)),
                  "CEM_logic_delay_seconds": ((80*NS,)*2, (84*NS,)*2)}
        self.bounds = bounds
        for name, intervals in bounds.items():
            _require(all(lo <= value <= hi for value, (lo, hi) in zip(getattr(self, name), intervals)), "raw timing point outside its registered SI interval")
        durations = tuple(80*NS+a+b+c for a, b, c in zip(self.AOM_delay_seconds, self.ion_window_end_delay_seconds, self.CEM_logic_delay_seconds))
        _require(946*NS <= durations[0] <= 948*NS and 1092*NS <= durations[1] <= 1094*NS,
                 "raw timing point violates the separately measured overall SI durations")

    def events(self):
        result = []
        for side in (0, 1):
            arrival = self.FPGA_trigger_delay_seconds+self.transmission_seconds[side]
            request = arrival+self.CU_wait_seconds[side]
            output = request+self.RN_output_delay_seconds[side]
            onset = output+self.AOM_delay_seconds[side]
            close = onset+self.ion_window_end_delay_seconds[side]
            result.append({name: time/self.seconds_per_unit for name, time in (
                ("CU_receives_BSM", arrival), ("RN_request", request),
                ("earliest_RN_correlation", output-80*NS), ("RN_output", output),
                ("readout_reaches_atom", onset), ("ion_acceptance_window_closes", close),
                ("CEM_logic_deadline", close+self.CEM_logic_delay_seconds[side]))})
        return tuple(result)

    def record(self):
        events = self.events()
        return {"schema": "munich-SI-receipt-relative-response-timing/v1", "seconds_per_unit": str(self.seconds_per_unit),
                "public_source": {'url': 'https://journals.aps.org/prl/supplemental/10.1103/PhysRevLett.119.010402/BellTest-supplement.pdf',
                                  'sha256': 'bf957f62ec90082818175b2c5d06e46e140768da3a1f00f1d3c7edcf86fd13dd',
                                  'locations': ['I.C, Figure 3, pp4-6']},
                "raw_FPGA_trigger_delay_seconds": str(self.FPGA_trigger_delay_seconds),
                "FPGA_delay_identified_by_public_transmission_measurements": False,
                "raw_timing_seconds": {name: list(map(str, getattr(self, name))) for name in self.bounds},
                "SI_interval_constraints_seconds": {name: [list(map(str, interval)) for interval in intervals] for name, intervals in self.bounds.items()},
                "max_RN_age_seconds": str(80*NS), "RN_age_anchor": "earliest correlation = RN output minus 80 ns",
                "CEM_logic_time_semantics": "latest accepted-fragment logic deadline; individual detection pulses may occur earlier",
                "relative_events": [{name: str(value) for name, value in side.items()} for side in events],
                "derived_RN_request_A_minus_B_seconds": str((events[0]["RN_request"]-events[1]["RN_request"])*self.seconds_per_unit),
                "derived_measurement_begin_A_minus_B_seconds": str((events[0]["earliest_RN_correlation"]-events[1]["earliest_RN_correlation"])*self.seconds_per_unit),
                "SI_reported_central_measurement_begin_A_minus_B_seconds": str(Q(57, 2)*NS),
                "derived_measurement_duration_seconds": [str((side["CEM_logic_deadline"]-side["earliest_RN_correlation"])*self.seconds_per_unit) for side in events],
                "overall_SI_duration_intervals_seconds": [[str(946*NS), str(948*NS)], [str(1092*NS), str(1094*NS)]],
                "raw_point_is_actual_hardware_identification": False, "UID_sample_index_assumed": False,
                "Unix_clock_used_as_quantum_time": False, "controller_advance": False}

    @classmethod
    def from_record(cls, record):
        _require(type(record) is dict and record.get("schema") == "munich-SI-receipt-relative-response-timing/v1", "registered SI timing record required")
        source = cls(seconds_per_unit=record["seconds_per_unit"],
                     FPGA_trigger_delay_seconds=record['raw_FPGA_trigger_delay_seconds'],
                     **{name: tuple(values) for name, values in record["raw_timing_seconds"].items()})
        _require(source.record() == record, "SI timing source identity or interval scope changed")
        return source


def _read_history(record):
    history = trap.TrapHistory(record["old_atom_epoch"], _canonical(record["cem_receipt"]),
                              tuple(dipole.State(*state) for state in record["birth_modes"]),
                              tuple(trap.DepartedFragment(item["atom_epoch"], item["stage"], None if item["cem_receipt"] is None else _canonical(item["cem_receipt"]))
                                    for item in record["departed_fragments"]), record["occupied"])
    _require(cem.history_record(history) == record, "literal full cohort history required")
    return history


def _polynomial_piece(generator, matrix, order, mode_bits=60):
    _require(type(order) is int and 0 <= order <= 64, "finite source polynomial order in [0,64] required")
    kernel, quantum = channel.SourceKernel(generator), 1 << mode_bits
    coefficient = {}
    for (i, j), value in matrix.items():
        real, _ = full.radical_midpoint(value.real, 160)
        imag, _ = full.radical_midpoint(value.imag, 160)
        coefficient[0, i, j] = real, imag
    matrices = []
    for degree in range(order+1):
        matrices.append([[c, i, j, round(a*quantum), round(b*quantum)] for (c, i, j), (a, b) in sorted(coefficient.items())
                         if round(a*quantum) or round(b*quantum)])
        coefficient = {key: (a*generator.duration/(degree+1), b*generator.duration/(degree+1))
                       for key, (a, b) in kernel.action(coefficient).items()}
    return [{"duration": str(generator.duration), "modes": [{"lambda": [0, 0], "coefficients": matrices}]}]


@dataclass(frozen=True)
class TriggeredSnapshot:
    receipt_law: certified.ReceiptMeasure
    receipt_interval: tuple
    pattern_index: int
    herald: str
    receipt_poststate: dict
    complete_poststate: dict
    local_event_time_supports: tuple
    cem_image: cem.Image
    measurement_certificate: dict
    trap_histories: tuple
    journal: tuple


@dataclass(frozen=True)
class TriggeredInterval:
    source_record: dict
    receipt_interval: tuple
    snapshots: tuple
    global_trace_norm_error: Q
    receipt_trace_norm_error: Q
    response_local_trace_norm_error: Q


@dataclass(frozen=True)
class TriggeredTrapImage:
    branches: tuple
    global_trace_norm_error: Q
    source_interval: TriggeredInterval


class ReceiptTriggeredProgramme:
    """Fixed receipt-relative raw response on every interval of the same CP law."""
    def __init__(self, receipt_law, timing, transfer_a, transfer_b, pulses_a, pulses_b, idle_a, idle_b, *,
                 trap_histories, backgrounds, fragment_efficiencies, command_bits=240, source_journal=()):
        _require(type(receipt_law) is certified.ReceiptMeasure, "same certified first-receipt CP time/state measure required")
        self.law = certified.ReceiptMeasure(receipt_law.certificate, full.exact(receipt_law.start_time), full.nonnegative(receipt_law.inherited_error))
        self.law.interval()
        _require(type(timing) is PublicResponseTiming, "registered raw SI timing constructor required")
        self.timing = PublicResponseTiming.from_record(timing.record())
        source = bsm.BSMSource.from_record(self.law.certificate["raw_source"])
        _require(source.seconds_per_unit == self.timing.seconds_per_unit, "first receipt and response use different physical time units")
        cem._histories(trap_histories)
        _require(type(source_journal) is tuple, "immutable source journal required")
        self.histories, self.journal = trap_histories, source_journal
        self.idles = tuple(full.Segment.from_record(item.record()) for item in (idle_a, idle_b))
        self.pulses = tuple(tuple(full.Segment.from_record(item.record()) for item in values) for values in (pulses_a, pulses_b))
        events = self.timing.events()
        for side, (idle, pulses) in enumerate(zip(self.idles, self.pulses)):
            _require(pulses and all(item.duration > 0 for item in pulses), "nonempty positive-duration raw readout waveforms required")
            _require(not idle.r and not idle.c and not any(idle.ion_rates.values()), "field-off original bath required outside registered readout pulses")
            _require(all(item.gammas == idle.gammas for item in pulses), "one original natural bath must continue through each side response")
            _require(sum((item.duration for item in pulses), Q(0)) <= events[side]["ion_acceptance_window_closes"]-events[side]["readout_reaches_atom"],
                     "registered deferred-CEM waveform must stop ionization before its own acceptance window closes")
        self.boundaries, templates = self._partition()
        self.measurement = measurement.PairMeasurementSource(transfer_a, transfer_b, *templates,
                        backgrounds=backgrounds, fragment_efficiencies=fragment_efficiencies, command_bits=command_bits)

    def _partition(self):
        events = self.timing.events()
        terminal = max(side["CEM_logic_deadline"] for side in events)
        edges, local = {Q(0), terminal}, []
        for side, pulses in enumerate(self.pulses):
            start, intervals = events[side]["readout_reaches_atom"], []
            for pulse in pulses:
                end = start+pulse.duration
                edges.update((start, end))
                intervals.append((start, end, pulse))
                start = end
            local.append(intervals)
        boundaries = tuple(sorted(edges))
        templates = []
        for side in (0, 1):
            result = []
            for left, right in zip(boundaries, boundaries[1:]):
                template = next((pulse for start, end, pulse in local[side] if start <= left < end), self.idles[side])
                result.append(replace(template, duration=right-left))
            templates.append(tuple(result))
        return boundaries, tuple(templates)

    def record(self):
        return {"schema": "munich-full-state-receipt-triggered-response/v1",
                "receipt_law": {"certificate": self.law.certificate, "start_time": str(self.law.start_time), "inherited_error": str(self.law.inherited_error)},
                "timing": self.timing.record(), "raw_measurement": self.measurement.record(),
                "raw_pulses": [[item.record() for item in values] for values in self.pulses],
                "raw_idles": [item.record() for item in self.idles], "union_phase_boundaries": list(map(str, self.boundaries)),
                "trap_histories": [cem.history_record(item) for item in self.histories], "source_journal": list(self.journal),
                "receipt_time_state_measure_retained": True, "response_depends_on_absolute_receipt_time": False,
                "time_restriction_law": "for every original interval B: Phi(mu(B))",
                "CEM_deferred_scope": "each side ion bath stops before own window closes; later local CP preserves fragment sector",
                "CEM_efficiency_role": "effective accepted-fragment probability; flight/window selection is not separately identified",
                "fixed_gate_end_success_state_used": False, "UID_codec_assumed": False,
                "actual_complete_record_square_certified": False, "actual_hardware_uniquely_identified": False, "controller_advance": False}

    @classmethod
    def from_record(cls, record):
        _require(type(record) is dict and record.get("schema") == "munich-full-state-receipt-triggered-response/v1", "registered receipt-triggered raw programme required")
        law = record["receipt_law"]
        raw = measurement.PairMeasurementSource.from_record(record["raw_measurement"])
        source = cls(certified.ReceiptMeasure(law["certificate"], Q(law["start_time"]), Q(law["inherited_error"])),
                     PublicResponseTiming.from_record(record["timing"]), *raw.transfers,
                     *(tuple(full.Segment.from_record(item) for item in values) for values in record["raw_pulses"]),
                     *(full.Segment.from_record(item) for item in record["raw_idles"]),
                     trap_histories=tuple(_read_history(item) for item in record["trap_histories"]),
                     backgrounds=raw.detector.backgrounds, fragment_efficiencies=raw.detector.efficiencies,
                     command_bits=raw.command_bits, source_journal=tuple(record["source_journal"]))
        _require(source.record() == record, "receipt law, waveform, cohort or timing scope changed")
        return source

    def _trial_family(self, initial, settings, order):
        matrix, families = initial, []
        for source in self.measurement.sources(settings):
            pieces = _polynomial_piece(source, matrix, order)
            families.append(pieces)
            matrix, _ = channel.poststate(channel.certify(source, matrix, pieces))
        return families

    def interval(self, left=None, right=None, *, settings, trial_families=None, taylor_order=8):
        receipt = self.law.interval(left, right)
        interval, inherited = receipt["time_support"], receipt["global_trace_norm_error"]
        _require(trial_families is None or type(trial_families) is list and len(trial_families) == 4,
                 "all four source pattern trial families required")
        events = self.timing.events()
        supports = tuple({name: (interval[0]+offset, interval[1]+offset) for name, offset in side.items()} for side in events)
        snapshots, response_error = [], Q(0)
        for pattern, initial in enumerate(receipt["poststates"]):
            pieces = self._trial_family(initial, settings, taylor_order) if trial_families is None else trial_families[pattern]
            report = self.measurement.certify(initial, trap_histories=self.histories, settings=settings,
                                             trial_families=pieces, input_error=inherited)
            local_error = Q(report["trace_norm_error"])-inherited
            _require(local_error >= 0, "response dropped the shared first-receipt error price")
            response_error += local_error
            physical_receipt = {**report["cem_image"].receipt, "first_receipt_curve_sha256": _digest(self.law.certificate),
                                "first_receipt_interval": list(map(str, interval)), "pattern_index": pattern,
                                "receipt_relative_timing": self.timing.record(),
                                "local_physical_event_time_supports": [{name: list(map(str, bounds)) for name, bounds in side.items()} for side in supports],
                                "CEM_evaluation_deferred_with_fixed_fragment_sectors": True}
            image = replace(report["cem_image"], receipt=physical_receipt)
            journal = self.journal+({"kind": "first-receipt-triggered-response", "pattern_index": pattern,
                                    "receipt_curve_sha256": _digest(self.law.certificate), "receipt_interval": interval,
                                    "local_event_time_supports": supports, "raw_timing": self.timing.record()},)
            snapshots.append(TriggeredSnapshot(self.law, interval, pattern, bsm.PATTERNS[pattern][0], initial,
                              report["complete_poststate"], supports, image, report, self.histories, journal))
        return TriggeredInterval(self.record(), interval, tuple(snapshots), inherited+response_error, inherited, response_error)

    def verify(self, result):
        _require(type(result) is TriggeredInterval and result.source_record == self.record(), "same raw triggered interval certificate required")
        source = type(self).from_record(result.source_record)
        families = [[item["source_certificate"]["trial_pieces"] for item in snapshot.measurement_certificate["phase_certificates"]]
                    for snapshot in result.snapshots]
        settings = result.snapshots[0].measurement_certificate["settings"]
        expected = source.interval(*result.receipt_interval, settings=settings, trial_families=families)
        _require(expected == result, "receipt-triggered full interval, source, error or cohort certificate mismatch")
        return True

    def coarsen(self, result, pattern_index, *, clicks, photon_counter=0):
        self.verify(result)
        _require(type(pattern_index) is int and 0 <= pattern_index < 4, "original source pattern address required")
        snapshot = result.snapshots[pattern_index]
        return self.measurement.detector.coarsen(snapshot.cem_image, clicks=clicks, photon_counter=photon_counter)

    def next_trap_inputs(self, result, *, photon_counter=0):
        """Complete pattern/click direct sum, with the shared error paid once."""
        self.verify(result)
        branches = []
        for snapshot in result.snapshots:
            for observation in self.measurement.detector.observations(snapshot.cem_image):
                clicks = observation['clicks']
                branches.append({'pattern_index': snapshot.pattern_index, 'herald': snapshot.herald,
                                 'clicks': clicks, 'receipt_interval': result.receipt_interval,
                                 'local_event_time_supports': snapshot.local_event_time_supports,
                                 'source_journal': snapshot.journal,
                                 'trap_input': self.measurement.detector.coarsen(snapshot.cem_image,
                                                        clicks=clicks, photon_counter=photon_counter)})
        return TriggeredTrapImage(tuple(branches), result.global_trace_norm_error, result)
