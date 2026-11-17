"""Symmetric vs. asymmetric readout audit for the Munich 2017 entangled-atom Bell dataset.

Models the two-atom event-ready Bell experiment and official raw trial archives from:
  - W. Rosenfeld et al., "Event-Ready Bell Test Using Entangled Atoms Simultaneously
    Closing Detection and Locality Loopholes," Phys. Rev. Lett. 119, 010402 (2017),
    DOI: 10.1103/PhysRevLett.119.010402.
  - W. Rosenfeld et al., "Experimental data and archived website material for
    'Event-Ready Bell Test Using Entangled Atoms Simultaneously Closing Detection and
    Locality Loopholes'," Zenodo (2026), DOI: 10.5281/zenodo.22936124.

Pure Python 3 standard library only (fractions, decimal, csv, zipfile, hashlib, urllib).
"""
from __future__ import annotations

import csv
from dataclasses import dataclass
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction
import hashlib
import io
import itertools
import math
from pathlib import Path
import re
import urllib.request
from zipfile import ZipFile

ZENODO_DOI = "10.5281/zenodo.22936124"
ZENODO_RECORD_URL = "https://zenodo.org/records/22936124"
PER_RUN_THRESHOLD = Fraction(40)  # alpha = 1/40 per run; familywise alpha = 1/20 across both runs


@dataclass(frozen=True)
class ArchiveSpec:
    run: str
    filename: str
    url: str
    byte_length: int
    md5: str
    sha256: str
    local1_member: str
    local2_member: str
    pairs_member: str

    @property
    def members(self) -> tuple[str, ...]:
        return (self.local1_member, self.local2_member, self.pairs_member, "Readme.txt")


ARCHIVES: tuple[ArchiveSpec, ...] = (
    ArchiveSpec(
        run="2016-04-15",
        filename="Bell_2016-04-15.zip",
        url="https://zenodo.org/api/records/22936124/files/Bell_2016-04-15.zip/content",
        byte_length=369992,
        md5="53544819317d4dcfbe5c63e039a8aa38",
        sha256="da9e1125034e5e61a177ae1796f6362ab312bbfbc5947aeec0b09a85e67b8656",
        local1_member="Bell_2016-04-15_9_lab_1.csv",
        local2_member="Bell_2016-04-15_9_lab_2.csv",
        pairs_member="Bell_2016-04-15_9_pairs.csv",
    ),
    ArchiveSpec(
        run="2016-06-14",
        filename="Bell_2016-06-14.zip",
        url="https://zenodo.org/api/records/22936124/files/Bell_2016-06-14.zip/content",
        byte_length=391935,
        md5="030ce1a0c6c6cc7f1107e1cd608cce77",
        sha256="b24fb1693dfd14bc4d2b05df6bb23a53fc1e77b3d932c67668c2b7b9515bd84a",
        local1_member="Bell_2016-06-14_16_lab_1.csv",
        local2_member="Bell_2016-06-14_16_lab_2.csv",
        pairs_member="Bell_2016-06-14_16_pairs.csv",
    ),
)

README_SHA256 = "aec6c3be8b4f63f2fb33622665d5882cf7b566796ad152b6472276ffeca772a5"
HEADERS: dict[str, bytes] = {
    "local1": b"time (Unix time in ms);setting;result; local timestamp;Bell-state;excluded from evaluation; comment\n",
    "local2": b"time (Unix time in ms);setting;result;local timestamp;excluded from evaluation;comment;\n",
    "pairs": (
        b"timestamp lab 1 (unix time ms)\tBell-state\tsetting lab 1\tresult lab 1\t"
        b"setting lab 2\tresult lab 2\tline in lab 1 file\tline in lab 2 file\n"
    ),
}

# Simultaneous familywise 95% confidence bounds (alpha = 1/20) on readout bias
# mu = P(recorded 0) - P(recorded 1) across the full confidence domain.
SIMULTANEOUS_BIAS_BOUNDS: dict[str, dict[str, tuple[float, float]]] = {
    "2016-04-15": {
        "Alice 0": (-0.05513, 0.07853),
        "Alice 1": (-0.08480, 0.04914),
        "Bob 0": (-0.10928, 0.01755),
        "Bob 1": (-0.11514, 0.01244),
    },
    "2016-06-14": {
        "Alice 0": (-0.05716, 0.07029),
        "Alice 1": (-0.07009, 0.05900),
        "Bob 0": (-0.06534, 0.07834),
        "Bob 1": (-0.01826, 0.12410),
    },
}


@dataclass(frozen=True)
class Trial:
    row: int
    time_ms: Fraction
    h: int
    a: int
    b: int
    x: int
    y: int
    row_a: int
    row_b: int


@dataclass(frozen=True)
class AdmittedRun:
    run: str
    trials: tuple[Trial, ...]
    token_dictionaries: dict[str, list[str]]
    schema_audit: dict[str, object]


def ensure_archive(spec: ArchiveSpec, archive_dir: Path, *, allow_download: bool = True) -> Path:
    """Verify local archive bytes or download from Zenodo 22936124 and verify SHA-256."""
    archive_dir.mkdir(parents=True, exist_ok=True)
    target = archive_dir / spec.filename
    if not target.exists():
        if not allow_download:
            raise FileNotFoundError(f"Missing {target} and allow_download=False")
        urllib.request.urlretrieve(spec.url, target)
    raw = target.read_bytes()
    actual_sha = hashlib.sha256(raw).hexdigest()
    actual_md5 = hashlib.md5(raw).hexdigest()
    if len(raw) != spec.byte_length or actual_sha != spec.sha256 or actual_md5 != spec.md5:
        raise ValueError(
            f"Archive digest mismatch for {spec.filename}: "
            f"bytes={len(raw)} (expected {spec.byte_length}), sha256={actual_sha}"
        )
    return target


def _parse_timestamp(value: str) -> Fraction:
    s = value.strip()
    if not re.fullmatch(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?", s):
        raise ValueError(f"Invalid timestamp: {value!r}")
    num = Fraction(s)
    if num < 0:
        raise ValueError(f"Negative timestamp: {value!r}")
    return num


def _parse_records(raw: bytes, role: str) -> tuple[list[list[str]], int]:
    lines = raw.splitlines(keepends=True)
    if not lines or lines[0] != HEADERS[role]:
        raise ValueError(f"Header mismatch for {role}")
    delimiter = "\t" if role == "pairs" else ";"
    rows: list[list[str]] = []
    six_field_rows = 0
    for idx, line in enumerate(lines[1:], 1):
        text = line.decode("utf-8").removesuffix("\n").removesuffix("\r")
        fields = next(csv.reader([text], delimiter=delimiter, strict=True))
        if role == "local2":
            # Header has 7 semicolon-delimited fields (trailing ';'), data rows have 6 fields.
            if len(fields) == 6:
                six_field_rows += 1
                fields.append("")
            elif len(fields) == 7 and fields[-1] == "":
                pass
            else:
                raise ValueError(f"Unexpected column count {len(fields)} at {role} row {idx}")
        else:
            expected = 8 if role == "pairs" else 7
            if len(fields) != expected:
                raise ValueError(f"Unexpected column count {len(fields)} at {role} row {idx}")
        rows.append(fields)
    return rows, six_field_rows


def admit_run_bytes(run: str, raw_local1: bytes, raw_local2: bytes, raw_pairs: bytes) -> AdmittedRun:
    """Parse and cross-verify local1, local2, and pairs CSVs in original pair order."""
    local1_rows, _ = _parse_records(raw_local1, "local1")
    local2_rows, lab2_six_field_rows = _parse_records(raw_local2, "local2")
    pair_rows, _ = _parse_records(raw_pairs, "pairs")

    # Line numbers in *_pairs.csv are 0-indexed after the header line (1-based index = ref + 1).
    used_a: set[int] = set()
    used_b: set[int] = set()
    valid_flags_a: set[str] = set()
    valid_flags_b: set[str] = set()

    parsed_pairs = []
    for idx, fields in enumerate(pair_rows, 1):
        t_pair = _parse_timestamp(fields[0])
        herald, set_a, res_a, set_b, res_b = (f.strip() for f in fields[1:6])
        ref_a, ref_b = int(fields[6]), int(fields[7])
        row_a, row_b = ref_a + 1, ref_b + 1
        if not (1 <= row_a <= len(local1_rows) and 1 <= row_b <= len(local2_rows)):
            raise ValueError(f"Out-of-range local row reference at pair {idx}")
        if row_a in used_a or row_b in used_b:
            raise ValueError(f"Duplicate local row reference at pair {idx}")

        loc_a = local1_rows[row_a - 1]
        loc_b = local2_rows[row_b - 1]
        t_a = _parse_timestamp(loc_a[0])
        t_b = _parse_timestamp(loc_b[0])
        if t_pair != t_a or abs(t_a - t_b) > 100:
            raise ValueError(f"Timestamp join mismatch at pair {idx}")
        if (herald, set_a, res_a, set_b, res_b) != (loc_a[4], loc_a[1], loc_a[2], loc_b[1], loc_b[2]):
            raise ValueError(f"Setting/outcome/herald mismatch at pair {idx}")

        used_a.add(row_a)
        used_b.add(row_b)
        valid_flags_a.add(loc_a[5])
        valid_flags_b.add(loc_b[4])
        parsed_pairs.append((idx, t_pair, herald, set_a, res_a, set_b, res_b, row_a, row_b))

    if len(valid_flags_a) > 1 or len(valid_flags_b) > 1:
        raise ValueError(f"Inconsistent exclusion flags among paired events in {run}")

    roles = {
        "h": sorted({p[2] for p in parsed_pairs}),
        "a": sorted({p[3] for p in parsed_pairs}),
        "b": sorted({p[5] for p in parsed_pairs}),
        "x": sorted({p[4] for p in parsed_pairs}),
        "y": sorted({p[6] for p in parsed_pairs}),
    }
    for role_name, tokens in roles.items():
        if len(tokens) > 2:
            raise ValueError(f"Non-binary token inventory for {role_name}: {tokens}")
    encode_map = {k: {tok: bit for bit, tok in enumerate(toks)} for k, toks in roles.items()}

    trials = tuple(
        Trial(
            row=idx,
            time_ms=t_pair,
            h=encode_map["h"][herald],
            a=encode_map["a"][set_a],
            b=encode_map["b"][set_b],
            x=encode_map["x"][res_a],
            y=encode_map["y"][res_b],
            row_a=row_a,
            row_b=row_b,
        )
        for idx, t_pair, herald, set_a, res_a, set_b, res_b, row_a, row_b in parsed_pairs
    )

    unpaired_a = [r for i, r in enumerate(local1_rows, 1) if i not in used_a]
    unpaired_b = [r for i, r in enumerate(local2_rows, 1) if i not in used_b]
    flags_unpaired_a: dict[str, int] = {}
    flags_unpaired_b: dict[str, int] = {}
    for r in unpaired_a:
        flags_unpaired_a[r[5]] = flags_unpaired_a.get(r[5], 0) + 1
    for r in unpaired_b:
        flags_unpaired_b[r[4]] = flags_unpaired_b.get(r[4], 0) + 1

    schema_audit = {
        "local1_rows": len(local1_rows),
        "local2_rows": len(local2_rows),
        "pair_rows": len(trials),
        "unpaired_local1": len(unpaired_a),
        "unpaired_local2": len(unpaired_b),
        "unpaired_total": len(unpaired_a) + len(unpaired_b),
        "lab2_header_fields": len(HEADERS["local2"].decode("ascii").rstrip("\n").split(";")),
        "lab2_six_field_data_rows": lab2_six_field_rows,
        "pairs_row_index_origin": "0-based after header (1-based row = index + 1)",
        "paired_exclusion_flags": {
            "lab1": next(iter(valid_flags_a), None),
            "lab2": next(iter(valid_flags_b), None),
        },
        "unpaired_flag_counts": {"lab1": flags_unpaired_a, "lab2": flags_unpaired_b},
    }
    return AdmittedRun(run=run, trials=trials, token_dictionaries=roles, schema_audit=schema_audit)


def admit_archive(spec: ArchiveSpec, archive_dir: Path, *, allow_download: bool = True) -> AdmittedRun:
    path = ensure_archive(spec, archive_dir, allow_download=allow_download)
    with ZipFile(io.BytesIO(path.read_bytes())) as zf:
        if sorted(zf.namelist()) != sorted(spec.members):
            raise ValueError(f"Unexpected ZIP member list in {spec.filename}: {zf.namelist()}")
        readme = zf.read("Readme.txt")
        if len(readme) != 1302 or hashlib.sha256(readme).hexdigest() != README_SHA256:
            raise ValueError(f"Readme.txt digest mismatch in {spec.filename}")
        return admit_run_bytes(
            spec.run,
            zf.read(spec.local1_member),
            zf.read(spec.local2_member),
            zf.read(spec.pairs_member),
        )


# ---------------------------------------------------------------------------
# 1. Angle- & encoding-invariant symmetric-readout sequential e-process
# ---------------------------------------------------------------------------


def ideal_symmetric_joint(
    herald_plus: bool,
    gamma_a: float,
    gamma_b: float,
    visibility: float = 1.0,
    f_sym_a: float = 1.0,
    f_sym_b: float = 1.0,
) -> tuple[float, float, float, float]:
    """Four-outcome probabilities (P00, P01, P10, P11) under symmetric binary readout.

    For |Psi+/-> = (|u_x d_x> +/- |d_x u_x>) / sqrt(2), depolarizing visibility v in [0, 1],
    arbitrary equatorial/XZ spin angles (gamma_a, gamma_b), and symmetric readout fidelities
    F_0 = F_1 = f_sym on each side, the correlation is:
      C_- = -sin(gamma_a)*sin(gamma_b) - cos(gamma_a)*cos(gamma_b),
      C_+ = +sin(gamma_a)*sin(gamma_b) - cos(gamma_a)*cos(gamma_b),
    scaled by v * (2*f_sym_a - 1) * (2*f_sym_b - 1), while both single-side marginals vanish,
    giving P(0,0) = P(1,1) = (1 + c)/4 and P(0,1) = P(1,0) = (1 - c)/4.
    """
    raw_corr = (
        (1.0 if herald_plus else -1.0) * math.sin(gamma_a) * math.sin(gamma_b)
        - math.cos(gamma_a) * math.cos(gamma_b)
    )
    c = visibility * (2.0 * f_sym_a - 1.0) * (2.0 * f_sym_b - 1.0) * raw_corr
    p_same = 0.25 * (1.0 + c)
    p_diff = 0.25 * (1.0 - c)
    return (p_same, p_diff, p_diff, p_same)


class BalancedComplementProcess:
    """Exact sequential anytime-valid Jeffreys mixture e-process for symmetric readout.

    Tests the angle- and encoding-invariant null:
      P(0, 0 | past, h, a, b) = P(1, 1 | past, h, a, b),
      P(0, 1 | past, h, a, b) = P(1, 0 | past, h, a, b),
      P(x = 0 | past) = P(y = 0 | past) = 1/2,
    using exact fractions.Fraction arithmetic via E_t = (E_{J,t} + E_{A,t} + E_{B,t}) / 3.
    """

    def __init__(self) -> None:
        self.parity_counts: dict[tuple[int, int, int, int], list[int]] = {
            key: [0, 0] for key in itertools.product(range(2), repeat=4)
        }
        self.joints: dict[tuple[int, int, int], list[int]] = {
            key: [0, 0, 0, 0] for key in itertools.product(range(2), repeat=3)
        }
        self.pooled_a = [0, 0]
        self.pooled_b = [0, 0]
        self.joint_e = Fraction(1)
        self.alice_e = Fraction(1)
        self.bob_e = Fraction(1)
        self.evalue = Fraction(1)
        self.trials = 0

    def step_factors(self, h: int, a: int, b: int, x: int, y: int) -> tuple[Fraction, Fraction, Fraction]:
        parity = x ^ y
        n0, n1 = self.parity_counts[(h, a, b, parity)]
        nx = n0 if x == 0 else n1
        f_joint = Fraction(2 * nx + 1, n0 + n1 + 1)
        f_alice = Fraction(2 * self.pooled_a[x] + 1, self.pooled_a[0] + self.pooled_a[1] + 1)
        f_bob = Fraction(2 * self.pooled_b[y] + 1, self.pooled_b[0] + self.pooled_b[1] + 1)
        return f_joint, f_alice, f_bob

    def step(self, h: int, a: int, b: int, x: int, y: int) -> Fraction:
        f_joint, f_alice, f_bob = self.step_factors(h, a, b, x, y)
        self.joint_e *= f_joint
        self.alice_e *= f_alice
        self.bob_e *= f_bob
        self.evalue = (self.joint_e + self.alice_e + self.bob_e) / 3
        self.parity_counts[(h, a, b, x ^ y)][x] += 1
        self.joints[(h, a, b)][2 * x + y] += 1
        self.pooled_a[x] += 1
        self.pooled_b[y] += 1
        self.trials += 1
        return self.evalue


def score_balanced_complement(trials: tuple[Trial, ...], threshold: Fraction = PER_RUN_THRESHOLD) -> dict[str, object]:
    proc = BalancedComplementProcess()
    max_e = Fraction(1)
    max_prefix = 0
    first_crossing: int | None = None
    first_crossing_e: Fraction | None = None
    trajectory_float: list[float] = []

    for t in trials:
        val = proc.step(t.h, t.a, t.b, t.x, t.y)
        trajectory_float.append(float(val))
        if val > max_e:
            max_e = val
            max_prefix = t.row
        if first_crossing is None and val >= threshold:
            first_crossing = t.row
            first_crossing_e = val

    return {
        "trials": proc.trials,
        "rejected": first_crossing is not None,
        "first_crossing": first_crossing,
        "first_crossing_e": float(first_crossing_e) if first_crossing_e is not None else None,
        "max_prefix": max_prefix,
        "max_e": float(max_e),
        "terminal_e": float(proc.evalue),
        "components": {
            "joint": float(proc.joint_e),
            "alice": float(proc.alice_e),
            "bob": float(proc.bob_e),
        },
        "pooled_counts": {"alice": list(proc.pooled_a), "bob": list(proc.pooled_b)},
        "trajectory": trajectory_float,
    }


# ---------------------------------------------------------------------------
# 2. Asymmetric 12-parameter local readout model & 2D inverse-scale fiber
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Effect:
    """Local binary POVM readout effect (mu, u, z) with |mu| <= 1, u^2 + z^2 <= (1 - |mu|)^2.

    Here mu = F_0 - F_1 is the single-side readout bias P(0) - P(1) on a maximally mixed input,
    and sqrt(u^2 + z^2) = |F_0 + F_1 - 1| is the spin-projection contrast in the XZ plane.
    """

    mu: Fraction
    u: Fraction
    z: Fraction

    def __post_init__(self) -> None:
        object.__setattr__(self, "mu", Fraction(self.mu))
        object.__setattr__(self, "u", Fraction(self.u))
        object.__setattr__(self, "z", Fraction(self.z))
        norm_sq = self.u * self.u + self.z * self.z
        if not (-1 <= self.mu <= 1 and norm_sq <= (1 - abs(self.mu)) ** 2):
            raise ValueError(f"Effect outside legal readout cone: {self}")

    def canonical_gain_and_errors(self) -> tuple[float, float, float]:
        """Return (gain, e_0, e_1) for the canonical readout channel representation."""
        g = math.hypot(float(self.u), float(self.z))
        mu_f = float(self.mu)
        e0 = 0.5 * (1.0 - mu_f - g)
        e1 = 0.5 * (1.0 + mu_f - g)
        return g, max(0.0, e0), max(0.0, e1)


@dataclass(frozen=True)
class Instrument:
    alice: tuple[Effect, Effect]
    bob: tuple[Effect, Effect]


def _sign(bit: int) -> int:
    return 1 - 2 * bit


def source_joint(instrument: Instrument, h: int, a: int, b: int, x: int, y: int) -> Fraction:
    """Exact rational conditional probability P(x, y | h, a, b) under local asymmetric readout.

    In ASCII byte order, h = 0 corresponds to 'Psi+' and h = 1 to 'Psi-'.
    """
    eff_a = instrument.alice[a]
    eff_b = instrument.bob[b]
    corr = eff_a.mu * eff_b.mu - _sign(h) * eff_a.u * eff_b.u - eff_a.z * eff_b.z
    return Fraction(1 + _sign(x) * eff_a.mu + _sign(y) * eff_b.mu + _sign(x) * _sign(y) * corr, 4)


def full_joint_table(instrument: Instrument) -> dict[tuple[int, int, int], tuple[Fraction, Fraction, Fraction, Fraction]]:
    table: dict[tuple[int, int, int], tuple[Fraction, Fraction, Fraction, Fraction]] = {}
    for h, a, b in itertools.product((0, 1), repeat=3):
        table[(h, a, b)] = tuple(
            source_joint(instrument, h, a, b, x, y) for x, y in itertools.product((0, 1), repeat=2)
        )  # type: ignore[assignment]
    return table


def scale_fiber(instrument: Instrument, s: Fraction | str | int, t: Fraction | str | int) -> Instrument:
    """Apply the 2D inverse-scale equivalence transformation (u_A, z_A) -> (s*u_A, t*z_A),
    (u_B, z_B) -> (u_B/s, z_B/t), which preserves all 32 conditional probabilities identically.
    """
    sf, tf = Fraction(s), Fraction(t)
    if sf == 0 or tf == 0:
        raise ValueError("Scale factors s and t must be nonzero")
    alice_scaled = tuple(Effect(e.mu, sf * e.u, tf * e.z) for e in instrument.alice)
    bob_scaled = tuple(Effect(e.mu, e.u / sf, e.z / tf) for e in instrument.bob)
    return Instrument(alice=alice_scaled, bob=bob_scaled)  # type: ignore[arg-type]


# Exact 40-bit dyadic readout witnesses inside the 12D asymmetric readout cone for each run.
WITNESS_INSTRUMENTS: dict[str, Instrument] = {
    "2016-04-15": Instrument(
        alice=(
            Effect("1613133237/137438953472", "109421454503/1099511627776", "493095825207/549755813888"),
            Effect("-1228821495/68719476736", "242855158743/274877906944", "81229237849/549755813888"),
        ),
        bob=(
            Effect("-25281054879/549755813888", "22871863031/34359738368", "154380891135/274877906944"),
            Effect("-56613243853/1099511627776", "-571814216407/1099511627776", "760458139605/1099511627776"),
        ),
    ),
    "2016-06-14": Instrument(
        alice=(
            Effect("1809107211/274877906944", "-15499446543/274877906944", "951449976791/1099511627776"),
            Effect("-6113248523/1099511627776", "482081285295/549755813888", "63978544323/1099511627776"),
        ),
        bob=(
            Effect("1792329147/274877906944", "602334877055/1099511627776", "186434637091/274877906944"),
            Effect("58386834567/1099511627776", "-87927527849/137438953472", "146386984335/274877906944"),
        ),
    ),
}


def score_asymmetric_witness(trials: tuple[Trial, ...], instrument: Instrument, precision: int = 50) -> dict[str, object]:
    """Evaluate the 4-component sequential mixture e-process against an asymmetric readout point.

    Uses weights (1/6 complement, 1/6 Alice, 1/6 Bob, 1/2 full 4-outcome Dirichlet-Jeffreys)
    with directed outward Decimal interval rounding on log E_t.
    """
    table = full_joint_table(instrument)
    ctx = Context(prec=precision, Emin=-999999999, Emax=999999999)
    weights = (Fraction(1, 6), Fraction(1, 6), Fraction(1, 6), Fraction(1, 2))
    ln_cache: dict[Fraction, tuple[Decimal, Decimal]] = {}

    def ln_iv(val: Fraction) -> tuple[Decimal, Decimal]:
        if val not in ln_cache:
            with localcontext(ctx) as c:
                c.rounding = ROUND_FLOOR
                lo = (Decimal(val.numerator) / Decimal(val.denominator)).ln().next_minus(c)
                c.rounding = ROUND_CEILING
                hi = (Decimal(val.numerator) / Decimal(val.denominator)).ln().next_plus(c)
            ln_cache[val] = (lo, hi)
        return ln_cache[val]

    counts = {k: [0, 0, 0, 0] for k in itertools.product((0, 1), repeat=3)}
    comp_counts = {k + (p,): [0, 0] for k in itertools.product((0, 1), repeat=3) for p in (0, 1)}
    alice_c = [0, 0]
    bob_c = [0, 0]
    logs_lo = [Decimal(0)] * 4
    logs_hi = [Decimal(0)] * 4
    max_e_hi = 1.0
    max_prefix = 0
    trajectory_float: list[float] = []

    for t in trials:
        q = table[(t.h, t.a, t.b)]
        ev = 2 * t.x + t.y
        parity = t.x ^ t.y
        c_list = comp_counts[(t.h, t.a, t.b, parity)]
        pred_comp = Fraction(2 * c_list[t.x] + 1, 2 * (c_list[0] + c_list[1]) + 2)
        mass = q[0] + q[3] if parity == 0 else q[1] + q[2]
        marg_a = q[2 * t.x] + q[2 * t.x + 1]
        marg_b = q[t.y] + q[2 + t.y]
        cur = counts[(t.h, t.a, t.b)]

        factors = (
            pred_comp * mass / q[ev],
            Fraction(2 * alice_c[t.x] + 1, 2 * (alice_c[0] + alice_c[1]) + 2) / marg_a,
            Fraction(2 * bob_c[t.y] + 1, 2 * (bob_c[0] + bob_c[1]) + 2) / marg_b,
            Fraction(2 * cur[ev] + 1, 2 * sum(cur) + 4) / q[ev],
        )
        with localcontext(ctx) as c:
            for idx, fac in enumerate(factors):
                flo, fhi = ln_iv(fac)
                c.rounding = ROUND_FLOOR
                logs_lo[idx] += flo
                c.rounding = ROUND_CEILING
                logs_hi[idx] += fhi
            shift = max(logs_hi)
            c.rounding = ROUND_CEILING
            mix_sum_hi = Decimal(0)
            for idx, w in enumerate(weights):
                term = (logs_hi[idx] - shift).exp().next_plus(c)
                mix_sum_hi += term * Decimal(w.numerator) / Decimal(w.denominator)
            e_hi = float((shift + mix_sum_hi.ln().next_plus(c)).exp().next_plus(c))

        trajectory_float.append(e_hi)
        if e_hi > max_e_hi:
            max_e_hi = e_hi
            max_prefix = t.row

        cur[ev] += 1
        c_list[t.x] += 1
        alice_c[t.x] += 1
        bob_c[t.y] += 1

    return {
        "trials": len(trials),
        "max_e_upper": max_e_hi,
        "max_prefix": max_prefix,
        "terminal_e_upper": trajectory_float[-1] if trajectory_float else 1.0,
        "all_below_threshold": max_e_hi < float(PER_RUN_THRESHOLD),
        "trajectory": trajectory_float,
    }


def empirical_chsh_and_biases(trials: tuple[Trial, ...]) -> dict[str, object]:
    """Compute combined event-ready CHSH S and per-(station, setting) raw biases."""
    # Combine Psi- (h=1) and Psi+ (h=0) by flipping the (Psi+, a=1) correlation sign,
    # matching the event-ready CHSH combination in Rosenfeld et al., PRL 119, 010402 (2017).
    corrs: dict[tuple[int, int], float] = {}
    for a, b in itertools.product((0, 1), repeat=2):
        sub = [t for t in trials if t.a == a and t.b == b]
        s_sum = 0
        for t in sub:
            prod = 1 if t.x == t.y else -1
            if t.h == 0 and a == 1:
                prod = -prod
            s_sum += prod
        corrs[(a, b)] = s_sum / len(sub)
    chsh_s = -corrs[(0, 0)] - corrs[(0, 1)] + corrs[(1, 0)] - corrs[(1, 1)]

    biases: dict[str, dict[str, float | int]] = {}
    for side_label, s_attr, r_attr in (("Alice", "a", "x"), ("Bob", "b", "y")):
        for setting_bit in (0, 1):
            c0 = sum(1 for t in trials if getattr(t, s_attr) == setting_bit and getattr(t, r_attr) == 0)
            c1 = sum(1 for t in trials if getattr(t, s_attr) == setting_bit and getattr(t, r_attr) == 1)
            n = c0 + c1
            mu_hat = (c0 - c1) / n
            se_mu = math.sqrt(max(0.0, 1.0 - mu_hat * mu_hat) / n)
            biases[f"{side_label} {setting_bit}"] = {
                "count_0": c0,
                "count_1": c1,
                "n": n,
                "p0": c0 / n,
                "mu_hat": mu_hat,
                "se_mu": se_mu,
            }
    return {"chsh_s": chsh_s, "correlators": corrs, "biases": biases}
