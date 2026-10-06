"""Original published binomial tails from integer sufficient statistics."""

import argparse
from decimal import Decimal
from fractions import Fraction as F
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import subprocess


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[7]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def relative(path):
    return path.resolve().relative_to(REPO).as_posix()


def frozen(path):
    name = relative(path)
    commit = subprocess.check_output(
        ["git", "log", "-1", "--format=%H", "--", name], cwd=REPO, text=True).strip()
    require(bool(commit), "input lacks committed freeze: " + name)
    blob = subprocess.check_output(["git", "show", commit + ":" + name], cwd=REPO)
    require(blob == path.read_bytes(), "uncommitted input: " + name)
    return {"path": name, "commit": commit, "sha256": digest(path)}


def q_from_epsilon(epsilon):
    e = F(epsilon)
    require(0 <= e <= 1, "invalid predictability")
    return (1 + e) ** 2 / (2 * (1 + e * e))


def ceil_div(n, d):
    return -(-n // d)


def interval_receipt(lo, hi, scale):
    require(0 <= lo <= hi <= scale, "invalid probability interval")
    return {"exact_lower": str(F(lo, scale)), "exact_upper": str(F(hi, scale))}


def binomial_tail(n, h, q, digits=60):
    require(type(n) is int and type(h) is int and 0 <= h <= n, "invalid counts")
    q = F(q)
    require(0 <= q <= 1 and type(digits) is int and digits >= 1, "invalid tail inputs")
    scale = 10 ** digits
    if h == 0 or q == 1:
        return {"interval": interval_receipt(scale, scale, scale), "boundary": "certain"}
    if q == 0:
        return {"interval": interval_receipt(0, 0, scale), "boundary": "impossible"}
    a, D = q.numerator, q.denominator
    b = D - a
    k0 = max(h, min(n, (n + 1) * a // D))
    numerator = comb(n, k0) * pow(a, k0) * pow(b, n - k0)
    denominator = pow(D, n)
    start_lo = numerator * scale // denominator
    start_hi = ceil_div(numerator * scale, denominator)
    sum_lo, sum_hi = start_lo, start_hi
    up_lo, up_hi = start_lo, start_hi
    for k in range(k0, n):
        fa, fb = (n - k) * a, (k + 1) * b
        require(0 <= fa <= fb, "upward ratio not mode outward")
        up_lo = up_lo * fa // fb
        up_hi = ceil_div(up_hi * fa, fb)
        sum_lo += up_lo
        sum_hi += up_hi
    down_lo, down_hi = start_lo, start_hi
    for k in range(k0, h, -1):
        fa, fb = k * b, (n - k + 1) * a
        require(0 <= fa <= fb, "downward ratio not mode outward")
        down_lo = down_lo * fa // fb
        down_hi = ceil_div(down_hi * fa, fb)
        sum_lo += down_lo
        sum_hi += down_hi
    up, down = n - k0, k0 - h
    width_budget = 1 + up * (up + 3) // 2 + down * (down + 3) // 2
    require(sum_hi - sum_lo <= width_budget, "directed rounding budget exceeded")
    require(sum_lo <= scale, "tail lower bound exceeds probability mass")
    return {"interval": interval_receipt(sum_lo, min(sum_hi, scale), scale),
            "proof": {"n": n, "h": h, "q": str(q), "a": a, "D": D,
                      "mode_start": k0, "grid_digits": digits,
                      "first_term_formula": "C(n,k0)*a^k0*(D-a)^(n-k0)/D^n",
                      "first_term_grid": [start_lo, start_hi],
                      "upward_steps": up, "downward_steps": down,
                      "summed_terms": 1 + up + down,
                      "sum_grid_before_probability_bound": [sum_lo, sum_hi],
                      "rounding_width_budget_grid": width_budget}}


def print_interval(text):
    d = Decimal(text)
    require(d.is_finite() and 0 <= d <= 1, "invalid printed probability")
    p = F(d)
    exponent = d.as_tuple().exponent
    unit = F(10) ** exponent
    return max(F(0), p - unit / 2), min(F(1), p + unit / 2)


def compare_printed(receipt, text):
    p = receipt["interval"]
    lo, hi = F(p["exact_lower"]), F(p["exact_upper"])
    lower, upper = print_interval(text)
    if lo >= lower and hi <= upper:
        result = "PRINTED_PRECISION_COMPATIBLE"
    elif hi < lower or lo > upper:
        result = "CERTIFIED_PRINTED_TAIL_DISCREPANCY"
    else:
        result = "ROUNDING_DOMAIN_UNRESOLVED"
    return {"printed": text, "printed_rounding_domain": [str(lower), str(upper)],
            "outcome": result}


def inputs():
    bound = [HERE / "criterion.md", HERE / "sources.json", HERE / "published-inputs.json",
             HERE / "audit.py", HERE / "tests.py"]
    freezes = [frozen(p) for p in bound]
    manifest = json.loads((HERE / "sources.json").read_text())
    for item in manifest["bindings"]:
        p = REPO / item["path"]
        require(digest(p) == item["sha256"], "source sha mismatch: " + item["path"])
    text = (HERE / "criterion.md").read_text()
    block = text.split("<!-- PS-FROZEN-BEGIN -->")[1].split("<!-- PS-FROZEN-END -->")[0]
    config = json.loads(block.split("```json")[1].split("```")[0])
    data = json.loads((HERE / "published-inputs.json").read_text())
    require(data["schema"] == "p23-published-binomial-sufficient-statistics/v1", "wrong input role")
    require(len(data["runs"]) == 6 and data["pulse_counts"] == [1, 3, 5, 7], "incomplete run/window family")
    for r in data["runs"]:
        require(len(r["Nchi"]) == len(r["NS"]) == 4 and len(r["printed_p"]) == 4,
                "incomplete published row")
        require(all(len(p) == 4 for p in r["printed_p"]), "incomplete printed epsilon row")
        require(all(type(n) is int and type(h) is int and 0 <= h <= n <= r["complete_trials"]
                    for n, h in zip(r["Nchi"], r["NS"])), "invalid sufficient statistics")
    return data, config, freezes


def generate():
    data, config, freezes = inputs()
    tails, checks = {}, []

    def check(run, j, e, printed, table):
        n, h = run["Nchi"][j], run["NS"][j]
        key = f"{n}:{h}:{e}"
        if key not in tails:
            tails[key] = binomial_tail(n, h, q_from_epsilon(e), config["decimal_grid_digits"])
        checks.append({"table": table, "run": run["name"], "pulse_count": data["pulse_counts"][j],
                       "Nchi": n, "NS": h, "epsilon": e, "tail_key": key,
                       **compare_printed(tails[key], printed)})

    for run in data["runs"]:
        for i, e in enumerate(data["SI_epsilon_values"]):
            for j, printed in enumerate(run["printed_p"][i]):
                check(run, j, e, printed, "SI_S-I")
    main = data["main_Table_I"]
    run = next(r for r in data["runs"] if r["name"] == main["run"])
    for i, e in enumerate(main["epsilon_values"]):
        for j, printed in enumerate(main["printed_p"][i]):
            check(run, j, e, printed, "main_I")
    require(len(checks) == config["printed_checks"] and len(tails) == config["unique_tail_inputs"],
            "incomplete arithmetic family")
    counts = {label: sum(c["outcome"] == label for c in checks) for label in
              ["PRINTED_PRECISION_COMPATIBLE", "CERTIFIED_PRINTED_TAIL_DISCREPANCY", "ROUNDING_DOMAIN_UNRESOLVED"]}
    outcome = ("ALL_REPORTED_BINOMIAL_TAILS_MATCH_PRINTED_PRECISION" if counts["PRINTED_PRECISION_COMPATIBLE"] == len(checks)
               else "REPORTED_BINOMIAL_TAIL_DISCREPANCY" if counts["CERTIFIED_PRINTED_TAIL_DISCREPANCY"]
               else "PUBLISHED_TAIL_ARITHMETIC_UNRESOLVED")
    return {"schema": "p23-published-statistics-audit/v1", "version": config["version"],
            "outcome": outcome, "evidence_valid": True, "freezes": freezes,
            "tail_receipts": tails, "printed_checks": checks, "counts": counts,
            "source_role": "original_public_sufficient_statistics_arithmetic",
            "scope": {"conditional_memory_robust_local_null": True,
                      "arithmetic_precision_certified": not counts["ROUNDING_DOMAIN_UNRESOLVED"],
                      "raw_trial_records_read": 0, "new_multiwindow_results_read": False,
                      "execution_sequence_independently_reconstructed": False,
                      "actual_predeclaration_timestamp_certified": False,
                      "full_aggregate_substituted_for_prefix": False,
                      "source_mapping_actual_identified": False, "controller_advance": False,
                      "retrospective": True}}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "audit-ps0001.json")
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if not args.check_only:
        require(not args.output.exists(), "first scientific receipt already exists")
    report = generate()
    if args.check_only:
        require(json.loads(args.output.read_text()) == report, "stored arithmetic receipt mismatch")
    else:
        args.output.write_text(json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"outcome": report["outcome"], "counts": report["counts"],
                      "unique_tails": len(report["tail_receipts"]), "output": str(args.output)}))


if __name__ == "__main__":
    main()
