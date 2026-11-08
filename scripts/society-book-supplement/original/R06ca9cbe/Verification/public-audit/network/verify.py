"""Two independent data consumers; no producer verdict or private source input."""
from __future__ import annotations

from fractions import Fraction


def payment_scan(slot: int, evidence: dict) -> str:
    payment = evidence.get("payment")
    if not payment:
        return "insufficient"
    if (payment["slot"] != slot or payment["visit"] != 1 or payment["row"] != slot + 2
            or Fraction(payment["available"]) < 1 or Fraction(payment["start"]) < 1
            or Fraction(payment["finish"]) > 12):
        return "insufficient"
    return "verified"


def lifecycle_replay(slot: int, evidence: dict) -> str:
    state = "absent"
    admission = evidence.get("admission")
    if admission is not None and admission["ordinal"] == 0 and admission["slot"] == slot:
        state = "live"
    review = evidence.get("payment")
    if state == "live" and review is not None:
        in_window = Fraction(review["finish"]) <= 12 and 1 <= Fraction(review["start"])
        same_responsibility = review["row"] == slot + 2 and review["visit"] == 1 and review["slot"] == slot
        if in_window and same_responsibility and 1 <= Fraction(review["available"]):
            state = "fulfilled"
    return "verified" if state == "fulfilled" else "insufficient"


def verify_disclosure(record: dict) -> dict:
    if set(record) != {"cut", "actor", "query", "access", "version", "clock", "labor", "evidence"}:
        raise ValueError("PUBLIC_SCHEMA")
    if record["access"] not in {"admitted", "unauthorized", "unfunded", "expired"}:
        raise ValueError("ACCESS_ENUM")
    if any(type(record[key]) is not int or record[key] < 0 for key in ("cut", "actor", "version")) or not isinstance(record["evidence"], list):
        raise ValueError("PUBLIC_TYPES")
    if set(record["query"]) != {"slots", "fields"}:
        raise ValueError("QUERY_SCHEMA")
    Fraction(record["clock"])
    Fraction(record["labor"])
    mask, fields = record["query"]["slots"], record["query"]["fields"]
    if type(mask) is not int or not 0 <= mask < 64 or type(fields) is not int or not 0 <= fields < 4:
        raise ValueError("QUERY_MASK")
    selected = [slot for slot in range(6) if mask & (1 << slot)]
    admitted = record["access"] == "admitted"
    if not admitted:
        if record["evidence"] or Fraction(record["labor"]) != 0:
            raise ValueError("DENIAL_DISCLOSED_OR_CHARGED")
        return {"access": record["access"], "payment": [], "lifecycle": []}
    if [row["slot"] for row in record["evidence"]] != selected or Fraction(record["labor"]) != 2:
        raise ValueError("SCOPE_OR_FEE")
    if not 2 <= Fraction(record["clock"]) <= 22:
        raise ValueError("AUTHORIZATION_WINDOW")
    trace, lifecycle = [], []
    for row in record["evidence"]:
        if set(row) != {"slot", "admission", "payment"}:
            raise ValueError("EVIDENCE_SCHEMA")
        if (row["admission"] is not None) != bool(fields & 1) or (row["payment"] is not None) != bool(fields & 2):
            raise ValueError("FIELD_SCOPE")
        if row["admission"] is not None:
            if set(row["admission"]) != {"slot", "ordinal"} or any(type(value) is not int for value in row["admission"].values()):
                raise ValueError("ADMISSION_SCHEMA")
        if row["payment"] is not None:
            payment = row["payment"]
            if set(payment) != {"slot", "visit", "row", "available", "start", "finish"} or any(type(payment[key]) is not int for key in ("slot", "visit", "row")):
                raise ValueError("PAYMENT_SCHEMA")
            for key in ("available", "start", "finish"):
                Fraction(payment[key])
        trace.append(payment_scan(row["slot"], row))
        lifecycle.append(lifecycle_replay(row["slot"], row))
    return {"access": "admitted", "payment": trace, "lifecycle": lifecycle}
