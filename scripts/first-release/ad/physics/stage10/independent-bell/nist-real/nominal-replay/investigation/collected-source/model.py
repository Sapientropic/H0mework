"""Finite optical source -> collection branches -> non-normalized polarization objects.

No empirical target, effective probability, or prepared output channel is an input.
S1--S5 and units are fixed in criterion.md. Python uses H-first throughout.
"""
from __future__ import annotations

import cmath
import json
import math
from pathlib import Path


def frozen():
    text = Path(__file__).with_name("criterion.md").read_text()
    body = text.split("<!-- CS-FROZEN-BEGIN -->")[1].split("<!-- CS-FROZEN-END -->")[0]
    return json.loads(body.split("```json")[1].split("```")[0])


def unit_interval(value):
    if not math.isfinite(value) or not 0 <= value <= 1:
        raise ValueError("expected finite probability in [0,1]")
    return value


def zero_matrix(n):
    return [[0j for _ in range(n)] for _ in range(n)]


def sincos_pi(x):
    exact = {0.0: (0.0, 1.0), 0.5: (1.0, 0.0), 1.0: (0.0, -1.0), 1.5: (-1.0, 0.0)}
    return exact[x % 2] if x % 2 in exact else (math.sin(math.pi*x), math.cos(math.pi*x))


def analyzer(theta_pi, phase_pi=0.0):
    if not all(math.isfinite(x) for x in (theta_pi, phase_pi)):
        raise ValueError("nonfinite analyzer")
    return (complex(math.cos(math.pi*theta_pi)),
            cmath.exp(1j*math.pi*phase_pi)*math.sin(math.pi*theta_pi))


def expectation(matrix, vector):
    z = sum(vector[i].conjugate()*matrix[i][j]*vector[j]
            for i in range(len(vector)) for j in range(len(vector)))
    if abs(z.imag) > 1e-12:
        raise ArithmeticError("non-Hermitian expectation")
    return z.real


class OpticalSource:
    def __init__(self, recipe):
        self.recipe = recipe
        self.na = len(recipe["power_H"])
        self.nb = len(recipe["power_H"][0]) if self.na else 0
        if self.na == 0 or self.nb == 0:
            raise ValueError("empty source")
        self.f = []
        for p in ("H", "V"):
            powers = recipe["power_"+p]
            phases = recipe.get("source_mode_phase_"+p,
                                [[0]*self.nb for _ in range(self.na)])
            if (len(powers) != self.na or len(phases) != self.na
                    or any(len(row) != self.nb for row in powers+phases)):
                raise ValueError("inconsistent source shape")
            if abs(sum(sum(row) for row in powers)-1) > 1e-12:
                raise ValueError("source path must be normalized")
            self.f.append([[math.sqrt(unit_interval(powers[i][j]))*
                            cmath.exp(1j*math.pi*phases[i][j])
                            for j in range(self.nb)] for i in range(self.na)])
            if any(not math.isfinite(x) for row in phases for x in row):
                raise ValueError("nonfinite source phase")
        self.optics = []
        for side, n in (("A", self.na), ("B", self.nb)):
            beta = recipe["beta_"+side]
            phase = recipe.get("phase_"+side, [[0]*n for _ in range(2)])
            if len(beta) != 2 or len(phase) != 2 or any(len(row) != n for row in beta+phase):
                raise ValueError("inconsistent optical shape")
            if any(not math.isfinite(x) for row in beta+phase for x in row):
                raise ValueError("nonfinite optical input")
            # Both outputs retain polarization and spectral label; the lost port is not erased.
            self.optics.append([[(cmath.exp(1j*math.pi*phase[p][i])*sincos_pi(beta[p][i])[1],
                                   complex(sincos_pi(beta[p][i])[0]))
                                  for i in range(n)] for p in range(2)])

    def branch(self, p, a_lost, b_lost):
        return [self.f[p][i][j]*self.optics[0][p][i][a_lost]*self.optics[1][p][j][b_lost]
                for i in range(self.na) for j in range(self.nb)]

    def statistics(self):
        powers = [[[math.fsum(abs(z)**2 for z in self.branch(p, a, b))
                    for b in range(2)] for a in range(2)] for p in range(2)]
        h, v = self.branch(0, 0, 0), self.branch(1, 0, 0)
        return {"A": [powers[p][0][0]+powers[p][0][1] for p in range(2)],
                "B": [powers[p][0][0]+powers[p][1][0] for p in range(2)],
                "C": [powers[p][0][0] for p in range(2)],
                "Z": sum(x*y.conjugate() for x, y in zip(h, v)),
                "branches": powers}

    def objects(self, r, phase_pi=0.0):
        if not math.isfinite(r) or r < 0 or not math.isfinite(phase_pi):
            raise ValueError("invalid preparation")
        # hypot avoids overflow for large finite preparation ratios.
        n = math.hypot(1, r)
        return self.objects_from_preparation(1/n, r/n*cmath.exp(1j*math.pi*phase_pi))

    def objects_from_preparation(self, h, v):
        """Normalized source amplitudes, including the two exact pure-path endpoints."""
        c = (complex(h), complex(v))
        if (any(not math.isfinite(z.real) or not math.isfinite(z.imag) for z in c)
                or abs(sum(abs(z)**2 for z in c)-1) > 1e-12):
            raise ValueError("preparation amplitudes must be finite and normalized")
        stats = self.statistics()
        ab, a, b = zero_matrix(4), zero_matrix(2), zero_matrix(2)
        for p, k in enumerate((0, 3)):
            ab[k][k] = complex(abs(c[p])**2*stats["C"][p])
            a[p][p] = complex(abs(c[p])**2*stats["A"][p])
            b[p][p] = complex(abs(c[p])**2*stats["B"][p])
        ab[0][3] = c[0]*c[1].conjugate()*stats["Z"]
        ab[3][0] = ab[0][3].conjugate()
        return {"AB": ab, "A": a, "B": b}

    def read(self, r, phase_pi, a, b, Q=1.0, uA=1.0, uB=1.0):
        Q, uA, uB = map(unit_interval, (Q, uA, uB))
        o = self.objects(r, phase_pi)
        va, vb = analyzer(*a), analyzer(*b)
        return {"sA": Q*uA*expectation(o["A"], va),
                "sB": Q*uB*expectation(o["B"], vb),
                "j": Q*uA*uB*expectation(o["AB"], [x*y for x in va for y in vb])}

    def rates(self, r, Q, uA, uB):
        Q, uA, uB = map(unit_interval, (Q, uA, uB))
        o = self.objects(r)
        pa = sum(o["A"][i][i].real for i in range(2))
        pb = sum(o["B"][i][i].real for i in range(2))
        pp = sum(o["AB"][i][i].real for i in range(4))
        sa, sb, j = Q*uA*pa, Q*uB*pb, Q*uA*uB*pp
        return {"Pa": pa, "Pb": pb, "Pp": pp, "Q": Q, "joint_pair_rate": Q*pp,
                "sA": sa, "sB": sb, "j": j,
                "etaA_K": j/sb if sb else None, "etaB_K": j/sa if sa else None,
                "q_eff": sa*sb/j if j else None,
                "eta_c": pp/math.sqrt(pa*pb) if pa*pb else None}

    def collected_shape(self, r):
        if not math.isfinite(r) or r < 0:
            raise ValueError("invalid preparation")
        s = self.statistics()
        h, v = s["C"]
        return {"r_col_population": r*math.sqrt(v/h) if h else None,
                "coherence": s["Z"]/math.sqrt(h*v) if h*v else None,
                "A_proportional_residual": s["A"][0]*v-s["A"][1]*h,
                "B_proportional_residual": s["B"][0]*v-s["B"][1]*h}


def click_table(read):
    return (read["j"], read["sA"]-read["j"], read["sB"]-read["j"],
            1-read["sA"]-read["sB"]+read["j"])


def encode(value):
    if isinstance(value, complex):
        return [value.real, value.imag]
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def family_report(spec=None):
    spec = frozen() if spec is None else spec
    rows = []
    for recipe in spec["fixtures"]:
        source = OpticalSource(recipe)
        for r in spec["r_values"]:
            for phase in spec["source_phase_pi"]:
                reads = [source.read(r, phase, a, b, **spec["rates"])
                         for a in spec["analyzers"] for b in spec["analyzers"]]
                rows.append({"name": recipe["name"], "r": r, "phase_pi": phase,
                             "objects": encode(source.objects(r, phase)), "reads": reads})
    return rows


if __name__ == "__main__":
    print(json.dumps(family_report(), sort_keys=True, allow_nan=False))
