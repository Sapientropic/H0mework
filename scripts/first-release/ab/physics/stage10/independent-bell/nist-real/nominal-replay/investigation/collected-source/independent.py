"""Independent direct amplitude consumer; does not import model.py or its outputs."""
import cmath
import json
import math
from pathlib import Path


def specification():
    text = Path(__file__).with_name("criterion.md").read_text()
    section = text[text.index("<!-- CS-FROZEN-BEGIN -->"):text.index("<!-- CS-FROZEN-END -->")]
    return json.loads(section[section.index("{"):section.rindex("}")+1])


def full_state(recipe, r, phase_pi):
    norm = math.hypot(1, r)
    return state_from_preparation(recipe, (1/norm, r/norm*cmath.exp(1j*math.pi*phase_pi)))


def state_from_preparation(recipe, preparation):
    """Basis (A port, A pol, A bin, B port, B pol, B bin); port 0 is collected."""
    state = {}
    for pol, label in enumerate(("H", "V")):
        for i, row in enumerate(recipe["power_"+label]):
            for j, power in enumerate(row):
                modes = recipe.get("source_mode_phase_"+label)
                phase = modes[i][j] if modes else 0
                z = math.sqrt(power)*cmath.exp(1j*math.pi*phase)*preparation[pol]
                for a in (0, 1):
                    for b in (0, 1):
                        amplitude = z
                        for side, index, port in (("A", i, a), ("B", j, b)):
                            beta = math.pi*recipe["beta_"+side][pol][index]
                            phases = recipe.get("phase_"+side)
                            angle = math.pi*phases[pol][index] if phases else 0
                            fraction = recipe["beta_"+side][pol][index] % 2
                            sine, cosine = math.sin(beta), math.cos(beta)
                            if fraction in (0, 0.5, 1, 1.5):
                                sine, cosine = ((0, 1), (1, 0), (0, -1), (-1, 0))[int(2*fraction)]
                            amplitude *= (cosine*cmath.exp(1j*angle) if port == 0 else sine)
                        state[(a, pol, i, b, pol, j)] = amplitude
    return state


def density_objects(state):
    out = {"AB": [[0j]*4 for _ in range(4)],
           "A": [[0j]*2 for _ in range(2)], "B": [[0j]*2 for _ in range(2)]}
    # Explicit trace equalities include the partner's polarization even in its lost port.
    for x, z in state.items():
        for y, w in state.items():
            zw = z*w.conjugate()
            if x[0] == y[0] == x[3] == y[3] == 0 and (x[2], x[5]) == (y[2], y[5]):
                out["AB"][2*x[1]+x[4]][2*y[1]+y[4]] += zw
            if x[0] == y[0] == 0 and (x[2], x[3:]) == (y[2], y[3:]):
                out["A"][x[1]][y[1]] += zw
            if x[3] == y[3] == 0 and (x[:3], x[5]) == (y[:3], y[5]):
                out["B"][x[4]][y[4]] += zw
    return out


def amplitude_read(state, a, b, Q, uA, uB):
    # Group amplitudes by surviving orthogonal labels after each optical analyzer.
    groups = [{}, {}, {}]
    for (aport, apol, ai, bport, bpol, bi), z in state.items():
        overlaps = []
        for setting, p in ((a, apol), (b, bpol)):
            angle, phase = (math.pi*x for x in setting)
            overlaps.append(math.cos(angle) if p == 0 else
                            math.sin(angle)*cmath.exp(-1j*phase))
        terms = []
        if aport == 0:
            terms.append((0, (ai, bport, bpol, bi), z*overlaps[0]))
        if bport == 0:
            terms.append((1, (aport, apol, ai, bi), z*overlaps[1]))
        if aport == bport == 0:
            terms.append((2, (ai, bi), z*overlaps[0]*overlaps[1]))
        for k, label, v in terms:
            groups[k][label] = groups[k].get(label, 0j)+v
    probabilities = [sum(abs(z)**2 for z in group.values()) for group in groups]
    return dict(zip(("sA", "sB", "j"),
                    (Q*uA*probabilities[0], Q*uB*probabilities[1], Q*uA*uB*probabilities[2])))


def serial(value):
    if isinstance(value, complex):
        return [value.real, value.imag]
    if isinstance(value, dict):
        return {k: serial(v) for k, v in value.items()}
    if isinstance(value, list):
        return [serial(v) for v in value]
    return value


def generate(spec=None):
    spec = specification() if spec is None else spec
    rows = []
    for recipe in spec["fixtures"]:
        for r in spec["r_values"]:
            for phase in spec["source_phase_pi"]:
                state = full_state(recipe, r, phase)
                rows.append({"name": recipe["name"], "r": r, "phase_pi": phase,
                             "objects": serial(density_objects(state)),
                             "reads": [amplitude_read(state, a, b, **spec["rates"])
                                       for a in spec["analyzers"] for b in spec["analyzers"]]})
    return rows


if __name__ == "__main__":
    print(json.dumps(generate(), sort_keys=True, allow_nan=False))
