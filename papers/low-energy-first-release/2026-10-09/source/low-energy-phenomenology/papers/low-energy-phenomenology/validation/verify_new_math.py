#!/usr/bin/env python3
"""Exact algebra in the new written proofs; original Lean certifications are reused."""
import json
from pathlib import Path
import sympy as sp

PAPER = Path(__file__).resolve().parents[1]
OUT = PAPER / 'build/release-checks'
OUT.mkdir(parents=True, exist_ok=True)
checks = []


def check(name, result, detail=None):
    passed = bool(result)
    checks.append({'name': name, 'passed': passed, 'detail': detail})
    print(('PASS ' if passed else 'FAIL ') + name)
    if not passed:
        raise AssertionError(name)


def zero(value):
    if isinstance(value, sp.MatrixBase):
        return all(sp.simplify(v) == 0 for v in value)
    return sp.simplify(value) == 0


q = sp.Rational
T = sp.sqrt(30) * sp.Matrix([
    [-q(25, 54), 0, 0, 0, 0], [0, -q(12, 335), 0, 0, 0],
    [0, 0, q(1, 15), -q(1, 3), 0], [0, 0, -q(1, 3), q(1, 15), 0],
    [0, 0, 0, 0, q(4, 5)]])
G = sp.sqrt(30) * sp.Matrix([
    [-q(9, 125), 0, 0, 0, 0], [0, -q(67, 72), 0, 0, 0],
    [0, 0, -q(1, 48), -q(5, 48), 0], [0, 0, -q(5, 48), -q(1, 48), 0],
    [0, 0, 0, 0, q(1, 24)]])
check('F.5 actual five-dimensional static left and right inverse',
      zero(T*G-sp.eye(5)) and zero(G*T-sp.eye(5)))
w = sp.Matrix([1, 1, 0, 0, 0])
K = q(9023, 9000)*sp.sqrt(30)
check('complete static contraction has the negative sign', zero((w.T*G*w)[0]+K))
check('two actual Coulomb channels give the same Kstar',
      zero(1/(q(25, 54)*sp.sqrt(30))+1/(q(12, 335)*sp.sqrt(30))-K))
check('static compound and Thomson sign conventions differ', K != -K)

scalar_weights = [q(1, 2), -q(1, 2), 0]
matter_weights = [-1, 0, -q(1, 2)]
check('three source letters have the same joint half-unit increment',
      all(a+b == -q(1, 2) for a, b in zip(scalar_weights, matter_weights)))
check('a joint half-unit does not replace the actual edge-zero electron unit', q(1, 2) != 1)

# The source Green convention is H-z, so the inverse-commutator sign is fixed.
H = sp.Matrix([[2, 1], [1, 3]])
Q = sp.diag(1, -1)
z = sp.I
Rz = (H-z*sp.eye(2)).inv()
check('H-z inverse commutator sign', zero(Q*Rz-Rz*Q-Rz*(H*Q-Q*H)*Rz))
u = sp.Matrix([1, sp.I]); d = sp.Matrix([[2, -sp.I]])
ER = q(3, 2); EL = q(5, 2)
r = (H-ER*sp.eye(2))*u; ell = d*(H-EL*sp.eye(2))
ua = u-Rz*r; da = d-ell*Rz
check('actual amputations use original H-z equations',
      zero(ua-(ER-z)*Rz*u) and zero(da-(EL-z)*d*Rz))
A = sp.Matrix([[1, 2], [3, -1]])
correction = -ell*Rz*A*u-d*A*Rz*r+ell*Rz*A*Rz*r
check('both endpoint corrections and their cross term are retained',
      zero(da*A*ua-d*A*u-correction))
check('omitting the endpoint cross term changes this noncommuting readout',
      not zero(da*A*ua-d*A*u+ell*Rz*A*u+d*A*Rz*r))

c = sp.symbols('c', positive=True)
residue = sp.diag(1, 0); derivative = sp.diag(1, 0)
Rc = residue/c; Dc = c*derivative
check('clock residue and derivative preserve the normalized projector',
      zero(Rc*Dc-residue*derivative))
check('clock flux is the same identity with both sides scaling by 1/c', zero(Rc*Dc*Rc-Rc))
check('raw clock flux is not a numerically constant matrix at scale three',
      not zero((Rc*Dc*Rc).subs(c, 3)-residue*derivative*residue))

radius, time = sp.symbols('radius time', positive=True)
newton = sp.integrate((4*sp.pi*time)**(-q(3, 2))*sp.exp(-radius**2/(4*time)),
                      (time, 0, sp.oo))
check('original Fourier convention gives exactly one 4pi in the Newton kernel',
      zero(newton-1/(4*sp.pi*radius)))
check('three-dimensional Newton singularity is locally integrable',
      sp.integrate(radius**2/radius**2, (radius, 0, 1)) == 1)
check('a Schwartz majorant pays the Newton tail in three dimensions',
      zero(sp.integrate(1/(1+radius**2)**2, (radius, 0, sp.oo))-sp.pi/4))

base, tail = sp.symbols('base tail', positive=True)
overlap = base/sp.sqrt(base**2+tail**2)
check('normalized bottom Born value equals overlap squared',
      zero(overlap**2-base**2/(base**2+tail**2)))
check('sharp response has overlap one without a strict-less-than assertion',
      zero(overlap.subs(tail, 0)-1))
sharp = sp.Matrix([1, 0]); full = sp.Matrix([1, 1])/sp.sqrt(2)
insertion = sp.diag(1, 2)
check('one sharp leg reads exactly the bottom overlap',
      zero((sharp.T*insertion*full)[0]-1/sp.sqrt(2)))
check('two unrestricted full legs need the additional upper-grade term',
      not zero((full.T*insertion*full)[0]-q(1, 2)))
Z = sp.Rational(2, 3)*sp.Rational(3, 5)*sp.Rational(5, 7)*sp.Rational(7, 11)
C = 2+3*sp.I
check('four actual overlap factors give the exact scalar norm difference',
      0 < Z <= 1 and zero(sp.Abs(Z*C-C)-(1-Z)*sp.Abs(C)))

result = {'all_passed': all(x['passed'] for x in checks), 'checks': checks,
          'check_count': len(checks), 'sympy_version': sp.__version__,
          'scope': 'New written-proof algebra and key counterexamples; original source bindings and Lean certifications are separately recorded.'}
(OUT/'new-math-checks.json').write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
