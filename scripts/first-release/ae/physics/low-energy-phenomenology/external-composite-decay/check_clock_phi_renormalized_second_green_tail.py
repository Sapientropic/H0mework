from fractions import Fraction as F
from itertools import product
import json

checks = {}
negative = {name: 0 for name in [
    "omit_H0k_square", "omit_second_tester_square", "omit_first_tester_square",
    "wrong_mu_second_response", "wrong_Young_allocation", "omit_price_coefficient",
]}

def ck(name, value):
    assert value, name
    assert name not in checks, name
    checks[name] = True

mus = [F(1, 11), F(1), F(7, 3)]
epsilons = [F(1, 13), F(1), F(9, 2)]
# pi is a positive common symbolic price scale: the identities below hold for
# every such scale. Lean separately owns the original all-frequency pi mass.
price_scales = [F(1, 2), F(22, 7), F(5)]
vectors = [
    (F(), F(), F(), F(), F(), F()),
    (F(2), F(1, 3), F(1), F(2), F(1, 4), F(3)),
    (F(1, 5), F(9), F(7), F(1, 2), F(4), F(1)),
    (F(1), F(50), F(), F(), F(), F()),
    (F(), F(), F(8), F(3), F(), F()),
    (F(), F(), F(), F(), F(5), F(11)),
]
masses = [(F(), F()), (F(2, 3), F(7)), (F(13), F(1, 4))]
for mu, epsilon, scale, mass, vector in product(mus, epsilons, price_scales, masses, vectors):
    m0, m1 = mass
    a, b, x0, x1, y0, y1 = vector
    eta = epsilon * mu / (8 * scale)
    c0, c1, c2 = scale / mu, scale / (4 * eta * mu ** 3), scale / (4 * eta * mu)
    square_sum = sum(v * v for v in vector)
    actual = c0 * (4 * eta + a * b + mu * a * a) + c1 * (x0*x0*m0+x1*x1*m1) + c2 * (y0*y0*m0+y1*y1*m1)
    coefficient = c0*(1+mu)+(c1+c2)*(m0+m1)
    tag = f"mu={mu};e={epsilon};p={scale};m={mass};v={vector}"
    ck(tag + "/whole_six_norm_envelope", actual <= 4*c0*eta+coefficient*square_sum)
    ck(tag + "/eta_half_price", 4*c0*eta == epsilon/2)
    delta = epsilon/(2*(coefficient+1))
    ck(tag + "/common_delta_positive", delta > 0 and coefficient >= 0)
    ck(tag + "/generated_common_delta_payment", coefficient*delta <= epsilon/2)
    ck(tag + "/zero_fixed_sources_keep_Young_floor", square_sum != 0 or actual == epsilon/2)
    for name, removed in [
        ("omit_H0k_square", b*b),
        ("omit_second_tester_square", x0*x0+x1*x1),
        ("omit_first_tester_square", y0*y0+y1*y1),
    ]:
        negative[name] += actual > 4*c0*eta+coefficient*(square_sum-removed)
    wrong_actual = c0*(4*eta+a*b+mu*a*a)+scale/(4*eta*mu**2)*(x0*x0*m0+x1*x1*m1)+c2*(y0*y0*m0+y1*y1*m1)
    negative["wrong_mu_second_response"] += actual != wrong_actual
    wrong_eta = epsilon*mu/(4*scale)
    negative["wrong_Young_allocation"] += 4*c0*wrong_eta+coefficient*delta > epsilon
    wrong_delta = epsilon/2
    negative["omit_price_coefficient"] += 4*c0*eta+coefficient*wrong_delta > epsilon
assert all(n > 0 for n in negative.values()), negative
from pathlib import Path
import hashlib
import re as regex
BASE = Path(__file__).resolve().parent
SOURCE = BASE / 'SourceClockPhiRenormalizedSecondGreenTail.lean'
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(SOURCE) == 'bc34f1dbbaf136705d5a2c54fd01363f8f2b1c886df5225ed03f90ecc84d9522'
INPUT_SHA = {'SourceClockPhiRenormalizedSecondGreen.lean': '70d028b8ff713d8717100d27fb03cba7832f878fd775350decd99dc13f3cfc19', 'SourceClockPhiRenormalizedSecondGreenBudget.lean': '694bf1e47e17cdd1997a6ae6fefbd2d0e66eddac85b9db5fbdbbbfd7a04da97d', 'SourceClockPhiFixedSecondGreenTail.lean': '557f9770ad15aecbda7f82de0801800286dd314c8082427b24b7d18e26764191'}
for name, digest in INPUT_SHA.items():
    assert sha(BASE/name) == digest, name
flat = regex.sub(r'\s+', ' ', SOURCE.read_text())
role_count = len(checks)
def token(name, *parts):
    ck(name, all(part in flat for part in parts))
token('original_generated_renormalized_endpoint', 'renormalizedEndpoint m ell F (actualFrequency advanced μ w)')
token('actual_full_fixed_hamiltonian_column', 'embed (diagonalAction (fixedColumn m ell g))')
token('both_original_fixed_testers', 'fixedSecondTester m ell g i', 'fixedFirstTester m ell g i')
token('whole_H0_squared_source_mass', 'GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep (inputSeed g i))')
token('exact_second_and_first_response_mu_scales', 'Real.pi/(4*η*μ^3)', 'Real.pi/(4*η*μ)')
token('source_six_norm_tail_consumed', 'actual_fixed_second_green_endpoint_common_tail g (ε/(2*(C+1)))')
token('source_spectral_budget_consumed', 'actual_renormalized_fixed_frequency_budget μ hμ g η hη')
token('internally_generated_young_allocation', 'let η:=ε*μ/(8*Real.pi)', 'have hηε:4*Real.pi/μ*η=ε/2')
token('internally_generated_fixed_price_coefficient', 'let C:=fixedPriceCoefficient μ η g', 'coefficient_nonnegative μ η hμ hη g')
token('absolute_all_frequency_integral_not_signed_bound', '∫⁻w : ℝ,ENNReal.ofReal (|renormalizedEndpoint', 'ENNReal.ofReal ε')
token('common_N_prior_to_cutoff_and_causal_legs', '∃N : ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter : Filter Index),∀advanced : Bool')
token('arbitrary_positive_mu_and_epsilon_no_cap_premise', '(μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (ε : ℝ) (hε : 0 < ε)')
token('actual_frequency_positive_mu_not_gap', 'actualFrequency advanced μ w', 'frequency_nonreal advanced μ hμ w')
token('six_norm_envelope_actual_internal_use', 'have h:=six_price_bound', 'have hb:=actual_fixed_price_bound μ η hμ hη m ell g')
report = {'module': 'SourceClockPhiRenormalizedSecondGreenTail', 'all_pass': True,
    'count': len(checks), 'role_arithmetic_count': role_count, 'checks': checks,
    'negative_witness_counts': negative,
    'effective_negative_controls': {name: n > 0 for name, n in negative.items()},
    'source_sha256': sha(SOURCE), 'script_sha256': sha(__file__),
    'input_sha256': {name: sha(BASE/name) for name in INPUT_SHA}, 'helper_sha256': {},
    'scope': 'Exact symbolic positive spectral-mass scale, literal six fixed source norms, arbitrary positive mu, and internally generated eta/delta allocation. No numeric pi integration or fixed-norm convergence is assumed by these arithmetic controls; the Lean source consumer owns convergence and cofinal F.'}
(BASE/'clock-phi-renormalized-second-green-tail-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'controls': len(checks), 'arithmetic': role_count, 'negative': len(negative),
    'inputs': len(INPUT_SHA), 'helpers': 0, 'all_pass': True}))
