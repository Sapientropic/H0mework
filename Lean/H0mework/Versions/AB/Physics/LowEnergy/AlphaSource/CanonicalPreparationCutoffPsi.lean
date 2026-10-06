import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockInverseJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCutoffBudget
open CanonicalPreparationCutoff Polynomial
open scoped BigOperators ContDiff Topology

def psiPolynomial (r : ℕ) : ℝ[X] :=
  Nat.rec 1 (fun _ P => X^2*(P-Polynomial.derivative P)) r

def psiBound (r : ℕ) : ℝ :=
  ∑ d∈(psiPolynomial r).support,|(psiPolynomial r).coeff d| *(d : ℝ)^d

theorem psiPolynomial_zero : psiPolynomial 0=1 := rfl
theorem psiPolynomial_next (r : ℕ) :
    psiPolynomial (r+1)=X^2*(psiPolynomial r-Polynomial.derivative (psiPolynomial r)) := rfl

theorem actual_psi_derivative (r : ℕ) :
    iteratedDeriv r expNegInvGlue=fun t => (psiPolynomial r).eval t⁻¹*expNegInvGlue t := by
  induction r with
  | zero => simp [psiPolynomial]
  | succ r ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    exact (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (psiPolynomial r) t).deriv

theorem monomial_exp_bound (u : ℝ) (nonnegative : 0≤ u) (d : ℕ) :
    u^d*Real.exp (-u)≤(d : ℝ)^d := by
  cases d with
  | zero => simpa using (Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative))
  | succ d =>
    let n : ℝ := (d+1 : ℕ)
    have positive : 0<n := by dsimp [n]; positivity
    have elementary := Real.mul_exp_neg_le_exp_neg_one (u/n)
    have factorNonnegative : 0≤(u/n)*Real.exp (-(u/n)) := by positivity
    have exponential : Real.exp (-1)≤1 := Real.exp_le_one_iff.mpr (by norm_num)
    have bounded : ((u/n)*Real.exp (-(u/n)))^(d+1)≤1 :=
      (pow_le_pow_left₀ factorNonnegative (elementary.trans exponential) (d+1)).trans_eq (one_pow _)
    have identity : u^(d+1)*Real.exp (-u)=n^(d+1)*((u/n)*Real.exp (-(u/n)))^(d+1) := by
      rw [mul_pow,←Real.exp_nat_mul]
      have exponent : ((d+1 : ℕ) : ℝ)*(-(u/n))=-u := by dsimp [n]; field_simp
      rw [exponent]
      rw [←mul_assoc,←mul_pow]
      have cancel : n*(u/n)=u := by field_simp
      rw [cancel]
    rw [identity]
    have estimate := mul_le_mul_of_nonneg_left bounded (pow_nonneg positive.le (d+1))
    simpa [n] using estimate

theorem polynomial_exp_bound (P : ℝ[X]) (u : ℝ) (nonnegative : 0≤ u) :
    |P.eval u*Real.exp (-u)|≤∑ d∈P.support,|P.coeff d| *(d : ℝ)^d := by
  rw [Polynomial.eval_eq_sum,Polynomial.sum,Finset.sum_mul]
  calc
    _≤∑ d∈P.support,|P.coeff d*u^d*Real.exp (-u)| := Finset.abs_sum_le_sum_abs _ _
    _≤_ := by
      apply Finset.sum_le_sum
      intro d _
      rw [abs_mul,abs_mul,abs_pow,abs_of_nonneg nonnegative,abs_of_pos (Real.exp_pos _)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (monomial_exp_bound u nonnegative d) (abs_nonneg (P.coeff d))

theorem psiBound_nonnegative (r : ℕ) : 0≤ psiBound r := by
  unfold psiBound
  exact Finset.sum_nonneg (fun d _ => by positivity)

theorem actual_psi_budget (r : ℕ) (t : ℝ) : |iteratedDeriv r expNegInvGlue t|≤ psiBound r := by
  rw [actual_psi_derivative]
  change |(psiPolynomial r).eval t⁻¹*expNegInvGlue t|≤ psiBound r
  by_cases positive : 0<t
  · simp only [expNegInvGlue,if_neg positive.not_ge]
    exact polynomial_exp_bound (psiPolynomial r) t⁻¹ (inv_nonneg.mpr positive.le)
  · rw [expNegInvGlue.zero_of_nonpos (le_of_not_gt positive),mul_zero,abs_zero]
    exact psiBound_nonnegative r

theorem actual_psi_flat (r : ℕ) : iteratedDeriv r expNegInvGlue 0=0 := by
  rw [actual_psi_derivative]
  change (psiPolynomial r).eval (0 : ℝ)⁻¹*expNegInvGlue 0=0
  rw [expNegInvGlue.zero,mul_zero]

theorem transition_denominator (x : ℝ) :
    (1/9 : ℝ)<expNegInvGlue x+expNegInvGlue (1-x) := by
  have exponential : (1/9 : ℝ)<Real.exp (-2) := by
    have upper : Real.exp 2<9 := by
      rw [show (2 : ℝ)=1+1 from by norm_num,Real.exp_add]
      nlinarith [Real.exp_one_lt_three,Real.exp_pos 1]
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (Real.exp_pos 2) upper
  have half : expNegInvGlue (1/2)=Real.exp (-2) := by norm_num [expNegInvGlue]
  by_cases left : (1/2 : ℝ)≤ x
  · have bound := expNegInvGlue.monotone left
    rw [half] at bound
    linarith [expNegInvGlue.nonneg (1-x)]
  · have right : (1/2 : ℝ)≤1-x := by linarith
    have bound := expNegInvGlue.monotone right
    rw [half] at bound
    linarith [expNegInvGlue.nonneg x]

end LowEnergy.PreparationVacuumCutoffBudget
