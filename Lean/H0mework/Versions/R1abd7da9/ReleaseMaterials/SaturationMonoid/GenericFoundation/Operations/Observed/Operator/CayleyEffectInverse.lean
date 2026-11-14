import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def cayley (action : A) (d : ℝ) : A := 1 + (d : ℂ) • action

private def weight (d : ℝ) : ℝ := (1+d)⁻¹

private theorem weight_bounds {d : ℝ} (positive : 0 < d) :
    0 ≤ weight d ∧ weight d < 1 := by
  have one : 1 < 1+d := lt_add_of_pos_right 1 positive
  exact ⟨inv_nonneg.mpr (zero_le_one.trans one.le),inv_lt_one_of_one_lt₀ one⟩

private def damped (action : A) (d : ℝ) : A := (weight d : ℂ) • cayley action d

private theorem linear_series {d : ℝ} (positive : 0 < d) (budget : ℝ) :
    HasSum (fun n : Nat => budget * ((n : ℝ)+1) * (weight d)^n)
      (budget / (1-weight d)^2) := by
  have q := weight_bounds positive
  have normLt : ‖weight d‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg q.1] using q.2
  have linear : HasSum (fun n : Nat => ((n : ℝ)+1) * (weight d)^n)
      (1 / (1-weight d)^2) := by
    simpa only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one] using
      (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 normLt)
  simpa only [← mul_assoc,div_eq_mul_inv,one_mul] using linear.mul_left budget

private theorem norm_power_le (action : A) {d budget : ℝ} (positive : 0 < d)
    (growth : ∀ n : Nat, ‖(cayley action d)^n‖ ≤ ((n : ℝ)+1)*budget) (n : Nat) :
    ‖(damped action d)^n‖ ≤ budget*((n : ℝ)+1)*(weight d)^n := by
  let q := weight d
  have nonnegative : 0 ≤ q := (weight_bounds positive).1
  have normCast : ‖(q : ℂ)‖ = q := by simp [Real.norm_eq_abs,abs_of_nonneg nonnegative]
  change ‖((q : ℂ) • cayley action d)^n‖ ≤ budget*((n : ℝ)+1)*q^n
  rw [smul_pow]
  calc
    _ ≤ ‖(q : ℂ)^n‖ * ‖(cayley action d)^n‖ := norm_smul_le _ _
    _ ≤ q^n * (((n : ℝ)+1)*budget) := by
      rw [norm_pow,normCast]
      exact mul_le_mul_of_nonneg_left (growth n) (pow_nonneg nonnegative _)
    _ = _ := by ring

private theorem normalized_effect (action : A) {d : ℝ} (positive : 0 < d) :
    (-((d : ℂ)*(weight d : ℂ))) • (action-1) = 1-damped action d := by
  let q := weight d
  have positiveOne : 0 < 1+d := zero_lt_one.trans (lt_add_of_pos_right 1 positive)
  have weightIdentity : d*q+q = 1 := by
    calc
      _ = (1+d)*(1+d)⁻¹ := by dsimp only [q,weight]; ring
      _ = 1 := mul_inv_cancel₀ positiveOne.ne'
  have coefficient : (d : ℂ)*(q : ℂ) = 1-(q : ℂ) := by
    exact_mod_cast (eq_sub_iff_add_eq.mpr weightIdentity)
  change (-((d : ℂ)*(q : ℂ))) • (action-1) =
    1 - (q : ℂ) • (1 + (d : ℂ) • action)
  calc
    _ = ((d : ℂ)*(q : ℂ)) • 1 - ((d : ℂ)*(q : ℂ)) • action := by
      rw [neg_smul,smul_sub,neg_sub]
    _ = (1-(q : ℂ)) • 1 - ((q : ℂ)*(d : ℂ)) • action := by
      rw [← coefficient,mul_comm (q : ℂ) (d : ℂ)]
    _ = _ := by rw [sub_smul,one_smul,smul_add,smul_smul,sub_sub]

/-- A linear power budget on the actual Cayley action pays a convergent inverse of its increment. -/
def inverse (action : A) (d : ℝ) : A :=
  (-((d : ℂ)*(weight d : ℂ))) • ∑' n : Nat, (damped action d)^n

def inverseBudget (d budget : ℝ) : ℝ := d*weight d*(budget/(1-weight d)^2)

variable [CompleteSpace A]

theorem inverse_effect (action : A) {d budget : ℝ} (positive : 0 < d)
    (growth : ∀ n : Nat, ‖(cayley action d)^n‖ ≤ ((n : ℝ)+1)*budget) :
    inverse action d * (action-1) = 1 ∧ (action-1) * inverse action d = 1 := by
  have powers := Summable.of_norm_bounded (linear_series positive budget).summable
    (norm_power_le action positive growth)
  constructor
  · unfold inverse
    rw [smul_mul_assoc,← mul_smul_comm,normalized_effect action positive]
    exact powers.tsum_pow_mul_one_sub
  · unfold inverse
    rw [mul_smul_comm,← smul_mul_assoc,normalized_effect action positive]
    exact powers.one_sub_mul_tsum_pow

theorem inverse_norm (action : A) {d budget : ℝ} (positive : 0 < d)
    (growth : ∀ n : Nat, ‖(cayley action d)^n‖ ≤ ((n : ℝ)+1)*budget) :
    ‖inverse action d‖ ≤ inverseBudget d budget := by
  let q := weight d
  have qNonnegative : 0 ≤ q := (weight_bounds positive).1
  have powers := Summable.of_norm_bounded (linear_series positive budget).summable
    (norm_power_le action positive growth)
  have sumBound := powers.hasSum.norm_le_of_bounded (linear_series positive budget)
    (norm_power_le action positive growth)
  have scalarNorm : ‖-((d : ℂ)*(q : ℂ))‖ = d*q := by
    rw [norm_neg,norm_mul]
    simp [Real.norm_eq_abs,abs_of_nonneg positive.le,abs_of_nonneg qNonnegative]
  unfold inverse inverseBudget
  calc
    _ ≤ ‖-((d : ℂ)*(q : ℂ))‖ * ‖∑' n : Nat, (damped action d)^n‖ := norm_smul_le _ _
    _ ≤ _ := by rw [scalarNorm]; exact mul_le_mul_of_nonneg_left sumBound (mul_nonneg positive.le qNonnegative)

end SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
