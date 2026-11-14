import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.CayleyEffectInverse
import H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.FiniteInverseWord
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse

open Filter
open scoped Topology

open private weight weight_bounds damped normalized_effect from
  H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.CayleyEffectInverse

def retention (d : ℝ) : ℝ := weight d

theorem retention_pos {d : ℝ} (positive : 0 < d) : 0 < retention d :=
  inv_pos.mpr (add_pos zero_lt_one positive)

theorem retention_lt_one {d : ℝ} (positive : 0 < d) : retention d < 1 :=
  (weight_bounds positive).2

theorem loss_eq {d : ℝ} (positive : 0 < d) : d * retention d = 1 - retention d := by
  have live : (1+d) ≠ 0 := (add_pos zero_lt_one positive).ne'
  change d*(1+d)⁻¹ = 1-(1+d)⁻¹
  field_simp
  ring

section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def clock (action : A) (d : ℝ) : A := damped action d

def driveScale (d : ℝ) : ℂ := -((d : ℂ)*(retention d : ℂ))

/-- The finite prefix of the existing Cayley effect inverse. -/
def finite (action : A) (d : ℝ) (length : Nat) : A :=
  driveScale d • SourceGeneratedFiniteInverseWord.word 1 (clock action d) length

@[simp] theorem finite_zero (action : A) (d : ℝ) : finite action d 0 = 0 := by
  simp only [finite, SourceGeneratedFiniteInverseWord.word, Finset.range_zero,
    Finset.sum_empty, smul_zero]

theorem finite_succ (action : A) (d : ℝ) (n : Nat) :
    finite action d (n+1) = clock action d * finite action d n + driveScale d • 1 := by
  simp only [finite, SourceGeneratedFiniteInverseWord.word, SourceGeneratedFiniteInverseWord.relative,
    inv_one, one_smul, geom_sum_succ, smul_add, mul_smul_comm]

theorem finite_effect (action : A) {d : ℝ} (positive : 0 < d) (n : Nat) :
    finite action d n * (action-1) = 1-(clock action d)^n ∧
      (action-1) * finite action d n = 1-(clock action d)^n := by
  have normalized : driveScale d • (action-1) = 1-clock action d :=
    normalized_effect action positive
  constructor
  · rw [finite, smul_mul_assoc, ← mul_smul_comm, normalized]
    simpa only [one_smul, SourceGeneratedFiniteInverseWord.relative, inv_one] using
      SourceGeneratedFiniteInverseWord.word_clock (1 : ℂ) one_ne_zero (clock action d) n
  · rw [finite, mul_smul_comm, ← smul_mul_assoc, normalized]
    simpa only [one_smul, SourceGeneratedFiniteInverseWord.relative, inv_one] using
      SourceGeneratedFiniteInverseWord.clock_word (1 : ℂ) one_ne_zero (clock action d) n

theorem clock_commutes (action : A) (d : ℝ) : Commute action (clock action d) := by
  change Commute action ((retention d : ℂ) • (1 + (d : ℂ) • action))
  exact ((Commute.one_right action).add_right ((Commute.refl action).smul_right _)).smul_right _

theorem finite_commutes (action : A) (d : ℝ) (n : Nat) : Commute action (finite action d n) := by
  induction n with
  | zero => rw [finite_zero]; exact Commute.zero_right action
  | succ n prior =>
    rw [finite_succ]
    exact ((clock_commutes action d).mul_right prior).add_right ((Commute.one_right action).smul_right _)

end Algebra

section Operator
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
local notation "Op" => H →L[ℂ] H

private theorem clock_apply_norm (action : Op) {d : ℝ} (positive : 0 < d)
    (isometric : ∀ x, ‖cayley action d x‖ = ‖x‖) (x : H) :
    ‖clock action d x‖ = retention d * ‖x‖ := by
  change ‖(retention d : ℂ) • cayley action d x‖ = _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (retention_pos positive), isometric]

private theorem clock_power_norm (action : Op) {d : ℝ} (positive : 0 < d)
    (isometric : ∀ x, ‖cayley action d x‖ = ‖x‖) (x : H) (n : Nat) :
    ‖(clock action d ^ n) x‖ = retention d ^ n * ‖x‖ := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self, one_mul]
  | succ n prior =>
    rw [pow_succ', mul_apply_eq_comp, clock_apply_norm action positive isometric, prior,
      pow_succ', mul_assoc]

theorem source_norm_le_effect (action : Op) {d : ℝ} (positive : 0 < d)
    (isometric : ∀ x, ‖cayley action d x‖ = ‖x‖) (x : H) : ‖x‖ ≤ ‖(action-1) x‖ := by
  have scaled : driveScale d • (action-1) = 1-clock action d :=
    normalized_effect action positive
  have applied : driveScale d • (action-1) x = x-clock action d x :=
    congrArg (fun op : Op => op x) scaled
  have scalarNorm : ‖driveScale d‖ = d*retention d := by
    rw [driveScale, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos positive, abs_of_pos (retention_pos positive)]
  have triangle := norm_sub_norm_le x (clock action d x)
  rw [clock_apply_norm action positive isometric, ← applied, norm_smul, scalarNorm] at triangle
  apply le_of_mul_le_mul_left _ (mul_pos positive (retention_pos positive))
  simpa only [loss_eq positive, sub_mul, one_mul] using triangle

/-- The geometric tail is an actual field and its bound uses only the measured effect. -/
theorem finite_error (action : Op) {d : ℝ} (positive : 0 < d)
    (isometric : ∀ x, ‖cayley action d x‖ = ‖x‖) (x : H) (n : Nat) :
    finite action d n ((action-1) x) = x-(clock action d ^ n) x ∧
      ‖finite action d n ((action-1) x)-x‖ ≤ retention d ^ n * ‖(action-1) x‖ := by
  have exactField : finite action d n ((action-1) x) = x-(clock action d ^ n) x :=
    congrArg (fun op : Op => op x) (finite_effect action positive n).1
  refine ⟨exactField, ?_⟩
  rw [exactField, sub_right_comm, sub_self, zero_sub, norm_neg, clock_power_norm action positive isometric]
  exact mul_le_mul_of_nonneg_left (source_norm_le_effect action positive isometric x)
    (pow_nonneg (retention_pos positive).le _)

theorem inverse_isometric_effect [CompleteSpace H] (action : Op) {d : ℝ} (positive : 0 < d)
    (isometric : ∀ x, ‖cayley action d x‖ = ‖x‖) :
    inverse action d * (action-1) = 1 ∧ (action-1) * inverse action d = 1 := by
  apply inverse_effect action (budget := 1) positive
  intro n
  have bound : ‖(cayley action d)^n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [one_mul]
    induction n with
    | zero => rw [pow_zero, one_apply_eq_self]
    | succ n prior => rw [pow_succ', mul_apply_eq_comp, isometric]; exact prior
  exact bound.trans (by rw [mul_one]; exact le_add_of_nonneg_left (Nat.cast_nonneg n))

theorem finite_tendsto [CompleteSpace H] (action : Op) {d : ℝ} (positive : 0 < d)
    (isometric : ∀ x, ‖cayley action d x‖ = ‖x‖) (effect : H) :
    Tendsto (fun n => finite action d n effect) atTop (𝓝 (inverse action d effect)) := by
  let x := inverse action d effect
  have solved : (action-1) x = effect :=
    congrArg (fun op : Op => op effect) (inverse_isometric_effect action positive isometric).2
  have tail := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (retention_pos positive).le (retention_lt_one positive)).mul_const ‖effect‖
  rw [zero_mul] at tail
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by
    simpa only [solved] using (finite_error action positive isometric x n).2) tail

end Operator

end SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
