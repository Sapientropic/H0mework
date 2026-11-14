import H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.CayleyEffectInverse.Finite

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse

open Filter
open scoped Topology

open private norm_power_le linear_series from H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.CayleyEffectInverse

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
local notation "Op" => H →L[ℂ] H

/-- The omitted term of the finite inverse is the damped clock applied to the entire recovered field. -/
theorem finite_tail (action : Op) {d budget : ℝ} (positive : 0 < d)
    (growth : ∀ n : Nat, ‖(cayley action d)^n‖ ≤ ((n : ℝ)+1)*budget) (data : H) (m : Nat) :
    finite action d m data = inverse action d data - (clock action d ^ m) (inverse action d data) := by
  have right : (action-1) (inverse action d data) = data :=
    congrArg (fun operator : Op => operator data) (inverse_effect action positive growth).2
  have finiteRight : finite action d m ((action-1) (inverse action d data)) =
      inverse action d data - (clock action d ^ m) (inverse action d data) :=
    congrArg (fun operator : Op => operator (inverse action d data)) (finite_effect action positive m).1
  rwa [right] at finiteRight

/-- Linear Cayley growth costs one factor of the word length in the geometric tail. -/
theorem finite_growth_error (action : Op) {d budget : ℝ} (positive : 0 < d)
    (growth : ∀ n : Nat, ‖(cayley action d)^n‖ ≤ ((n : ℝ)+1)*budget) (data : H) (m : Nat) :
    ‖finite action d m data-inverse action d data‖ ≤
      (budget*((m : ℝ)+1)*retention d ^ m) * (inverseBudget d budget * ‖data‖) := by
  rw [finite_tail action positive growth, sub_right_comm, sub_self, zero_sub, norm_neg]
  let size := budget*((m : ℝ)+1)*retention d^m
  have power : ‖clock action d ^ m‖ ≤ size := norm_power_le action positive growth m
  have inverseBound : ‖inverse action d data‖ ≤ inverseBudget d budget * ‖data‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (inverse_norm action positive growth) (norm_nonneg _))
  exact ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right power (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left inverseBound ((norm_nonneg _).trans power))

omit [CompleteSpace H] in
/-- A uniform inverse budget also controls the gain on finite observation errors. -/
theorem finite_norm_of_growth (action : Op) {d budget : ℝ} (positive : 0 < d)
    (budgetNonnegative : 0 ≤ budget)
    (growth : ∀ n : Nat, ‖(cayley action d)^n‖ ≤ ((n : ℝ)+1)*budget) (m : Nat) :
    ‖finite action d m‖ ≤ inverseBudget d budget := by
  let q := retention d
  have qNonnegative : 0 ≤ q := (retention_pos positive).le
  let term (n : Nat) : ℝ := budget*((n : ℝ)+1)*q^n
  have sums : HasSum term (budget/(1-q)^2) := linear_series positive budget
  have powers : ∀ n, ‖clock action d ^ n‖ ≤ term n := norm_power_le action positive growth
  have scalarNorm : ‖driveScale d‖ = d*q := by
    rw [driveScale, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos positive, abs_of_nonneg qNonnegative]
  have tailBound : (∑ j ∈ Finset.range m, term j) ≤ budget/(1-q)^2 := by
    rw [← sums.tsum_eq]
    exact sums.summable.sum_le_tsum _ (fun j _ => mul_nonneg
      (mul_nonneg budgetNonnegative (by positivity)) (pow_nonneg qNonnegative j))
  have finiteSum : ‖∑ j ∈ Finset.range m, clock action d ^ j‖ ≤ budget/(1-q)^2 :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => powers j).trans tailBound)
  change ‖driveScale d • SourceGeneratedFiniteInverseWord.word 1 (clock action d) m‖ ≤ _
  simp only [SourceGeneratedFiniteInverseWord.word, SourceGeneratedFiniteInverseWord.relative, inv_one,
    one_smul, norm_smul, scalarNorm]
  exact mul_le_mul_of_nonneg_left finiteSum (mul_nonneg positive.le qNonnegative)

/-- The observation and omitted action terms in the finite inverse budget. -/
def noisyBudget (d budget : ℝ) (m : Nat) (dataNorm observationError : ℝ) : ℝ :=
  inverseBudget d budget*observationError +
    (budget*((m : ℝ)+1)*retention d^m)*(inverseBudget d budget*dataNorm)

theorem finite_noisy_error (action : H →L[ℂ] H) {loss budget : ℝ} (positive : 0 < loss)
    (budgetNonnegative : 0 ≤ budget)
    (powers : ∀ k : Nat, ‖(cayley action loss)^k‖ ≤ ((k : ℝ)+1)*budget)
    (datum projection : H) (m : Nat) :
    ‖finite action loss m projection-inverse action loss datum‖ ≤
      noisyBudget loss budget m ‖datum‖ ‖datum-projection‖ := by
  unfold noisyBudget
  let act := finite action loss m
  have finiteBound := finite_norm_of_growth action positive budgetNonnegative powers m
  have tail := finite_growth_error action positive powers datum m
  calc
    _ ≤ ‖act projection-act datum‖+‖act datum-inverse action loss datum‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      refine add_le_add ?_ tail
      rw [← map_sub, norm_sub_rev datum projection]
      exact (act.le_opNorm _).trans (mul_le_mul_of_nonneg_right finiteBound (norm_nonneg _))

theorem finite_noisy_error_resolved (action : Op) {loss budget : ℝ} (positive : 0 < loss)
    (budgetNonnegative : 0 ≤ budget)
    (powers : ∀ k : Nat, ‖(cayley action loss)^k‖ ≤ ((k : ℝ)+1)*budget)
    (datum projection target : H) (m : Nat) (resolved : inverse action loss datum = target) :
    ‖finite action loss m projection-target‖ ≤ noisyBudget loss budget m ‖datum‖ ‖datum-projection‖ :=
  resolved ▸ finite_noisy_error action positive budgetNonnegative powers datum projection m

theorem finite_observed_error
    (action : Op) {loss bound : ℝ} (positive : 0 < loss) (nonnegative : 0 ≤ bound)
    (powers : ∀ k : Nat, ‖(cayley action loss)^k‖ ≤ ((k : ℝ)+1)*bound)
    (datum fitted target actual : H) (m : Nat) (error total : ℝ)
    (resolved : inverse action loss datum = target)
    (executed : actual = finite action loss m fitted)
    (observation : error = ‖datum-fitted‖)
    (budget : total = noisyBudget loss bound m ‖datum‖ error) :
    ‖actual-target‖ ≤ total := by
  subst actual total error
  exact finite_noisy_error_resolved action positive nonnegative powers datum fitted target m resolved

omit [CompleteSpace H] in
theorem linear_retention_tendsto {d : ℝ} (positive : 0 < d) :
    Tendsto (fun m : Nat => ((m : ℝ)+1)*retention d^m) atTop (𝓝 0) := by
  have q := retention_pos positive
  have small := retention_lt_one positive
  have first := tendsto_self_mul_const_pow_of_lt_one q.le small
  have second := tendsto_pow_atTop_nhds_zero_of_lt_one q.le small
  simpa only [add_mul, one_mul, zero_add] using first.add second

end SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
