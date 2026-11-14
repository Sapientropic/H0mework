import Mathlib.Analysis.InnerProductSpace.MeanErgodic

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.ContractiveRecovery

open Filter Finset Function
open scoped Topology

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The source supplies a drive for the existing linear action. -/
def step (action : H →L[𝕜] H) (drive current : H) : H := action current + drive

/-- Average the finite driven trajectory starting from zero. -/
def approximate (action : H →L[𝕜] H) (drive : H) (n : Nat) : H :=
  birkhoffAverage 𝕜 (step action drive) id (n+1) (0 : H)

theorem iterate_source (action : H →L[𝕜] H) (source : H) (n : Nat) :
    (step action (source-action source))^[n] 0 = source - (action)^[n] source := by
  induction n with
  | zero => simp only [iterate_zero, id_eq, sub_self]
  | succ n prior =>
    rw [iterate_succ_apply', prior, step, map_sub, iterate_succ_apply']
    abel

theorem actual_approximation (action : H →L[𝕜] H) (source : H) (n : Nat) :
    approximate action (source-action source) n =
      source - birkhoffAverage 𝕜 action id (n+1) source := by
  have live : (((n+1 : ℕ) : 𝕜)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have constant : (((n+1 : ℕ) : 𝕜))⁻¹ • (∑ _j ∈ range (n+1), source) = source := by
    rw [sum_const, card_range, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ live, one_smul]
  simp only [approximate, birkhoffAverage, birkhoffSum, id_eq, iterate_source, sum_sub_distrib,
    smul_sub, constant]

/-- A fixed-point-free contraction recovers its source from the actual drive. -/
theorem recover [CompleteSpace H] (action : H →L[𝕜] H) (contractive : ‖action‖ ≤ 1)
    (fixed : ∀ x, action x=x → x=0) (source : H) :
    Tendsto (approximate action (source-action source)) atTop (𝓝 source) := by
  have converge := (action.tendsto_birkhoffAverage_orthogonalProjection contractive source).comp
    (tendsto_add_atTop_nat 1)
  let projection := (action.eqLocus (1 : H →L[𝕜] H)).orthogonalProjectionOnto source
  have zero : (projection : H) = 0 := fixed _ projection.property
  change Tendsto (fun n : Nat => birkhoffAverage 𝕜 action id (n+1) source) atTop
    (𝓝 (projection : H)) at converge
  rw [zero] at converge
  have limit := (tendsto_const_nhds (x := source)).sub converge
  rw [sub_zero] at limit
  exact limit.congr' (Eventually.of_forall fun n => (actual_approximation action source n).symm)

private theorem step_error (action : H →L[𝕜] H) (contractive : ‖action‖ ≤ 1)
    (x y : H) (j : Nat) :
    ‖(step action x)^[j] (0 : H)-(step action y)^[j] 0‖ ≤ (j : ℝ)*‖x-y‖ := by
  induction j with
  | zero => simp only [iterate_zero, id_eq, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ j prior =>
    rw [iterate_succ_apply', iterate_succ_apply', step, step]
    let a := (step action x)^[j] (0 : H)
    let b := (step action y)^[j] (0 : H)
    change ‖action a+x-(action b+y)‖ ≤ _
    rw [show action a+x-(action b+y) = action (a-b)+(x-y) by rw [map_sub]; abel]
    calc
      _ ≤ ‖action (a-b)‖ + ‖x-y‖ := norm_add_le _ _
      _ ≤ ‖a-b‖ + ‖x-y‖ := add_le_add_left
        (by simpa only [one_mul] using action.le_of_opNorm_le contractive (a-b)) _
      _ ≤ (j : ℝ)*‖x-y‖ + ‖x-y‖ := add_le_add_left prior _
      _ = _ := by rw [Nat.cast_succ, add_mul, one_mul]

/-- Finite drive perturbations are paid through the actual trajectory. -/
theorem error (action : H →L[𝕜] H) (contractive : ‖action‖ ≤ 1)
    (x y : H) (n : Nat) :
    ‖approximate action x n-approximate action y n‖ ≤ (n : ℝ)*‖x-y‖ := by
  let diff := fun j : Nat => (step action x)^[j] (0 : H) - (step action y)^[j] (0 : H)
  let budget := (n : ℝ)*‖x-y‖
  have scale : ‖(((n+1 : ℕ) : 𝕜))⁻¹‖ = (((n+1 : ℕ) : ℝ))⁻¹ := by rw [norm_inv, RCLike.norm_natCast]
  have positive : 0 ≤ (((n+1 : ℕ) : ℝ))⁻¹ := by positivity
  have live : (((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have bound (j : Nat) (inside : j ∈ range (n+1)) : ‖diff j‖ ≤ budget :=
    (step_error action contractive x y j).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp inside)) (norm_nonneg _))
  simp only [approximate, birkhoffAverage, birkhoffSum, id_eq, ← smul_sub, ← sum_sub_distrib, norm_smul, scale]
  change (((n+1 : ℕ) : ℝ))⁻¹ * ‖∑ j ∈ range (n+1), diff j‖ ≤ budget
  calc
    _ ≤ (((n+1 : ℕ) : ℝ))⁻¹ * (∑ j ∈ range (n+1), ‖diff j‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) positive
    _ ≤ (((n+1 : ℕ) : ℝ))⁻¹ * (∑ _j ∈ range (n+1), budget) :=
      mul_le_mul_of_nonneg_left (sum_le_sum bound) positive
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ live, one_mul]

end SourceGeneratedActionObservationHistory.ContractiveRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
