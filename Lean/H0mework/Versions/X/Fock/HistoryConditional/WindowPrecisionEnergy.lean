import H0mework.Versions.X.Fock.HistoryConditional.WindowPrecisionRows

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPrecision

open SourceCopyProgram (Index)
open SourceOperatorObservationAcquisition (Window)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def rowVector (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coefficients : Coefficients runtime index steps) (phase : Fin (index.val + 2)) : SourceJointClockGraph.Carrier :=
  ∑ actor, (star (coefficients phase actor)) • cotest runtime index actor.val

def coefficientEnergy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coefficients : Coefficients runtime index steps) : ℝ :=
  ∑ phase, ∑ left, ∑ right,
    (coefficients phase left * star (coefficients phase right) *
      ((if left.val = right.val then 1 else 0) + 1 +
        (((index.val + 1 : Nat) : ℂ) ^ 4 * ((left.val + 1 : Nat) : ℂ) * ((right.val + 1 : Nat) : ℂ)))).re

theorem evaluate_pairing (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coefficients : Coefficients runtime index steps) (samples : Window runtime index) :
    evaluate runtime index steps coefficients samples =
      ∑ phase, ⟪rowVector runtime index steps coefficients phase, samples phase⟫_ℂ := by
  simp only [evaluate_apply, column_pairing, rowVector, sum_inner, inner_smul_left,
    starRingEnd_apply, star_star]

theorem row_inner (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coefficients : Coefficients runtime index steps) (phase : Fin (index.val + 2)) :
    ⟪rowVector runtime index steps coefficients phase, rowVector runtime index steps coefficients phase⟫_ℂ =
      ∑ left, ∑ right, coefficients phase left * star (coefficients phase right) *
        ((if left.val = right.val then 1 else 0) + 1 +
          (((index.val + 1 : Nat) : ℂ) ^ 4 * ((left.val + 1 : Nat) : ℂ) * ((right.val + 1 : Nat) : ℂ))) := by
  simp only [rowVector]
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro left _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro right _
  simp only [inner_smul_left, inner_smul_right, starRingEnd_apply, star_star, cotest_gram]
  ring

theorem energy_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coefficients : Coefficients runtime index steps) :
    (∑ phase, ‖rowVector runtime index steps coefficients phase‖ ^ 2) =
      coefficientEnergy runtime index steps coefficients := by
  unfold coefficientEnergy
  apply Finset.sum_congr rfl
  intro phase _
  have source := congrArg Complex.re (row_inner runtime index steps coefficients phase)
  have normRe : (⟪rowVector runtime index steps coefficients phase, rowVector runtime index steps coefficients phase⟫_ℂ).re =
      ‖rowVector runtime index steps coefficients phase‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (rowVector runtime index steps coefficients phase)
  simpa only [normRe, Complex.re_sum] using source

def sampleEnergy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (samples : Window runtime index) : ℝ := ∑ phase, ‖samples phase‖ ^ 2

theorem evaluate_bound (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coefficients : Coefficients runtime index steps) (samples : Window runtime index) :
    ‖evaluate runtime index steps coefficients samples‖ ^ 2 ≤
      coefficientEnergy runtime index steps coefficients * sampleEnergy runtime index samples := by
  have bounded : ‖evaluate runtime index steps coefficients samples‖ ≤
      ∑ phase, ‖rowVector runtime index steps coefficients phase‖ * ‖samples phase‖ := by
    rw [evaluate_pairing]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun phase _ => norm_inner_le_norm _ _))
  have positive : 0 ≤ ∑ phase, ‖rowVector runtime index steps coefficients phase‖ * ‖samples phase‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    _ ≤ (∑ phase, ‖rowVector runtime index steps coefficients phase‖ * ‖samples phase‖) ^ 2 := by
      nlinarith [norm_nonneg (evaluate runtime index steps coefficients samples)]
    _ ≤ (∑ phase, ‖rowVector runtime index steps coefficients phase‖ ^ 2) * (∑ phase, ‖samples phase‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = _ := by rw [energy_source]; rfl

end
end SourceWindowPrecision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
