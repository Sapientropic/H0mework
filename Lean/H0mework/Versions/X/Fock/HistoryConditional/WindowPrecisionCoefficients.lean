import H0mework.Versions.X.Fock.HistoryConditional.WindowPrecisionCotest

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPrecision

open SourceCopyProgram (Index)
open SourceOperatorObservationAcquisition (Window)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev Coefficients (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :=
  Fin (index.val + 2) → Fin (inventoryBound runtime + steps + 1) → ℂ

def evaluate (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Coefficients runtime index steps →ₗ[ℂ] (Window runtime index →ₗ[ℂ] ℂ) :=
  ∑ phase : Fin (index.val + 2), ∑ actor : Fin (inventoryBound runtime + steps + 1),
    ((LinearMap.proj actor : (Fin (inventoryBound runtime + steps + 1) → ℂ) →ₗ[ℂ] ℂ).comp
      (LinearMap.proj phase : Coefficients runtime index steps →ₗ[ℂ] (Fin (inventoryBound runtime + steps + 1) → ℂ))).smulRight
    (SourceOperatorObservationAcquisition.columns runtime index steps actor phase)

theorem evaluate_apply (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coefficients : Coefficients runtime index steps) (samples : Window runtime index) :
    evaluate runtime index steps coefficients samples =
      ∑ phase, ∑ actor, coefficients phase actor * columnReader runtime index steps actor phase samples := by
  simp only [evaluate, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

def columnCoefficients (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1)) (phase : Fin (index.val + 2)) : Coefficients runtime index steps :=
  Pi.single phase (Pi.single actor 1)

theorem evaluate_column (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1)) (phase : Fin (index.val + 2)) :
    evaluate runtime index steps (columnCoefficients runtime index steps actor phase) =
      SourceOperatorObservationAcquisition.columns runtime index steps actor phase := by
  apply LinearMap.ext
  intro samples
  simp [evaluate_apply, columnCoefficients, Pi.single_apply, ite_apply]
  rfl

end
end SourceWindowPrecision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
