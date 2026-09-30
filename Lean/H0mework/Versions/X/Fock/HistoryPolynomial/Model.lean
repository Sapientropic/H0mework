import H0mework.Versions.X.Fock.HistoryPolynomial.Dynamic
import H0mework.Versions.X.Fock.PrimeField.RecoveryMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCyclicModule

open SourcePrimeHistoryRecovery SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Polynomial
noncomputable section

def originalModelEquiv : SourceOperationNative.Carrier process ≃ₗ[ℤ] Model nativeAction observation :=
  LinearEquiv.ofBijective (projection nativeAction observation)
    ⟨fun _ _ same => (original_model_fibre sourceOwner _ _).mp same,
      Submodule.mkQ_surjective (LinearMap.ker (sourceMap nativeAction observation))⟩

abbrev DynamicModel := Module.AEval' (modelAction nativeAction observation)

def retainModel : Model nativeAction observation ≃ₗ[ℤ] DynamicModel :=
  Module.AEval'.of (modelAction nativeAction observation)

def modelEquiv : DynamicSource ≃ₗ[Polynomial ℤ] DynamicModel :=
  LinearEquiv.ofAEval nativeAction (originalModelEquiv.trans retainModel) (fun word => by
    change retainModel (projection nativeAction observation (nativeAction word)) =
      (X : Polynomial ℤ) • retainModel (projection nativeAction observation word)
    exact (congrArg retainModel (modelAction_source nativeAction observation word).symm).trans
      (Module.AEval'.X_smul_of (modelAction nativeAction observation)
        (projection nativeAction observation word)).symm)

theorem model_is_original (word : SourceOperationNative.Carrier process) :
    modelEquiv (retained word) = retainModel (projection nativeAction observation word) := rfl

theorem model_program (polynomial : Polynomial ℤ) :
    retainModel (projection nativeAction observation (program polynomial)) =
      polynomial • retainModel (projection nativeAction observation (SourceOperationNative.point runtimeSeed)) := by
  change modelEquiv (retained (program polynomial)) = polynomial • modelEquiv generator
  rw [program_is_action, map_smul]

def modelPolynomial : DynamicModel ≃ₗ[Polynomial ℤ] Polynomial ℤ := modelEquiv.symm.trans polynomialEquiv

theorem model_coefficients (polynomial : Polynomial ℤ) :
    modelPolynomial (retainModel (projection nativeAction observation (program polynomial))) = polynomial := by
  change polynomialEquiv (modelEquiv.symm (modelEquiv (retained (program polynomial)))) = polynomial
  rw [modelEquiv.symm_apply_apply, polynomial_program]

theorem original_selector_reads (polynomial : Polynomial ℤ) (index : Nat) :
    selector sourceOwner index (program polynomial) = polynomial.coeff index :=
  (recovers_source_word sourceOwner index (program polynomial)).trans (program_coefficient polynomial index)

instance model_finite_polynomial : Module.Finite (Polynomial ℤ) DynamicModel :=
  Module.Finite.equiv modelEquiv

instance model_noetherian_polynomial : IsNoetherian (Polynomial ℤ) DynamicModel := inferInstance

end
end SourceCyclicModule
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
