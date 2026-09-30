import H0mework.Versions.X.Fock.HistoryConditional.MinimumWindowErrorCost

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumWindowError

open SourceCopyCurrentCoordinates (maximumIndex)
open SourceOperatorObservationAcquisition (Window)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧ ∀ nonunit : (maximumIndex runtime).val ≠ 0,
    type_of% (source_noise_energy runtime nonunit) ∧
    (∀ target : SourceJointClockGraph.Carrier, ∀ error : Window runtime (maximumIndex runtime),
      type_of% (error_energy runtime (maximumIndex runtime) nonunit 0 target error) ∧
      type_of% (step_error runtime nonunit target error)) ∧
    ∀ key : ZMod 2,
      (∀ error : Window runtime (maximumIndex runtime),
        type_of% (effect_error runtime nonunit (fun index : Nat => (index : ZMod 2)) key error)) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support,
        type_of% (conditional_noise_cost runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported) ∧
        ∀ error : Window runtime (maximumIndex runtime),
          type_of% (conditional_error runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported error) ∧
          type_of% (conditional_next_error runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported error)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes, fun nonunit => ⟨source_noise_energy runtime nonunit,
    fun target error => ⟨error_energy runtime (maximumIndex runtime) nonunit 0 target error, step_error runtime nonunit target error⟩,
    fun key => ⟨fun error => effect_error runtime nonunit (fun index : Nat => (index : ZMod 2)) key error,
      fun supported => ⟨conditional_noise_cost runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported,
        fun error => ⟨conditional_error runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported error,
          conditional_next_error runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported error⟩⟩⟩⟩⟩

end
end SourceMinimumWindowError
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
