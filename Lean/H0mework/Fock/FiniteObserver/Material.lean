import H0mework.Fock.FiniteObserver.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObserverCalculation

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceCopyProgram (Index)
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  (∀ (index : Index (inventoryBound runtime)) (steps : Nat) (word : Nat →₀ ℚ)
      (actor : Fin (inventoryBound runtime + steps + 1)),
    type_of% (response_source runtime index steps word actor) ∧
    type_of% (calculated_pairing runtime index steps word actor) ∧
    type_of% (frame_calculated runtime index steps word actor)) ∧
  (∀ (index : Index (inventoryBound runtime)) (steps length : Nat) (key : ZMod 2),
    type_of% (window_source runtime index steps length (fun index : Nat => (index : ZMod 2)) key)) ∧
  (∀ (nonunit : (maximumIndex runtime).val ≠ 0) (key : ZMod 2),
    type_of% (window_reconstruction runtime nonunit (fun index : Nat => (index : ZMod 2)) key) ∧
    type_of% (window_model runtime nonunit (fun index : Nat => (index : ZMod 2)) key) ∧
    ∀ error : SourceMinimumSharedNext.Window runtime,
      type_of% (window_effect runtime nonunit (fun index : Nat => (index : ZMod 2)) key error)) ∧
  ∀ (key : ZMod 2)
      (supported : key ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (fun actor : Actors runtime.tick.next => (actor.val : ZMod 2))).support),
    type_of% (window_next_support runtime (fun index : Nat => (index : ZMod 2)) key supported)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes,
    fun index steps word actor => ⟨response_source runtime index steps word actor,
      calculated_pairing runtime index steps word actor, frame_calculated runtime index steps word actor⟩,
    fun index steps length key => window_source runtime index steps length (fun index : Nat => (index : ZMod 2)) key,
    fun nonunit key => ⟨window_reconstruction runtime nonunit (fun index : Nat => (index : ZMod 2)) key,
      window_model runtime nonunit (fun index : Nat => (index : ZMod 2)) key,
      fun error => window_effect runtime nonunit (fun index : Nat => (index : ZMod 2)) key error⟩,
    fun key supported => window_next_support runtime (fun index : Nat => (index : ZMod 2)) key supported⟩

end
end SourceFiniteObserverCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
