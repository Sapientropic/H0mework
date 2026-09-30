import H0mework.Fock.HistoryConditional.MinimumSharedNextConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumSharedNext

open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧ type_of% initial_source ∧ type_of% initial_next ∧
  (∀ phase : Fin ((maximumIndex runtime).val + 2), type_of% (native_sample runtime phase)) ∧
  ∀ nonunit : (maximumIndex runtime).val ≠ 0,
    type_of% (SourceFiniteObservationMinimum.least_window runtime (maximumIndex runtime) nonunit 0) ∧
    type_of% (step_source runtime nonunit) ∧ type_of% (family_next runtime nonunit) ∧
    (∀ previous : Window runtime, type_of% (step_energy runtime nonunit previous)) ∧
    (∀ target : SourceJointClockGraph.Carrier,
      type_of% (step_reconstruction runtime nonunit target) ∧ type_of% (step_loss runtime nonunit target)) ∧
    ∀ key : ZMod 2, type_of% (effect_reconstruction runtime nonunit (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (effect_loss runtime nonunit (fun index : Nat => (index : ZMod 2)) key)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes, initial_source, initial_next, fun phase => native_sample runtime phase,
    fun nonunit => ⟨SourceFiniteObservationMinimum.least_window runtime (maximumIndex runtime) nonunit 0,
      step_source runtime nonunit, family_next runtime nonunit, fun previous => step_energy runtime nonunit previous,
      fun target => ⟨step_reconstruction runtime nonunit target, step_loss runtime nonunit target⟩,
      fun key => ⟨effect_reconstruction runtime nonunit (fun index : Nat => (index : ZMod 2)) key,
        effect_loss runtime nonunit (fun index : Nat => (index : ZMod 2)) key⟩⟩⟩

end
end SourceMinimumSharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
