import H0mework.Fock.CopyGraph.Consumers

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyPhaseRecovery

open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  (∀ target : SourceJointClockGraph.Carrier,
    type_of% (phase_budget runtime target) ∧
      ∀ phase : Fin ((maximumIndex runtime.tick.next).val + 1),
        type_of% (remaining_source runtime target phase) ∧ type_of% (remaining_energy runtime target phase) ∧
        type_of% (without_budget runtime target phase) ∧ type_of% (phase_conditional runtime target phase)) ∧
    (∀ phase : Fin ((maximumIndex runtime.tick.next).val + 1),
      type_of% (no_decoder_without_phase runtime phase) ∧ type_of% (no_model_decoder_without_phase runtime phase) ∧
      type_of% (strict_loss runtime phase)) ∧
    type_of% (native_tail_zero runtime) ∧ type_of% (native_gain_zero runtime) ∧
    (∀ phase : Fin ((maximumIndex runtime.tick.next).val + 1), type_of% (native_phase_zero runtime phase)) ∧
    type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨(fun target => ⟨phase_budget runtime target, fun phase =>
    ⟨remaining_source runtime target phase, remaining_energy runtime target phase,
      without_budget runtime target phase, phase_conditional runtime target phase⟩⟩),
    (fun phase => ⟨no_decoder_without_phase runtime phase, no_model_decoder_without_phase runtime phase, strict_loss runtime phase⟩),
    native_tail_zero runtime, native_gain_zero runtime, native_phase_zero runtime, material.factorizes⟩

end
end SourceCopyPhaseRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
