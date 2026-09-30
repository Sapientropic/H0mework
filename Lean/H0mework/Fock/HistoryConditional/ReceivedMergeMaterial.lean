import H0mework.Fock.HistoryConditional.ReceivedMergePositive

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalMerge

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ (nonunit : (maximumIndex runtime).val ≠ 0)
      (samples : ZMod 2 → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
      (budgets : ∀ key : ZMod 2, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (fun n : Nat => (n : ZMod 2)) key)) < SourcePosteriorStability.threshold runtime ^ 2),
    type_of% (received_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets) ∧
    type_of% (received_next runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets) ∧
    type_of% (model_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll () budgets) ∧
    type_of% (decoder_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll () budgets) ∧
    type_of% (received_information runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets) ∧
    type_of% (lost_energy_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets) ∧
    type_of% (information_zero_iff runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets) ∧
    type_of% (loss runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets) ∧
    type_of% (recovery_budget runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets) ∧
    type_of% (information_next runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets) ∧
    type_of% (observation_balance runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets) ∧
    type_of% (parity_positive runtime nonunit samples budgets)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes, fun nonunit samples budgets =>
    ⟨received_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets,
      received_next runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets,
      model_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll () budgets,
      decoder_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll () budgets,
      received_information runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets,
      lost_energy_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets,
      information_zero_iff runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets,
      loss runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets,
      recovery_budget runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets,
      information_next runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets,
      observation_balance runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets,
      parity_positive runtime nonunit samples budgets⟩⟩

end
end SourceReceivedConditionalMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
