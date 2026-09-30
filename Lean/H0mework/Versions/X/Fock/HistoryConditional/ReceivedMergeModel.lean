import H0mework.Versions.X.Fock.HistoryConditional.ReceivedMergeRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalMerge

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse] [Fintype Fine]

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors NextModel nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def model (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (forget : Fine → Coarse) (value : Coarse) : NextModel runtime :=
  ∑ actor : Actors runtime,
    ((received forget (inventoryBound runtime) (maximumIndex runtime).val nonunit samples value).2 actor : ℂ) • nextRead runtime actor

def decoder (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (forget : Fine → Coarse) (value : Coarse) : SourceJointClockGraph.Carrier :=
  SourceConditionalVector.realizeModel runtime (model runtime nonunit samples forget value)

theorem model_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse) (value : Coarse)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    model runtime nonunit samples forget value = SourceConditionalNativePosterior.model runtime (forget ∘ read) value := by
  rw [model, received_source runtime nonunit samples read forget budgets]
  rfl

theorem decoder_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse) (value : Coarse)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    decoder runtime nonunit samples forget value = SourceConditionalMergeLoss.decoder runtime read forget value := by
  rw [decoder, model_source runtime nonunit samples read forget value budgets]
  exact (congrFun (SourceConditionalMergeLoss.decoder_original runtime read forget) value).symm

end
end SourceReceivedConditionalMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
