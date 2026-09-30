import H0mework.Fock.StableReceivedCount.Energy

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceStableReceivedCount

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def updatedSamples (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) (selected : Bool) :
    SourceRationalWindowReadout.Samples (inventoryBound runtime.tick.next) ((maximumIndex runtime.tick.next).val + 1) :=
  SourceReceivedConditionalStep.completeSamples (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val
    (nextData runtime nonunit samples selected)

def updatedModel (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) (selected : Bool) :
    SourceConditionalModel.NextModel runtime.tick.next :=
  SourceWindowPosterior.model runtime.tick.next (SourceMinimumSharedNext.next_nonunit runtime)
    (SourceRationalWindowReadout.embed runtime.tick.next (maximumIndex runtime.tick.next) 0
      (updatedSamples runtime nonunit samples selected))

theorem model_realization (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) (selected : Bool) :
    SourceConditionalVector.realizeModel runtime.tick.next (updatedModel runtime nonunit samples selected) =
      nextValue runtime nonunit samples selected := by
  have evaluated := SourceReceivedConditionalStep.complete_roundtrip runtime.tick.next (maximumIndex runtime.tick.next)
    (SourceMinimumSharedNext.next_nonunit runtime) 0 (nextData runtime nonunit samples selected)
  simp only [Nat.add_zero] at evaluated
  have actual := SourceRationalWindowReadout.decoded_model runtime.tick.next (SourceMinimumSharedNext.next_nonunit runtime)
    (updatedSamples runtime nonunit samples selected)
  change SourceCopyCurrentCoordinates.realize runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceRationalWindowReadout.coordinates runtime.tick.next (maximumIndex runtime.tick.next) 0
      (SourceRationalWindowReadout.decode (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val
        (SourceReceivedConditionalStep.completeSamples _ _ _))) = _ at actual
  rw [evaluated] at actual
  exact actual.symm

end
end SourceStableReceivedCount
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
