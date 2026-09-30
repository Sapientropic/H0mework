import H0mework.Fock.StableReceivedCount.Absent

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceStableReceivedCount

def stepData (bound stride nextStride : Nat) (nonunit : stride ≠ 0)
    (samples : SourceRationalWindowReadout.Samples bound (stride + 1)) (selected : Bool) :
    (Fin ((bound + 2) * (nextStride + 1)) → ℚ) × ℚ × ℚ :=
  SourceReceivedConditionalStep.advanceData bound stride nextStride (count bound stride nonunit samples) selected
    (SourceRationalWindowReadout.decode bound stride samples)

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def nextData (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) (selected : Bool) :
    (Fin ((inventoryBound runtime.tick.next + 1) * ((maximumIndex runtime.tick.next).val + 1)) → ℚ) × ℚ × ℚ :=
  SourceReceivedConditionalStep.nextData runtime (maximumIndex runtime)
    (count (inventoryBound runtime) (maximumIndex runtime).val nonunit samples) selected
    (SourceRationalWindowReadout.decode (inventoryBound runtime) (maximumIndex runtime).val samples)

def nextValue (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) (selected : Bool) :
    SourceJointClockGraph.Carrier :=
  SourceReceivedConditionalStep.completeValue runtime.tick.next (maximumIndex runtime.tick.next) 0 (nextData runtime nonunit samples selected)

theorem next_value_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) (selected : Bool) :
    nextValue runtime nonunit samples selected =
      let old := SourceReceivedConditionalStep.completeValue runtime (maximumIndex runtime) 0
        (SourceRationalWindowReadout.decode (inventoryBound runtime) (maximumIndex runtime).val samples)
      if selected then old +
        ((((count (inventoryBound runtime) (maximumIndex runtime).val nonunit samples + 1 : Nat) : ℚ)⁻¹) : ℂ) •
          (SourceConditionalInventory.born (inventoryBound runtime) - old)
      else old :=
  SourceReceivedConditionalStep.next_value_source runtime (maximumIndex runtime) _ _ _

end
end SourceStableReceivedCount
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
