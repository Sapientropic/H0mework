import H0mework.Fock.RetainedCoarsening.Data

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceRetainedReceiver (Raw Frame)
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def realize (runtime : LivingRuntimeState process) :
    Raw (inventoryBound runtime) (maximumIndex runtime).val →ₗ[ℚ] SourceJointClockGraph.Carrier where
  toFun := SourceReceivedConditionalStep.completeValue runtime (maximumIndex runtime) 0
  map_add' left right := by
    rw [SourceReceivedConditionalStep.completeValue, SourceReceivedConditionalStep.completeValue,
      SourceReceivedConditionalStep.completeValue, ← map_add]
    congr 1
    apply Prod.ext
    · funext coordinate
      exact Rat.cast_add _ _
    · exact Prod.ext (Rat.cast_add _ _) (Rat.cast_add _ _)
  map_smul' scalar value := by
    change SourceCopyCurrentCoordinates.realize runtime (maximumIndex runtime) 0
      (SourceRationalWindowReadout.coordinates runtime (maximumIndex runtime) 0 (scalar • value)) =
        (scalar : ℂ) • SourceCopyCurrentCoordinates.realize runtime (maximumIndex runtime) 0
          (SourceRationalWindowReadout.coordinates runtime (maximumIndex runtime) 0 value)
    rw [← map_smul]
    congr 1
    apply Prod.ext
    · funext coordinate
      exact Rat.cast_mul _ _
    · exact Prod.ext (Rat.cast_mul _ _) (Rat.cast_mul _ _)

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

theorem value_merge (runtime : LivingRuntimeState process) (frame : SourceRetainedReceiver.At runtime Fine)
    (forget : Fine → Coarse) (coarse : Coarse) :
    SourceRetainedReceiver.value runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget) coarse =
      ∑ key ∈ frame.keys,
        (weight (inventoryBound runtime) (maximumIndex runtime).val frame forget coarse key : ℂ) •
          SourceRetainedReceiver.value runtime frame key := by
  rw [SourceRetainedReceiver.value, raw_merge]
  change realize runtime (blend _ _ frame forget coarse) = _
  simp only [blend, map_sum, map_smul]
  rfl

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
