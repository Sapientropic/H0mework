import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Conditional

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceRetainedReceiver (At)
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
noncomputable section

def total (table : Table Fine) (forget : Fine → Coarse) (coarse : Coarse) : Nat :=
  ∑ key ∈ table.keys.toFinset, if forget key = coarse then (lookup table key).count else 0

def weight (table : Table Fine) (forget : Fine → Coarse) (coarse : Coarse) (key : Fine) : ℚ :=
  if forget key = coarse then (lookup table key).count / (total table forget coarse : ℚ) else 0

def mixedValue (runtime : LivingRuntimeState process) (table : Table Fine) (forget : Fine → Coarse)
    (coarse : Coarse) : SourceJointClockGraph.Carrier :=
  ∑ key ∈ table.keys.toFinset, (weight table forget coarse key : ℂ) • readValue runtime table key

theorem inventory_source (bound stride : Nat) (table : Table Fine) (frame : SourceRetainedReceiver.Frame Fine bound stride)
    (source : Simulates bound stride table frame) : table.keys.toFinset = frame.keys := by
  ext key
  exact List.mem_toFinset.trans (source.keys key)

theorem weight_source (runtime : LivingRuntimeState process) (table : Table Fine) (frame : At runtime Fine)
    (source : Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (forget : Fine → Coarse) (coarse : Coarse) (key : Fine) :
    weight table forget coarse key =
      SourceRetainedCoarsening.weight (inventoryBound runtime) (maximumIndex runtime).val frame forget coarse key := by
  simp only [weight, total, inventory_source _ _ table frame source, (source.rows _).count_eq,
    SourceRetainedCoarsening.weight, SourceConditionalNativeMerge.inventoryCount]

theorem mixedValue_source (runtime : LivingRuntimeState process) (table : Table Fine) (frame : At runtime Fine) (read : Nat → Fine)
    (source : Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val))
    (forget : Fine → Coarse) (coarse : Coarse) :
    mixedValue runtime table forget coarse = SourceRetainedReceiver.value runtime
      (SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val frame forget) coarse := by
  simp only [mixedValue, inventory_source _ _ table frame source, weight_source runtime table frame source,
    readValue_source runtime table frame read source native keys]
  exact (SourceRetainedCoarsening.value_merge runtime frame forget coarse).symm

end
end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
