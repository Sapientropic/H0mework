import H0mework.Versions.X.Fock.RetainedReceiver.Data

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*} [DecidableEq Key]

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem start_native (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2) :
    (start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples).native =
        SourceConditionalNativeObservers.generate read (inventoryBound runtime) :=
  SourceReceivedKeyInventory.restored_source runtime nonunit read samples budgets

theorem start_raw (bound stride : Nat) (nonunit : stride ≠ 0) (keys : Finset Key)
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples bound (stride + 1)) (key : Key) :
    rawAt bound stride (start bound stride nonunit keys samples) key =
      SourceRationalWindowReadout.decode bound stride (SourceReceivedKeyInventory.extend bound stride keys samples key) := by
  dsimp only [rawAt, start, SourceReceivedKeyInventory.extend]
  by_cases present : key ∈ keys
  · simp only [dif_pos present]
  · simp only [dif_neg present]
    symm
    apply Prod.ext
    · funext coordinate
      simp [SourceRationalWindowReadout.decode, SourceRationalWindowReadout.hilbert,
        SourceRationalWindowReadout.mass, SourceRationalWindowReadout.clock, SourceRationalWindowReadout.column]
    · simp [SourceRationalWindowReadout.decode, SourceRationalWindowReadout.mass,
        SourceRationalWindowReadout.clock, SourceRationalWindowReadout.column]

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
