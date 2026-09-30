import H0mework.Versions.X.Fock.HistoryConditional.ReceivedMergeObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalMerge

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem parity_positive (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : ZMod 2 → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key : ZMod 2, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (fun n : Nat => (n : ZMod 2)) key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    0 < lostEnergy runtime nonunit samples SourceConditionalMergeLoss.forgetAll := by
  rw [lost_energy_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) SourceConditionalMergeLoss.forgetAll budgets]
  apply SourceConditionalMergeLoss.parity_gap_positive
  have bound := SourceCopyCurrentCoordinates.maximum_index_val runtime
  omega

end
end SourceReceivedConditionalMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
