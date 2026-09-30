import H0mework.Versions.X.Fock.FibreExactState.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFibreExactState

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem restored_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Key) (key : Key)
    (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    restore (inventoryBound runtime) (maximumIndex runtime).val nonunit samples =
      SourceConditionalNativeObservers.generate read (inventoryBound runtime) key := by
  have recovered := support_complete runtime nonunit samples read key budget
  unfold restore
  rw [recovered]
  dsimp only
  apply Prod.ext
  · exact (SourceConditionalNativePosterior.count_fibre read (inventoryBound runtime) key).symm
  · funext actor
    rw [SourceConditionalNativePosterior.weight_fibre, ← SourceConditionalNativePosterior.count_fibre]
    simp only [SourceUniformFibreVariance.fibre_mem]

theorem state_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Key)
    (budgets : ∀ key : Key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (received key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    restoreState (inventoryBound runtime) (maximumIndex runtime).val nonunit received =
      SourceConditionalNativeObservers.generate read (inventoryBound runtime) := by
  funext key
  exact restored_source runtime nonunit (received key) read key (budgets key)

end
end SourceFibreExactState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
