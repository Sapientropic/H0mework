import H0mework.Fock.StableReceivedCount.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFibreExactState

def restore (bound stride : Nat) (nonunit : stride ≠ 0)
    (samples : SourceRationalWindowReadout.Samples bound (stride + 1)) : Nat × (Fin (bound + 1) → ℚ) :=
  let retained := SourceStableReceivedCount.support bound stride nonunit samples
  (retained.card, fun actor => if actor ∈ retained then (retained.card : ℚ)⁻¹ else 0)

def restoreState {Key : Type*} (bound stride : Nat) (nonunit : stride ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples bound (stride + 1)) : SourceConditionalNativeObservers.State Key bound :=
  fun key => restore bound stride nonunit (received key)

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem support_complete (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Key) (key : Key)
    (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    SourceStableReceivedCount.support (inventoryBound runtime) (maximumIndex runtime).val nonunit samples =
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (fun actor => read actor.val) key := by
  classical
  by_cases present : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support
  · rw [SourceStableReceivedCount.support_source]
    exact SourceWindowPosterior.support_from_precision runtime nonunit read key present _ budget
  · have actual := SourceStableReceivedCount.count_complete runtime nonunit samples read key budget
    rw [SourceStableReceivedCount.absent_state runtime read key present] at actual
    have empty : SourceStableReceivedCount.support (inventoryBound runtime) (maximumIndex runtime).val nonunit samples = ∅ :=
      Finset.card_eq_zero.mp actual
    have source := SourceConditionalNativePosterior.count_fibre read (inventoryBound runtime) key
    rw [SourceStableReceivedCount.absent_state runtime read key present] at source
    exact empty.trans (Finset.card_eq_zero.mp source.symm).symm

end
end SourceFibreExactState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
