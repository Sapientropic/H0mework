import H0mework.Fock.HistoryConditional.WindowPosteriorNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPosterior

open SourceCopyCurrentCoordinates (maximumIndex)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open SourceConditionalNativePosterior (decoder)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem exact_support (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    SourcePosteriorStability.restoredSupport runtime
      (model runtime nonunit (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key))) =
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (fun actor => read actor.val) key := by
  apply support_from_precision runtime nonunit read key supported
  simp only [sub_self, SourceWindowPrecision.sampleEnergy, Pi.zero_apply, norm_zero,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero]
  exact sq_pos_of_pos (SourcePosteriorStability.threshold_positive runtime)

theorem next_support (runtime : LivingRuntimeState process) (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (fun actor : Actors runtime.tick.next => read actor.val)).support)
    (samples : SourceOperatorObservationAcquisition.Window runtime.tick.next (maximumIndex runtime.tick.next))
    (budget : SourceWindowPrecision.gain runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) 0 *
      SourceWindowPrecision.sampleEnergy runtime.tick.next (maximumIndex runtime.tick.next)
        (samples - recordedPrefix runtime.tick.next (maximumIndex runtime.tick.next) 0 ((maximumIndex runtime.tick.next).val + 1)
          (decoder runtime.tick.next read key)) < SourcePosteriorStability.threshold runtime.tick.next ^ 2) :
    SourcePosteriorStability.restoredSupport runtime.tick.next (model runtime.tick.next (SourceMinimumSharedNext.next_nonunit runtime) samples) =
      SourceUniformFibreVariance.fibre (inventoryBound runtime.tick.next) (fun actor => read actor.val) key :=
  support_from_precision runtime.tick.next (SourceMinimumSharedNext.next_nonunit runtime) read key supported samples budget

end
end SourceWindowPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
