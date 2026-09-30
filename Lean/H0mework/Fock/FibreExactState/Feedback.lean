import H0mework.Fock.FibreExactState.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFibreExactState

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem next_residual (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Key) (key : Key)
    (budgets : ∀ key : Key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (received key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    SourceConditionalVector.realizeModel runtime.tick.next
      (SourceStableReceivedCount.updatedModel runtime nonunit (received key) (decide (key = read runtime.tick.next.state))) -
      SourceConditionalVector.realizeModel runtime.tick.next (nextModel runtime nonunit received (read runtime.tick.next.state) key) =
      if key = read runtime.tick.next.state then
        (SourceStableReceivedCount.contraction (restoreState (inventoryBound runtime) (maximumIndex runtime).val nonunit received key).1 : ℂ) •
          residual runtime nonunit (received key)
      else residual runtime nonunit (received key) := by
  have old_value : SourceConditionalVector.realizeModel runtime (observed runtime nonunit (received key)) =
      SourceReceivedConditionalStep.completeValue runtime (maximumIndex runtime) 0
        (SourceRationalWindowReadout.decode (inventoryBound runtime) (maximumIndex runtime).val (received key)) :=
    (SourceRationalWindowReadout.decoded_model runtime nonunit (received key)).symm
  rw [SourceStableReceivedCount.model_realization, next_model_source runtime nonunit received read key budgets,
    residual, old_value, model_source runtime nonunit (received key) read key (budgets key),
    restoreState, restored_source runtime nonunit (received key) read key (budgets key)]
  exact SourceStableReceivedCount.residual_from_precision runtime nonunit (received key) read key (budgets key)

end
end SourceFibreExactState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
