import H0mework.Fock.HistoryConditional.ReceivedMergeBudget

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalMerge

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse] [Fintype Fine]

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton

theorem information_next (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    (inventoryBound runtime + 2 : ℝ) * information forget (inventoryBound runtime + 1)
      (SourceFibreExactState.next (inventoryBound runtime) (maximumIndex runtime).val nonunit samples (read runtime.tick.next.state)) =
      (inventoryBound runtime + 1 : ℝ) * information forget (inventoryBound runtime)
        (SourceFibreExactState.restoreState (inventoryBound runtime) (maximumIndex runtime).val nonunit samples) +
        SourceConditionalNativeBirth.informationIncrement
          (received forget (inventoryBound runtime) (maximumIndex runtime).val nonunit samples (forget (read runtime.tick.next.state))).1 -
        SourceConditionalNativeBirth.informationIncrement
          (SourceFibreExactState.restoreState (inventoryBound runtime) (maximumIndex runtime).val nonunit samples (read runtime.tick.next.state)).1 := by
  have next_source : information forget (inventoryBound runtime + 1)
      (SourceConditionalNativeObservers.generate read (inventoryBound runtime + 1)) =
        SourceConditionalInformationLoss.amount runtime.tick.next read forget := by
    rw [← SourceActualImageStep.next_bound runtime]
    exact information_source runtime.tick.next read forget
  have receipt := congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))
  rw [SourceFibreExactState.next_source runtime nonunit samples read budgets, next_source,
    SourceFibreExactState.state_source runtime nonunit samples read budgets, information_source,
    received_source runtime nonunit samples read forget budgets, receipt]
  have paid := SourceConditionalNativeBirth.amount_next runtime read forget
  rw [SourceConditionalNativeMerge.count_generated, SourceActualImageStep.next_bound runtime] at paid
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using paid

end
end SourceReceivedConditionalMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
