import H0mework.Fock.HistoryConditional.ReceivedMergeModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalMerge

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse] [Fintype Fine]
noncomputable section

def information (forget : Fine → Coarse) (bound : Nat)
    (previous : SourceConditionalNativeObservers.State Fine bound) : ℝ :=
  ∑ key : Fine, (previous key).1 / (bound + 1 : ℝ) *
    Real.log ((merge forget bound previous (forget key)).1 / ((previous key).1 : ℝ))

theorem source_sum (read : Nat → Fine) (bound : Nat) (value : Fine → ℝ) :
    (∑ key : Fine, ((SourceConditionalNativeObservers.generate read bound key).1 : ℝ) * value key) =
      ∑ actor : Fin (bound + 1), value (read actor.val) := by
  simp_rw [SourceConditionalNativePosterior.count_fibre]
  have paid := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Fin (bound + 1)))) (t := (Finset.univ : Finset Fine))
    (g := fun actor => read actor.val) (fun _ _ => Finset.mem_univ _ ) value
  simpa only [SourceUniformFibreVariance.fibre, Finset.sum_const, nsmul_eq_mul] using paid

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

theorem information_source (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    information forget (inventoryBound runtime) (SourceConditionalNativeObservers.generate read (inventoryBound runtime)) =
      SourceConditionalInformationLoss.amount runtime read forget := by
  rw [information, source_generated, SourceConditionalInformationLoss.amount]
  simp_rw [SourceUniformFibreVariance.source_weight, SourceConditionalNativeMerge.count_generated]
  have paid := source_sum read (inventoryBound runtime) (fun key =>
    (inventoryBound runtime + 1 : ℝ)⁻¹ *
      Real.log (((SourceConditionalNativeObservers.generate (forget ∘ read) (inventoryBound runtime) (forget key)).1 : ℝ) /
        ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1 : ℝ)))
  simpa only [div_eq_mul_inv, mul_assoc, one_mul] using paid

theorem received_information (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    information forget (inventoryBound runtime)
      (SourceFibreExactState.restoreState (inventoryBound runtime) (maximumIndex runtime).val nonunit samples) =
        SourceConditionalInformationLoss.amount runtime read forget := by
  rw [SourceFibreExactState.state_source runtime nonunit samples read budgets]
  exact information_source runtime read forget

end
end SourceReceivedConditionalMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
