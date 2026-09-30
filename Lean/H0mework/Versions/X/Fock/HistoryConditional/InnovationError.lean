import H0mework.Versions.X.Fock.HistoryConditional.InnovationFeedback

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInnovation

open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (count observation bornObservation born)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem old_error_decomposition (bound depth : Nat) (guess : Field parity → SourceJointClockGraph.Carrier) :
    SourceConditionalVector.dynamicError (runtimeAt bound) depth guess = SourceConditionalVector.dynamicVariance (runtimeAt bound) depth +
      ∑ i : Fin (bound + 1), (historyPMF bound i).toReal *
        ‖decoder bound depth (observation bound depth i) - guess (observation bound depth i)‖ ^ 2 := by
  have paid := SourceConditionalVector.dynamic_error_decomposition (runtimeAt bound) depth guess
  simp only [← SourceConditionalVector.decoder_at] at paid
  change SourceConditionalVector.dynamicError (runtimeAt bound) depth guess = SourceConditionalVector.dynamicVariance (runtimeAt bound) depth +
    ∑ i : Fin (SourceGeneratedAcquisitionContinuation.inventoryBound (runtimeAt bound) + 1),
      (historyPMF (SourceGeneratedAcquisitionContinuation.inventoryBound (runtimeAt bound)) i).toReal *
        ‖decoder bound depth (observation (SourceGeneratedAcquisitionContinuation.inventoryBound (runtimeAt bound)) depth i) -
          guess (observation (SourceGeneratedAcquisitionContinuation.inventoryBound (runtimeAt bound)) depth i)‖ ^ 2 at paid
  rw [SourceConditionalInventory.runtime_bound] at paid
  exact paid

theorem decoder_bias (bound depth : Nat) :
    ((bound + 1 : Nat) : ℝ) *
      (∑ i : Fin (bound + 1), (historyPMF bound i).toReal *
        ‖decoder bound depth (observation bound depth i) - decoder (bound + 1) depth (observation bound depth i)‖ ^ 2) =
      count bound depth (bornObservation bound depth) *
        ‖decoder bound depth (bornObservation bound depth) - decoder (bound + 1) depth (bornObservation bound depth)‖ ^ 2 := by
  rw [SourceConditionalInventory.sum_count, count_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases same : observation bound depth i = bornObservation bound depth
  · rw [same, if_pos rfl, one_mul]
  · have supported := SourceWeightedRecovery.observed_supported (historyPMF bound) (observation bound depth) i
      (SourceUniformFibreVariance.source_positive bound i)
    rw [decoder_unchanged bound depth _ supported same, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), if_neg same, zero_mul]

theorem minimum_difference (bound depth : Nat) :
    ((bound + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance (runtimeAt (bound + 1)) depth =
      ((bound + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance (runtimeAt bound) depth +
        count bound depth (bornObservation bound depth) *
          ‖decoder bound depth (bornObservation bound depth) - decoder (bound + 1) depth (bornObservation bound depth)‖ ^ 2 +
        ‖born bound - decoder (bound + 1) depth (bornObservation bound depth)‖ ^ 2 := by
  have paid := SourceConditionalInventory.minimum_append bound depth
  dsimp only at paid
  rw [old_error_decomposition, mul_add, decoder_bias] at paid
  exact paid

end
end SourceConditionalInnovation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
