import H0mework.Versions.X.Fock.HistoryConditional.InnovationMean

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInnovation

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
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

def updateDecoder (bound depth : Nat) (value : Field parity) : SourceJointClockGraph.Carrier :=
  if bornObservation bound depth = value then
    decoder bound depth value + ((count bound depth value + 1 : ℝ) : ℂ)⁻¹ • (born bound - decoder bound depth value)
  else decoder bound depth value

theorem decoder_missing (bound depth : Nat) (value : Field parity)
    (missing : value ∉ ((historyPMF bound).map (observation bound depth)).support) : decoder bound depth value = 0 := by
  have compatible : value ∉ ((historyPMF (inventoryBound (runtimeAt bound))).map
      (observation (inventoryBound (runtimeAt bound)) depth)).support := by
    rw [SourceConditionalInventory.runtime_bound]
    exact missing
  unfold decoder SourceConditionalVector.vectorDecoder
  exact dif_neg (by simpa only [SourceConditionalInventory.observation_original] using compatible)

theorem update_decoder (bound depth : Nat) : updateDecoder bound depth = decoder (bound + 1) depth := by
  funext value
  by_cases atBirth : bornObservation bound depth = value
  · subst value
    rw [updateDecoder, if_pos rfl]
    by_cases supported : bornObservation bound depth ∈ ((historyPMF bound).map (observation bound depth)).support
    · rw [← decoder_innovation bound depth supported]
      abel
    · rw [count_zero bound depth _ supported, decoder_fresh bound depth supported]
      simp only [zero_add, Complex.ofReal_one, inv_one, one_smul]
      abel
  · rw [updateDecoder, if_neg atBirth]
    by_cases supported : value ∈ ((historyPMF bound).map (observation bound depth)).support
    · exact (decoder_unchanged bound depth value supported (Ne.symm atBirth)).symm
    · have missingNext : value ∉ ((historyPMF (bound + 1)).map (observation (bound + 1) depth)).support := by
        rw [SourceConditionalInventory.new_support_iff]
        exact not_or.mpr ⟨supported, Ne.symm atBirth⟩
      rw [decoder_missing bound depth value supported, decoder_missing (bound + 1) depth value missingNext]

theorem update_attains (bound depth : Nat) :
    SourceConditionalVector.dynamicError (runtimeAt (bound + 1)) depth (updateDecoder bound depth) =
      SourceConditionalVector.dynamicVariance (runtimeAt (bound + 1)) depth := by
  rw [update_decoder]
  exact SourceConditionalVector.dynamic_attains _ _

theorem update_recovers_fresh (bound depth : Nat)
    (fresh : bornObservation bound depth ∉ ((historyPMF bound).map (observation bound depth)).support) :
    updateDecoder bound depth (bornObservation bound depth) = born bound := by
  rw [update_decoder, decoder_fresh bound depth fresh]

end
end SourceConditionalInnovation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
