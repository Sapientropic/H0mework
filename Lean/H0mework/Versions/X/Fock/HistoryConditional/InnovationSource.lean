import H0mework.Versions.X.Fock.HistoryConditional.InformationMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInnovation

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

abbrev decoder (bound depth : Nat) : Field parity → SourceJointClockGraph.Carrier :=
  SourceConditionalVector.vectorDecoder (runtimeAt bound) (SourceConditionalModel.dynamicRead (runtimeAt bound) depth)

private theorem decoder_current_mean (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (SourceConditionalInventory.observation (inventoryBound runtime) depth)).support) :
    SourceConditionalVector.vectorDecoder runtime (SourceConditionalModel.dynamicRead runtime depth) value =
      SourceVectorMoment.mean (SourceConditionalInventory.conditional (inventoryBound runtime) depth value supported)
        (SourceConditionalInventory.values (inventoryBound runtime)) := by
  rw [SourceConditionalVector.vectorDecoder, dif_pos (by simpa only [SourceConditionalInventory.observation_original] using supported)]
  exact (SourceConditionalInventory.mean_original runtime depth value supported).symm

theorem decoder_mean (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (SourceConditionalInventory.observation bound depth)).support) :
    decoder bound depth value = SourceVectorMoment.mean (SourceConditionalInventory.conditional bound depth value supported) (SourceConditionalInventory.values bound) := by
  have compatible : value ∈ ((historyPMF (inventoryBound (runtimeAt bound))).map
      (SourceConditionalInventory.observation (inventoryBound (runtimeAt bound)) depth)).support := by
    rw [SourceConditionalInventory.runtime_bound]
    exact supported
  have paid := decoder_current_mean (runtimeAt bound) depth value compatible
  have transport (n m : Nat) (same : n = m)
      (hn : value ∈ ((historyPMF n).map (SourceConditionalInventory.observation n depth)).support)
      (hm : value ∈ ((historyPMF m).map (SourceConditionalInventory.observation m depth)).support) :
      SourceVectorMoment.mean (SourceConditionalInventory.conditional n depth value hn) (SourceConditionalInventory.values n) =
        SourceVectorMoment.mean (SourceConditionalInventory.conditional m depth value hm) (SourceConditionalInventory.values m) := by
    subst m
    rfl
  exact paid.trans (transport _ _ (SourceConditionalInventory.runtime_bound bound) compatible supported)

theorem count_fibre (bound depth : Nat) (value : Field parity) :
    SourceConditionalInventory.count bound depth value =
      (SourceUniformFibreVariance.fibre bound (SourceConditionalInventory.observation bound depth) value).card := by
  rw [SourceConditionalInventory.count, SourceUniformFibreVariance.observed_weight]
  push_cast
  have nonzero : (bound + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem count_sum (bound depth : Nat) (value : Field parity) :
    SourceConditionalInventory.count bound depth value =
      ∑ i : Fin (bound + 1), if SourceConditionalInventory.observation bound depth i = value then (1 : ℝ) else 0 := by
  rw [count_fibre, Finset.sum_boole]
  rfl

theorem count_append (bound depth : Nat) (value : Field parity) :
    SourceConditionalInventory.count (bound + 1) depth value =
      SourceConditionalInventory.count bound depth value + (if SourceConditionalInventory.bornObservation bound depth = value then 1 else 0) := by
  rw [count_sum, count_sum, Fin.sum_univ_castSucc]
  simp only [SourceConditionalInventory.observation_retained]
  rfl

theorem count_positive (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (SourceConditionalInventory.observation bound depth)).support) :
    0 < SourceConditionalInventory.count bound depth value := by
  rw [SourceConditionalInventory.count]
  exact mul_pos (by positivity) (ENNReal.toReal_pos supported (((historyPMF bound).map _).apply_ne_top value))

theorem count_zero (bound depth : Nat) (value : Field parity)
    (missing : value ∉ ((historyPMF bound).map (SourceConditionalInventory.observation bound depth)).support) :
    SourceConditionalInventory.count bound depth value = 0 := by
  rw [SourceConditionalInventory.count, (PMF.apply_eq_zero_iff _ value).mpr missing, ENNReal.toReal_zero, mul_zero]

end
end SourceConditionalInnovation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
