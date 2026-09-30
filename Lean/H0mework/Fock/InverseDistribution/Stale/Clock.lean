import H0mework.Fock.InverseDistribution.Stale.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionStale

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceInverseDistributionOptimalBirth
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

private theorem mean_clock_le (bound : Nat) (p : PMF (Fin (bound + 1))) :
    (SourceJointClockGraph.clock (SourceVectorMoment.mean p (SourceConditionalInventory.values bound))).re ≤
      ((bound + 2 : Nat) : ℝ) := by
  simp only [SourceVectorMoment.mean, map_sum, map_smul, actor_clock, Complex.re_sum,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.natCast_re]
  have weights := congrArg Complex.re (SourceVectorMoment.weights p)
  simp only [Complex.re_sum, Complex.ofReal_re, Complex.one_re] at weights
  calc
    _ ≤ ∑ actor : Fin (bound + 1), (p actor).toReal * ((bound + 2 : Nat) : ℝ) := by
      apply Finset.sum_le_sum
      intro actor _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast (show actor.val + 2 ≤ bound + 2 by omega)
    _ = _ := by rw [← Finset.sum_mul, weights, one_mul]

theorem decoder_clock_le {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (read : Nat → Key) (key : Key) :
    (SourceJointClockGraph.clock (SourceConditionalNativePosterior.decoder runtime read key)).re ≤
      ((inventoryBound runtime + 2 : Nat) : ℝ) := by
  classical
  by_cases supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support
  · rw [SourceConditionalNativePosterior.decoder_mean runtime read key supported]
    simpa only [← SourceConditionalInventory.values_original] using
      mean_clock_le (inventoryBound runtime) (SourceConditionalHistory.conditional
        (historyPMF (inventoryBound runtime)) (fun actor : Actors runtime => read actor.val) key supported)
  · rw [SourceConditionalNativePosterior.decoder_original, SourceConditionalVector.vectorDecoder, dif_neg supported, map_zero]
    change (0 : ℝ) ≤ _
    positivity

theorem projected_born_ne {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) :
    project depth word (SourceConditionalInventory.born (inventoryBound runtime)) ≠
      decoder runtime depth word read (read (inventoryBound runtime + 1)) := by
  intro same
  have clocks := congrArg (fun value : SourceJointClockGraph.Carrier => (SourceJointClockGraph.clock value).re) same
  simp only [decoder, project_clock, born_clock, Complex.natCast_re] at clocks
  have upper := decoder_clock_le runtime read (read (inventoryBound runtime + 1))
  rw [← clocks] at upper
  push_cast at upper
  linarith

end
end SourceInverseDistributionStale
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
