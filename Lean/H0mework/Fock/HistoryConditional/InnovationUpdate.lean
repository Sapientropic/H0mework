import H0mework.Fock.HistoryConditional.InnovationError

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

theorem born_residual (bound depth : Nat)
    (supported : bornObservation bound depth ∈ ((historyPMF bound).map (observation bound depth)).support) :
    born bound - decoder (bound + 1) depth (bornObservation bound depth) =
      ((count bound depth (bornObservation bound depth) / (count bound depth (bornObservation bound depth) + 1) : ℝ) : ℂ) •
        (born bound - decoder bound depth (bornObservation bound depth)) := by
  have nonzero : (count bound depth (bornObservation bound depth) : ℂ) + 1 ≠ 0 := by
    have positive : 0 < count bound depth (bornObservation bound depth) + 1 := by
      have h := count_positive bound depth _ supported
      positivity
    exact_mod_cast positive.ne'
  have scalar : (1 : ℂ) - ((count bound depth (bornObservation bound depth) + 1 : ℝ) : ℂ)⁻¹ =
      ((count bound depth (bornObservation bound depth) / (count bound depth (bornObservation bound depth) + 1) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  calc
    _ = (born bound - decoder bound depth (bornObservation bound depth)) -
        (decoder (bound + 1) depth (bornObservation bound depth) - decoder bound depth (bornObservation bound depth)) := by abel
    _ = _ := by rw [decoder_innovation bound depth supported, ← scalar, sub_smul, one_smul]

theorem innovation_energy (bound depth : Nat)
    (supported : bornObservation bound depth ∈ ((historyPMF bound).map (observation bound depth)).support) :
    count bound depth (bornObservation bound depth) *
        ‖decoder bound depth (bornObservation bound depth) - decoder (bound + 1) depth (bornObservation bound depth)‖ ^ 2 +
      ‖born bound - decoder (bound + 1) depth (bornObservation bound depth)‖ ^ 2 =
      count bound depth (bornObservation bound depth) / (count bound depth (bornObservation bound depth) + 1) *
        ‖born bound - decoder bound depth (bornObservation bound depth)‖ ^ 2 := by
  rw [norm_sub_rev (decoder bound depth _) (decoder (bound + 1) depth _), decoder_innovation bound depth supported, born_residual bound depth supported]
  simp only [norm_smul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs]
  have nonzero : count bound depth (bornObservation bound depth) + 1 ≠ 0 := by
    have h := count_positive bound depth _ supported
    positivity
  field_simp
  ring

theorem minimum_update (bound depth : Nat) :
    ((bound + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance (runtimeAt (bound + 1)) depth =
      ((bound + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance (runtimeAt bound) depth +
        count bound depth (bornObservation bound depth) / (count bound depth (bornObservation bound depth) + 1) *
          ‖born bound - decoder bound depth (bornObservation bound depth)‖ ^ 2 := by
  rw [minimum_difference, add_assoc]
  by_cases supported : bornObservation bound depth ∈ ((historyPMF bound).map (observation bound depth)).support
  · rw [innovation_energy bound depth supported]
  · rw [count_zero bound depth _ supported, decoder_fresh bound depth supported]
    simp only [zero_mul, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]

end
end SourceConditionalInnovation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
