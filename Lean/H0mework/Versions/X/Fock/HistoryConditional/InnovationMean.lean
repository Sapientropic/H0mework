import H0mework.Versions.X.Fock.HistoryConditional.InnovationSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInnovation

open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (count observation bornObservation born)
open scoped Classical
noncomputable section

theorem decoder_mean_append (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (observation bound depth)).support) :
    (count (bound + 1) depth value : ℂ) • decoder (bound + 1) depth value =
      (count bound depth value : ℂ) • decoder bound depth value +
        (if bornObservation bound depth = value then born bound else 0) := by
  rw [decoder_mean bound depth value supported,
    decoder_mean (bound + 1) depth value (SourceConditionalInventory.supported_retained bound depth value supported)]
  exact SourceConditionalInventory.conditional_mean_append bound depth value supported

theorem decoder_unchanged (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (observation bound depth)).support)
    (different : value ≠ bornObservation bound depth) : decoder (bound + 1) depth value = decoder bound depth value := by
  have paid := decoder_mean_append bound depth value supported
  simp only [count_append, if_neg different.symm, add_zero] at paid
  exact smul_right_injective SourceJointClockGraph.Carrier (show (count bound depth value : ℂ) ≠ 0 from
    Complex.ofReal_ne_zero.mpr (count_positive bound depth value supported).ne') paid

theorem decoder_birth_mean (bound depth : Nat)
    (supported : bornObservation bound depth ∈ ((historyPMF bound).map (observation bound depth)).support) :
    ((count bound depth (bornObservation bound depth) + 1 : ℝ) : ℂ) • decoder (bound + 1) depth (bornObservation bound depth) =
      (count bound depth (bornObservation bound depth) : ℂ) • decoder bound depth (bornObservation bound depth) + born bound := by
  have paid := decoder_mean_append bound depth (bornObservation bound depth) supported
  simpa only [count_append, if_pos rfl, ite_true] using paid

theorem decoder_fresh (bound depth : Nat)
    (fresh : bornObservation bound depth ∉ ((historyPMF bound).map (observation bound depth)).support) :
    decoder (bound + 1) depth (bornObservation bound depth) = born bound := by
  rw [decoder_mean (bound + 1) depth _ (SourceConditionalInventory.born_supported bound depth)]
  exact SourceConditionalInventory.fresh_recovers bound depth fresh

private theorem mean_difference {E : Type*} [AddCommGroup E] [Module ℂ E] (weight : ℂ)
    (nonzero : weight + 1 ≠ 0) (before added after : E)
    (update : (weight + 1) • after = weight • before + added) :
    after - before = (weight + 1)⁻¹ • (added - before) := by
  apply smul_right_injective E nonzero
  change (weight + 1) • (after - before) = (weight + 1) • ((weight + 1)⁻¹ • (added - before))
  rw [smul_smul, mul_inv_cancel₀ nonzero, one_smul, smul_sub, update]
  module

theorem decoder_innovation (bound depth : Nat)
    (supported : bornObservation bound depth ∈ ((historyPMF bound).map (observation bound depth)).support) :
    decoder (bound + 1) depth (bornObservation bound depth) - decoder bound depth (bornObservation bound depth) =
      ((count bound depth (bornObservation bound depth) + 1 : ℝ) : ℂ)⁻¹ •
        (born bound - decoder bound depth (bornObservation bound depth)) := by
  have nonzero : (count bound depth (bornObservation bound depth) : ℂ) + 1 ≠ 0 := by
    have positive : 0 < count bound depth (bornObservation bound depth) + 1 := by
      have h := count_positive bound depth _ supported
      positivity
    exact_mod_cast positive.ne'
  have paid := decoder_birth_mean bound depth supported
  simp only [Complex.ofReal_add, Complex.ofReal_one] at paid ⊢
  exact mean_difference _ nonzero _ _ _ paid

end
end SourceConditionalInnovation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
