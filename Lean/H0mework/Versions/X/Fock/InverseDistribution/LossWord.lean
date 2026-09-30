import H0mework.Versions.X.Fock.InverseDistribution.LossGeometry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionLoss

noncomputable section

theorem word_hilbert (bound : Nat) (weights : Fin (bound + 1) → ℚ) :
    SourceSuccessorBoundary.readWord
      (SourceConditionalRationalStream.embedWord (SourceConditionalNativeKeys.word bound weights)) =
      ∑ actor : Fin (bound + 1), lp.single 2 (actor.val + 1) (weights actor : ℂ) := by
  simp only [SourceConditionalNativeKeys.word, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    SourceConditionalNativeKeys.source_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  apply Finset.sum_congr rfl
  intro actor _
  change SourceSuccessorBoundary.readWord
    (Finsupp.mapRange (Algebra.linearMap ℚ ℂ) (map_zero (Algebra.linearMap ℚ ℂ)) (Finsupp.single (actor.val + 1) (weights actor))) = _
  rw [Finsupp.mapRange_single, SourceSuccessorBoundary.readWord_single]
  simp only [SourceOwnedObservationHistory.SourceShift.basis, ← lp.single_smul, smul_eq_mul, mul_one]
  congr 1

theorem word_hilbert_norm (bound : Nat) (weights : Fin (bound + 1) → ℚ) :
    ‖SourceSuccessorBoundary.readWord
      (SourceConditionalRationalStream.embedWord (SourceConditionalNativeKeys.word bound weights))‖ ^ 2 =
      ∑ actor : Fin (bound + 1), ‖(weights actor : ℂ)‖ ^ 2 := by
  classical
  let indices : Finset Nat := Finset.univ.image (fun actor : Fin (bound + 1) => actor.val + 1)
  let coefficients := SourceConditionalRationalStream.embedWord (SourceConditionalNativeKeys.word bound weights)
  have coefficient (actor : Fin (bound + 1)) : coefficients (actor.val + 1) = (weights actor : ℂ) := by
    change ((SourceConditionalNativeKeys.word bound weights (actor.val + 1) : ℚ) : ℂ) = _
    rw [SourceConditionalNativeKeys.word_coefficient]
  have injective : Function.Injective (fun actor : Fin (bound + 1) => actor.val + 1) := by
    intro left right same
    exact Fin.ext (Nat.add_right_cancel same)
  have generated : SourceSuccessorBoundary.readWord coefficients =
      ∑ index ∈ indices, lp.single 2 index (coefficients index) := by
    rw [word_hilbert]
    dsimp only [indices]
    rw [Finset.sum_image (fun left _ right _ same => injective same)]
    simp only [coefficient]
  have paid := lp.norm_sum_single (E := fun _ : Nat => ℂ) (p := 2) (by norm_num) coefficients indices
  rw [← generated] at paid
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at paid
  rw [paid]
  dsimp only [indices]
  rw [Finset.sum_image (fun left _ right _ same => injective same)]
  simp only [coefficient]

end
end SourceInverseDistributionLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
