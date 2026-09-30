import H0mework.Versions.Y.Arithmetic.RieszGreen.KernelGram
import H0mework.Versions.Y.Arithmetic.MellinProjection.FiniteWindow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Complex Filter MeasureTheory Set
open OriginalRieszSourceGreen
noncomputable section

local notation "q" => (1 / 4 : ℝ)

private theorem gap_difference_mass (coordinate : BurnolCompletedMellinCoordinate)
    (left right : ℝ) (leftPositive : 0 < left) (rightPositive : 0 < right) :
    Integrable (burnolRadiusAmbientCompletedMellinKernelFormula left leftPositive coordinate -
      burnolRadiusAmbientCompletedMellinKernelFormula right rightPositive coordinate : BurnolL2) ∧
    (∫ x : ℝ, (burnolRadiusAmbientCompletedMellinKernelFormula left leftPositive coordinate -
      burnolRadiusAmbientCompletedMellinKernelFormula right rightPositive coordinate : BurnolL2) x) = 0 := by
  by_cases ordered : left ≤ right
  · have read := burnolGapTailFiniteWindow_ae_source leftPositive ordered coordinate
    refine ⟨(burnolGapTailFiniteWindow_integrable leftPositive ordered coordinate).congr read.symm, ?_⟩
    rw [integral_congr_ae read]
    exact burnolGapTailFiniteWindow_integral_zero leftPositive ordered coordinate
  · have reverse := burnolGapTailFiniteWindow_ae_source rightPositive (lt_of_not_ge ordered).le coordinate
    have reverseInt := (burnolGapTailFiniteWindow_integrable rightPositive (lt_of_not_ge ordered).le coordinate).congr reverse.symm
    have reverseMass := (integral_congr_ae reverse).trans
      (burnolGapTailFiniteWindow_integral_zero rightPositive (lt_of_not_ge ordered).le coordinate)
    let difference := burnolRadiusAmbientCompletedMellinKernelFormula right rightPositive coordinate -
      burnolRadiusAmbientCompletedMellinKernelFormula left leftPositive coordinate
    change (∫ x : ℝ, difference x) = 0 at reverseMass
    have identity : (burnolRadiusAmbientCompletedMellinKernelFormula left leftPositive coordinate -
        burnolRadiusAmbientCompletedMellinKernelFormula right rightPositive coordinate : BurnolL2) = -difference := by
      dsimp [difference]
      abel
    rw [identity]
    refine ⟨reverseInt.neg.congr (Lp.coeFn_neg difference).symm, ?_⟩
    rw [integral_congr_ae (Lp.coeFn_neg difference)]
    change (∫ x : ℝ, -difference x) = 0
    rw [integral_neg, reverseMass, neg_zero]

private theorem evenPart_mass (value : BurnolL2) (integrable : Integrable value)
    (mass : (∫ x : ℝ, value x) = 0) :
    Integrable (burnolAmbientEvenPart value) ∧ (∫ x : ℝ, burnolAmbientEvenPart value x) = 0 := by
  have negativeInt : Integrable (fun x : ℝ => value (-x)) := by
    simpa only [neg_one_mul] using integrable.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
  have negativeMass : (∫ x : ℝ, value (-x)) = ∫ x : ℝ, value x := by
    simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using
      (Measure.integral_comp_mul_left (fun x : ℝ => value x) (-1 : ℝ))
  have read := burnolEvenRaw_ae value (value : ℝ → ℂ) Filter.EventuallyEq.rfl
  refine ⟨((integrable.add negativeInt).const_mul (1 / 2 : ℂ)).congr read.symm, ?_⟩
  rw [integral_congr_ae read]
  unfold burnolEvenRaw
  rw [integral_const_mul, integral_add integrable negativeInt, negativeMass, mass, add_zero, mul_zero]

def gapDilationDifference (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  burnolMultiplicativeDilation shift (gapState coordinate) -
    fullMellinTranslationCharacter (star coordinate.value) shift • gapState coordinate

private theorem gapDilationDifference_mass (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    Integrable (gapDilationDifference coordinate shift) ∧
      (∫ x : ℝ, gapDilationDifference coordinate shift x) = 0 := by
  let moved := burnolRadiusAmbientCompletedMellinKernelFormula (q * Real.exp (-shift))
    (mul_pos (by norm_num) (Real.exp_pos _)) coordinate
  let base := burnolRadiusAmbientCompletedMellinKernelFormula q (by norm_num) coordinate
  let difference := moved - base
  let character := fullMellinTranslationCharacter (star coordinate.value) shift
  have action : burnolMultiplicativeDilation shift base = character • moved :=
    burnolRadiusAmbientKernel_dilation (by norm_num) coordinate shift
  have evenAction : burnolMultiplicativeDilation shift (burnolAmbientEvenPart base) =
      burnolAmbientEvenPart (burnolMultiplicativeDilation shift base) := by
    unfold burnolAmbientEvenPart
    rw [map_smul, map_add, reflectL2_burnolMultiplicativeDilation]
  have generated : gapDilationDifference coordinate shift = character • burnolAmbientEvenPart difference := by
    change burnolMultiplicativeDilation shift (burnolAmbientEvenPart base) -
      character • burnolAmbientEvenPart base = _
    rw [evenAction, action]
    dsimp [difference]
    unfold burnolAmbientEvenPart
    simp only [map_smul, map_sub]
    module
  have finite := gap_difference_mass coordinate (q * Real.exp (-shift)) q
    (mul_pos (by norm_num) (Real.exp_pos _)) (by norm_num)
  have even := evenPart_mass difference finite.1 finite.2
  rw [generated]
  refine ⟨(even.1.const_mul character).congr (Lp.coeFn_smul character (burnolAmbientEvenPart difference)).symm, ?_⟩
  rw [integral_congr_ae (Lp.coeFn_smul character (burnolAmbientEvenPart difference))]
  change (∫ x : ℝ, character * burnolAmbientEvenPart difference x) = 0
  rw [integral_const_mul, even.2, mul_zero]

theorem gapDilationDifference_integrable (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    Integrable (gapDilationDifference coordinate shift) := (gapDilationDifference_mass coordinate shift).1

theorem gapDilationDifference_integral_zero (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    (∫ x : ℝ, gapDilationDifference coordinate shift x) = 0 := (gapDilationDifference_mass coordinate shift).2

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
