import H0mework.Versions.Y.Arithmetic.RieszFiniteSource.Edge
import H0mework.Versions.Y.Arithmetic.MellinProjection.FiniteWindow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteColumns

open Complex MeasureTheory Set
open OriginalRieszSource OriginalRieszFiniteSource
noncomputable section

local notation "q" => (1 / 4 : ℝ)

private theorem outside_smaller {radius larger x : ℝ} (bounded : radius ≤ larger)
    (outside : x ∉ symmetricInterval larger) : x ∉ symmetricInterval radius := by
  intro inside
  exact outside ⟨(neg_le_neg bounded).trans inside.1, inside.2.trans bounded⟩

private theorem gapTail_difference_ae_zero {left right radius : ℝ}
    (leftPositive : 0 < left) (rightPositive : 0 < right)
    (leftBound : left ≤ radius) (rightBound : right ≤ radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, x ∉ symmetricInterval radius →
      (burnolRadiusAmbientCompletedMellinKernelFormula left leftPositive coordinate -
        burnolRadiusAmbientCompletedMellinKernelFormula right rightPositive coordinate : BurnolL2) x = 0 := by
  by_cases ordered : left ≤ right
  · filter_upwards [burnolGapTailFiniteWindow_ae_source leftPositive ordered coordinate]
      with x read outside
    rw [read]
    exact burnolGapTailFiniteWindowRaw_zero_outside leftPositive ordered coordinate
      (outside_smaller rightBound outside)
  · have orderedBack : right ≤ left := (lt_of_not_ge ordered).le
    let first := burnolRadiusAmbientCompletedMellinKernelFormula left leftPositive coordinate
    let second := burnolRadiusAmbientCompletedMellinKernelFormula right rightPositive coordinate
    filter_upwards [burnolGapTailFiniteWindow_ae_source rightPositive orderedBack coordinate,
      Lp.coeFn_sub first second, Lp.coeFn_sub second first] with x read forward backward outside
    change (second - first : BurnolL2) x = _ at read
    rw [backward] at read
    have vanished := read.trans (burnolGapTailFiniteWindowRaw_zero_outside
      rightPositive orderedBack coordinate (outside_smaller leftBound outside))
    change (first - second : BurnolL2) x = 0
    rw [forward]
    simp only [Pi.sub_apply] at vanished ⊢
    linear_combination -vanished

private theorem evenPart_ae_zero {radius : ℝ} (value : BurnolL2)
    (source : ∀ᵐ x : ℝ ∂volume, x ∉ symmetricInterval radius → value x = 0) :
    ∀ᵐ x : ℝ ∂volume, x ∉ symmetricInterval radius → burnolAmbientEvenPart value x = 0 := by
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (value + reflectL2 value),
    Lp.coeFn_add value (reflectL2 value), Lp.coeFn_compMeasurePreserving value negMeasurePreserving,
    source, negMeasurePreserving.quasiMeasurePreserving.ae source]
    with x scalar added reflected atPoint atNegative outside
  have negativeOutside : -x ∉ symmetricInterval radius := by
    intro inside
    apply outside
    exact ⟨by linarith [inside.2], by linarith [inside.1]⟩
  change ((1 / 2 : ℂ) • (value + reflectL2 value) : BurnolL2) x = 0
  rw [scalar]
  change (1 / 2 : ℂ) * (value + reflectL2 value : BurnolL2) x = 0
  rw [added]
  change (1 / 2 : ℂ) * (value x + reflectL2 value x) = 0
  change reflectL2 value x = value (-x) at reflected
  rw [reflected, atPoint outside, atNegative negativeOutside]
  simp

private theorem evenPart_dilation (value : BurnolL2) (shift : ℝ) :
    burnolMultiplicativeDilation shift (burnolAmbientEvenPart value) =
      burnolAmbientEvenPart (burnolMultiplicativeDilation shift value) := by
  unfold burnolAmbientEvenPart
  rw [map_smul, map_add, reflectL2_burnolMultiplicativeDilation]

theorem edgeIntegral_ae_zero (coordinate : BurnolCompletedMellinCoordinate)
    (shift radius : ℝ) (baseBound : q ≤ radius) (movedBound : q * Real.exp (-shift) ≤ radius) :
    ∀ᵐ x : ℝ ∂volume, x ∉ symmetricInterval radius → edgeIntegral coordinate shift x = 0 := by
  let scale := (-star coordinate.value * GapEuler.gapMean q coordinate)⁻¹
  let base := burnolRadiusAmbientCompletedMellinKernelFormula q (by norm_num) coordinate
  let moved := burnolRadiusAmbientCompletedMellinKernelFormula
    (q * Real.exp (-shift)) (mul_pos (by norm_num) (Real.exp_pos _)) coordinate
  let difference := moved - base
  have primitive : edgePrimitive coordinate = scale • burnolAmbientEvenPart base := rfl
  have action : burnolMultiplicativeDilation shift base =
      fullMellinTranslationCharacter (star coordinate.value) shift • moved :=
    burnolRadiusAmbientKernel_dilation (by norm_num) coordinate shift
  have generated : edgeIntegral coordinate shift =
      (scale * fullMellinTranslationCharacter (star coordinate.value) shift) •
        burnolAmbientEvenPart difference := by
    rw [edgeIntegral, primitive, map_smul, evenPart_dilation, action]
    dsimp only [difference]
    simp only [burnolAmbientEvenPart, map_smul, map_sub]
    module
  have finite : ∀ᵐ x : ℝ ∂volume,
      x ∉ symmetricInterval radius → difference x = 0 :=
    gapTail_difference_ae_zero (mul_pos (by norm_num) (Real.exp_pos _)) (by norm_num)
      movedBound baseBound coordinate
  have evenFinite := evenPart_ae_zero difference finite
  rw [generated]
  filter_upwards [Lp.coeFn_smul
    (scale * fullMellinTranslationCharacter (star coordinate.value) shift)
    (burnolAmbientEvenPart difference), evenFinite] with x scalar zero outside
  rw [scalar]
  change (scale * fullMellinTranslationCharacter (star coordinate.value) shift) *
    burnolAmbientEvenPart difference x = 0
  rw [zero outside, mul_zero]

end
end OriginalRieszFiniteColumns
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
