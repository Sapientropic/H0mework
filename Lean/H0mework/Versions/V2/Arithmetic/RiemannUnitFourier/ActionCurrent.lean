import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius

/-! Unit-radius dilation emits an actual Pa current throughout the original annulus.
The same current and its Fourier sibling give the paired source equation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolUnitOne_actualCurrent_memPa (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (lower : (1 / 4 : ℝ) < Real.exp (-shift))
    (upper : Real.exp (-shift) < 4) :
    burnolMultiplicativeDilation shift (burnolUnitTailResponse coordinate 1) -
      fullMellinTranslationCharacter coordinate.value shift • burnolUnitTailResponse coordinate 1 ∈
        burnolOriginalPaInL2 := by
  have bound : (1 * Real.exp (-shift))⁻¹ ≤ (4 : ℝ) := by
    rw [one_mul, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    exact lower.le
  rw [burnolUnitTailResponse_radius_dilation coordinate 1 (by norm_num) (by norm_num) shift bound, one_mul, ← smul_sub]
  apply burnolOriginalPaInL2.smul_mem
  have shellMoved := burnolUnitPowerShellWave_originalPa coordinate _ lower upper
  have shellOne := burnolUnitPowerShellWave_originalPa coordinate 1 (by norm_num) (by norm_num)
  rw [← burnolUnitTailResponse_shell coordinate _ lower upper] at shellMoved
  rw [← burnolUnitTailResponse_shell coordinate 1 (by norm_num) (by norm_num)] at shellOne
  convert burnolOriginalPaInL2.sub_mem shellMoved shellOne using 1
  module

theorem burnolOriginalPaInL2_fourier {value : BurnolL2} (belongs : value ∈ burnolOriginalPaInL2) :
    fourierL2 value ∈ burnolOriginalPaInL2 := by
  obtain ⟨state, stateIn, same⟩ := Submodule.mem_map.mp belongs
  refine Submodule.mem_map.mpr ⟨evenFaceFourierEquiv burnolUnscaledCommonGapRadius state,
    burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange stateIn, ?_⟩
  change fourierL2 (state : BurnolL2) = fourierL2 value
  exact congrArg fourierL2 same

theorem burnolUnitOne_pairedCurrent_memPa (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (forwardLower : (1 / 4 : ℝ) < Real.exp (-shift))
    (forwardUpper : Real.exp (-shift) < 4)
    (inverseLower : (1 / 4 : ℝ) < Real.exp shift) (inverseUpper : Real.exp shift < 4) :
    pairedBurnolMultiplicativeDilation shift
        (burnolUnitTailResponse coordinate 1 + fourierL2 (burnolUnitTailResponse coordinate 1)) -
      pairedMellinTranslationCharacter coordinate.value shift •
        (burnolUnitTailResponse coordinate 1 + fourierL2 (burnolUnitTailResponse coordinate 1)) ∈
          burnolOriginalPaInL2 := by
  let v := burnolUnitTailResponse coordinate 1
  let forward := burnolMultiplicativeDilation shift v -
    fullMellinTranslationCharacter coordinate.value shift • v
  let inverse := burnolMultiplicativeDilation (-shift) v -
    fullMellinTranslationCharacter coordinate.value (-shift) • v
  have forwardIn : forward ∈ burnolOriginalPaInL2 :=
    burnolUnitOne_actualCurrent_memPa coordinate shift forwardLower forwardUpper
  have inverseIn : inverse ∈ burnolOriginalPaInL2 := by
    apply burnolUnitOne_actualCurrent_memPa coordinate (-shift)
    · simpa only [neg_neg] using inverseLower
    · simpa only [neg_neg] using inverseUpper
  have whole := burnolOriginalPaInL2.smul_mem (1 / 2 : ℂ)
    (burnolOriginalPaInL2.add_mem (burnolOriginalPaInL2.add_mem forwardIn inverseIn)
      (burnolOriginalPaInL2.add_mem (burnolOriginalPaInL2_fourier forwardIn) (burnolOriginalPaInL2_fourier inverseIn)))
  have sourceLaw : burnolMultiplicativeDilation shift (fourierL2 v) =
      fourierL2 (burnolMultiplicativeDilation (-shift) v) := by
    rw [fourierL2_burnolMultiplicativeDilation, neg_neg]
  have inverseLaw : burnolMultiplicativeDilation (-shift) (fourierL2 v) =
      fourierL2 (burnolMultiplicativeDilation shift v) := by
    rw [fourierL2_burnolMultiplicativeDilation]
  have character : fullMellinTranslationCharacter coordinate.value (-shift) =
      reciprocalMellinTranslationCharacter coordinate.value shift := by
    unfold fullMellinTranslationCharacter reciprocalMellinTranslationCharacter
    congr 1
    push_cast
    ring
  convert whole using 1
  change pairedBurnolMultiplicativeDilation shift (v + fourierL2 v) -
    pairedMellinTranslationCharacter coordinate.value shift • (v + fourierL2 v) = _
  unfold pairedBurnolMultiplicativeDilation forward inverse
  simp only [smul_apply, add_apply, ContinuousLinearEquiv.coe_coe, map_add, map_sub, map_smul]
  change (1 / 2 : ℂ) • (burnolMultiplicativeDilation shift v + burnolMultiplicativeDilation (-shift) v) +
      (1 / 2 : ℂ) • (burnolMultiplicativeDilation shift (fourierL2 v) +
        burnolMultiplicativeDilation (-shift) (fourierL2 v)) -
      pairedMellinTranslationCharacter coordinate.value shift • (v + fourierL2 v) = _
  rw [sourceLaw, inverseLaw, character]
  unfold pairedMellinTranslationCharacter
  module

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
