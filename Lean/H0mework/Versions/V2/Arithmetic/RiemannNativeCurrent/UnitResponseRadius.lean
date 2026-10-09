import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseAction

/-! The actual unit source and its remainder response follow dilation at every admitted radius. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem burnolRadiusNormalizedUnitTail_dilation (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0 < radius) (shift : ℝ) :
    burnolMultiplicativeDilation shift (burnolRadiusNormalizedUnitTail coordinate radius positive) =
      fullMellinTranslationCharacter coordinate.value shift •
        burnolRadiusNormalizedUnitTail coordinate (radius * Real.exp (-shift)) (by positivity) := by
  let dual : BurnolCompletedMellinCoordinate := ⟨star coordinate.value,
    by simpa only [Complex.star_def, Complex.conj_re] using coordinate.rightHalf,
    by simpa only [Complex.star_def, Complex.conj_re] using coordinate.belowOne⟩
  have actual := burnolRadiusMellinTail_dilation positive dual shift
  dsimp only [dual] at actual
  rw [star_star] at actual
  unfold burnolRadiusNormalizedUnitTail
  dsimp only
  rw [map_neg, map_add, ← reflectL2_burnolMultiplicativeDilation, actual,
    map_smul, ← smul_add, smul_neg]

theorem burnolUnitTailResponse_radius_dilation (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0 < radius) (radiusBound : radius⁻¹ ≤ 4)
    (shift : ℝ) (movedBound : (radius * Real.exp (-shift))⁻¹ ≤ 4) :
    burnolMultiplicativeDilation shift (burnolUnitTailResponse coordinate radius) =
      fullMellinTranslationCharacter coordinate.value shift •
        burnolUnitTailResponse coordinate (radius * Real.exp (-shift)) := by
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  change (Lp.toTemperedDistributionCLM ℂ volume 2
      (burnolMultiplicativeDilation shift (burnolUnitTailResponse coordinate radius))) test =
    (Lp.toTemperedDistributionCLM ℂ volume 2
      (fullMellinTranslationCharacter coordinate.value shift •
        burnolUnitTailResponse coordinate (radius * Real.exp (-shift)))) test
  have read := burnolRemainderRealization_dilation
    (burnolRadiusNormalizedUnitTail coordinate radius positive)
    (burnolUnitTailResponse coordinate radius)
    (burnolUnitTailResponse_realizes coordinate radius positive radiusBound) shift test
  rw [burnolRadiusNormalizedUnitTail_dilation, ← burnolRemainderSourceReadCLM_apply,
    map_smul, burnolRemainderSourceReadCLM_apply,
    burnolUnitTailResponse_realizes coordinate _ (by positivity) movedBound] at read
  exact read.symm.trans (by simp only [map_smul, smul_apply])

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
