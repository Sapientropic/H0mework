import H0mework.Versions.V2.Arithmetic.RieszSynthesis.WholeSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSynthesis

open Complex MeasureTheory
open OriginalRieszFiniteSource
noncomputable section

theorem forcingIntegral_zero (coordinate : BurnolCompletedMellinCoordinate) :
    forcingIntegral coordinate 0 = 0 := by
  apply LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (forcingIntegral coordinate 0)) test =
    (Lp.toTemperedDistributionCLM ℂ volume 2 0) test
  rw [map_zero]
  simpa only [Lp.toTemperedDistributionCLM_apply, intervalIntegral.integral_same, zero_apply]
    using forcingIntegral_read coordinate test 0

theorem wholeSynthesis_zero (coordinate : BurnolCompletedMellinCoordinate) :
    wholeSynthesis coordinate 0 = 0 := by
  have bounded : |(0 : ℝ)| ≤ Real.log 2 := by
    rw [abs_zero]
    exact Real.log_nonneg (by norm_num)
  rw [wholeSynthesis_eq_projection coordinate 0 bounded, forcingIntegral_zero, map_zero]

theorem boundarySource_zero (coordinate : BurnolCompletedMellinCoordinate) :
    boundarySource coordinate 0 = 0 := by
  simp [boundarySource, wholeSynthesis_zero, pairedMellinTranslationCharacter,
    fullMellinTranslationCharacter, reciprocalMellinTranslationCharacter]

theorem wholeSourceRead_onPa (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (value : BurnolPaAmbientCarrier) (inPa : value ∈ burnolCompactCoPoissonClosedRange) :
    wholeSourceRead coordinate shift value = OriginalRieszFiniteColumns.firstSourceRead coordinate shift value := by
  rw [wholeSourceRead_keeps_defect, sourceFourierDefect_onPa value inPa, inner_zero_right, add_zero]

end
end OriginalRieszFiniteSynthesis
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
