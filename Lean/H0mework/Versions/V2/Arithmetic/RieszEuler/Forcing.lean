import H0mework.Versions.V2.Arithmetic.RieszEuler.Even

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.GapEuler

open Complex FourierTransform MeasureTheory
open scoped FourierTransform
noncomputable section

theorem original_fourier_euler (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    let forcing := (fourierL2 (burnolAmbientEvenPart
      (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate)) :
        TemperedDistribution ℝ ℂ)
    euler forcing - (star coordinate.value - 1 / 2) • forcing =
      (star coordinate.value * gapMean radius coordinate) • 𝓕 (edge radius) := by
  dsimp only
  let actual := burnolAmbientEvenPart
    (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate)
  have native : 𝓕 (actual : TemperedDistribution ℝ ℂ) =
      (fourierL2 actual : TemperedDistribution ℝ ℂ) :=
    Lp.fourier_toTemperedDistribution_eq actual
  have generated := congrArg (fourierCLM ℂ (TemperedDistribution ℝ ℂ))
    (even_gapTail_euler radius positive coordinate)
  simp only [map_add, map_smul, fourierCLM_apply] at generated
  change 𝓕 (euler (actual : TemperedDistribution ℝ ℂ)) +
      (star coordinate.value - 1 / 2) • 𝓕 (actual : TemperedDistribution ℝ ℂ) =
      (-star coordinate.value * gapMean radius coordinate) • 𝓕 (edge radius) at generated
  change euler (fourierL2 actual : TemperedDistribution ℝ ℂ) -
    (star coordinate.value - 1 / 2) • (fourierL2 actual : TemperedDistribution ℝ ℂ) = _
  rw [← native, euler_fourier]
  calc
    _ = -(𝓕 (euler (actual : TemperedDistribution ℝ ℂ)) +
      (star coordinate.value - 1 / 2) • 𝓕 (actual : TemperedDistribution ℝ ℂ)) := by module
    _ = _ := by rw [generated]; module

end
end OriginalRieszSource.GapEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
