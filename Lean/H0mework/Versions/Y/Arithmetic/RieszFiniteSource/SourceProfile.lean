import H0mework.Versions.Y.Arithmetic.RieszFiniteSource.FourierEdge
import H0mework.Versions.Y.Arithmetic.RieszSourceKernel.ResponseProfile

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSource

open Complex FourierTransform MeasureTheory
open scoped FourierTransform Topology
open OriginalRieszSource
noncomputable section

local notation "q" => (1 / 4 : ℝ)

private theorem profile_read (test : SchwartzMap ℝ ℂ) :
    Response.Psi test =
      ((fourierL2 Response.wholeU - Response.wholeV : BurnolL2) :
        TemperedDistribution ℝ ℂ) test - GapEuler.edge q test := by
  rw [Response.Psi, Lp.fourier_toTemperedDistribution_eq]
  change _ = (Lp.toTemperedDistributionCLM ℂ volume 2
    (fourierL2 Response.wholeU - Response.wholeV)) test - _
  simp only [map_sub, sub_apply, Lp.toTemperedDistributionCLM_apply]
  rfl

private theorem fourierProfile_read (test : SchwartzMap ℝ ℂ) :
    (𝓕 Response.Psi) test =
      ((Response.wholeU - fourierL2 Response.wholeV : BurnolL2) :
        TemperedDistribution ℝ ℂ) test - (𝓕 (GapEuler.edge q)) test := by
  rw [Response.Psi_fourier, Lp.fourier_toTemperedDistribution_eq]
  change _ = (Lp.toTemperedDistributionCLM ℂ volume 2
    (Response.wholeU - fourierL2 Response.wholeV)) test - _
  simp only [map_sub, sub_apply, Lp.toTemperedDistributionCLM_apply]
  rfl

theorem profileRead_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    Continuous (fun time : ℝ => Response.Psi
      (coPoissonSchwartzEnergyTranslation (-time) test)) := by
  exact ((nativeRead_continuous (fourierL2 Response.wholeU - Response.wholeV) test).sub
    (edge_read_continuous coordinate test)).congr (fun time => (profile_read _).symm)

theorem fourierProfileRead_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    Continuous (fun time : ℝ => (𝓕 Response.Psi)
      (coPoissonSchwartzEnergyTranslation (-time) test)) := by
  exact ((nativeRead_continuous (Response.wholeU - fourierL2 Response.wholeV) test).sub
    (fourierEdge_read_continuous coordinate test)).congr
      (fun time => (fourierProfile_read _).symm)

theorem profileRead_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (endpoint : ℝ) :
    IntervalIntegrable (fun time : ℝ =>
      Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
        Response.Psi (coPoissonSchwartzEnergyTranslation (-time) test)) volume 0 endpoint := by
  have weight : Continuous (fun time : ℝ =>
      Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ)))) :=
    (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)).cexp
  exact (weight.mul (profileRead_continuous coordinate test)).intervalIntegrable 0 endpoint

theorem fourierProfileRead_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (endpoint : ℝ) :
    IntervalIntegrable (fun time : ℝ =>
      Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
        (𝓕 Response.Psi) (coPoissonSchwartzEnergyTranslation (-time) test)) volume 0 endpoint := by
  have weight : Continuous (fun time : ℝ =>
      Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ)))) :=
    (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)).cexp
  exact (weight.mul (fourierProfileRead_continuous coordinate test)).intervalIntegrable 0 endpoint

/-- Original fixed source columns and the explicit gap/tail primitive generate the full program. -/
def profileIntegral (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) : BurnolL2 :=
  nativeIntegral (star coordinate.value - 1 / 2)
    (fourierL2 Response.wholeU - Response.wholeV) endpoint - edgeIntegral coordinate endpoint

def fourierProfileIntegral (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) : BurnolL2 :=
  nativeIntegral (star coordinate.value - 1 / 2)
    (Response.wholeU - fourierL2 Response.wholeV) endpoint - fourierEdgeIntegral coordinate endpoint

theorem profileIntegral_read (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (endpoint : ℝ) :
    (profileIntegral coordinate endpoint : TemperedDistribution ℝ ℂ) test =
      ∫ time : ℝ in (0 : ℝ)..endpoint,
        Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
          Response.Psi (coPoissonSchwartzEnergyTranslation (-time) test) := by
  have weight : Continuous (fun time : ℝ =>
      Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ)))) :=
    (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)).cexp
  have edgeIntegrable := (weight.mul (edge_read_continuous coordinate test)).intervalIntegrable
    (μ := volume) 0 endpoint
  dsimp only [Pi.mul_def] at edgeIntegrable
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (profileIntegral coordinate endpoint)) test = _
  simp only [profileIntegral, map_sub, sub_apply, Lp.toTemperedDistributionCLM_apply]
  rw [nativeIntegral_read, edgeIntegral_read,
    ← intervalIntegral.integral_sub (nativeWeightedRead_integrable (star coordinate.value - 1 / 2)
      (fourierL2 Response.wholeU - Response.wholeV) endpoint test) edgeIntegrable]
  apply intervalIntegral.integral_congr
  intro time _
  dsimp only
  rw [profile_read]
  ring

theorem fourierProfileIntegral_read (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (endpoint : ℝ) :
    (fourierProfileIntegral coordinate endpoint : TemperedDistribution ℝ ℂ) test =
      ∫ time : ℝ in (0 : ℝ)..endpoint,
        Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
          (𝓕 Response.Psi) (coPoissonSchwartzEnergyTranslation (-time) test) := by
  change (Lp.toTemperedDistributionCLM ℂ volume 2
    (fourierProfileIntegral coordinate endpoint)) test = _
  simp only [fourierProfileIntegral, map_sub, sub_apply, Lp.toTemperedDistributionCLM_apply]
  rw [nativeIntegral_read, fourierEdgeIntegral_read,
    ← intervalIntegral.integral_sub (nativeWeightedRead_integrable _ _ _ _)
      (fourierEdge_read_integrable coordinate test endpoint)]
  apply intervalIntegral.integral_congr
  intro time _
  dsimp only
  rw [fourierProfile_read]
  ring

end
end OriginalRieszFiniteSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
