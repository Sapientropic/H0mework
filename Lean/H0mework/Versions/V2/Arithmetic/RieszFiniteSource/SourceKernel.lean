import H0mework.Versions.V2.Arithmetic.RieszFiniteSource.SourceProfile
import H0mework.Versions.V2.Arithmetic.RieszResponse.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteSource

open Complex FourierTransform MeasureTheory
open scoped FourierTransform
open OriginalRieszSource
noncomputable section

/-- The actual two source traces weight the independently constructed forcing programs. -/
def forcingIntegral (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) : BurnolL2 :=
  Kernel.A coordinate • profileIntegral coordinate endpoint +
    Kernel.beta coordinate • fourierProfileIntegral coordinate endpoint

theorem forcingIntegral_read (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (endpoint : ℝ) :
    (forcingIntegral coordinate endpoint : TemperedDistribution ℝ ℂ) test =
      ∫ time : ℝ in (0 : ℝ)..endpoint,
        Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
          (Kernel.A coordinate * Response.Psi (coPoissonSchwartzEnergyTranslation (-time) test) +
            Kernel.beta coordinate * (𝓕 Response.Psi)
              (coPoissonSchwartzEnergyTranslation (-time) test)) := by
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (forcingIntegral coordinate endpoint)) test = _
  simp only [forcingIntegral, map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
    Lp.toTemperedDistributionCLM_apply]
  rw [profileIntegral_read, fourierProfileIntegral_read,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add
      ((profileRead_integrable coordinate test endpoint).const_mul (Kernel.A coordinate))
      ((fourierProfileRead_integrable coordinate test endpoint).const_mul (Kernel.beta coordinate))]
  apply intervalIntegral.integral_congr
  intro time _
  dsimp only
  ring

theorem original_material_eq_program (coordinate : BurnolCompletedMellinCoordinate)
    (endpoint : ℝ) :
    OriginalRieszFiniteResponse.sourceMaterial coordinate endpoint = forcingIntegral coordinate endpoint := by
  apply LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  change (OriginalRieszFiniteResponse.sourceMaterial coordinate endpoint : TemperedDistribution ℝ ℂ) test =
    (forcingIntegral coordinate endpoint : TemperedDistribution ℝ ℂ) test
  rw [OriginalRieszFiniteResponse.sourceMaterial_read, forcingIntegral_read]

theorem original_finite_action (coordinate : BurnolCompletedMellinCoordinate)
    (endpoint : ℝ) :
    burnolMultiplicativeDilation endpoint (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      fullMellinTranslationCharacter (star coordinate.value) endpoint •
        (burnolCompletedMellinRieszVector coordinate : BurnolL2) + forcingIntegral coordinate endpoint := by
  have generated := original_material_eq_program coordinate endpoint
  unfold OriginalRieszFiniteResponse.sourceMaterial at generated
  rw [← generated]
  module

end
end OriginalRieszFiniteSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
