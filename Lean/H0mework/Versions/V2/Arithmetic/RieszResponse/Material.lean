import H0mework.Versions.V2.Arithmetic.RieszResponse.Finite

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteResponse

open Complex FourierTransform MeasureTheory
open scoped FourierTransform
open OriginalRieszSource
noncomputable section

/-- The original finite action generates its inhomogeneous material in the original L² carrier. -/
def sourceMaterial (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  burnolMultiplicativeDilation shift (burnolCompletedMellinRieszVector coordinate : BurnolL2) -
    fullMellinTranslationCharacter (star coordinate.value) shift •
      (burnolCompletedMellinRieszVector coordinate : BurnolL2)

theorem sourceMaterial_read (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (endpoint : ℝ) :
    (sourceMaterial coordinate endpoint : TemperedDistribution ℝ ℂ) test =
      ∫ time : ℝ in (0 : ℝ)..endpoint,
        Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
          (Kernel.A coordinate * Response.Psi (coPoissonSchwartzEnergyTranslation (-time) test) +
            Kernel.beta coordinate * (𝓕 Response.Psi)
              (coPoissonSchwartzEnergyTranslation (-time) test)) := by
  have character : fullMellinTranslationCharacter (star coordinate.value) endpoint =
      Complex.exp (-(star coordinate.value - 1 / 2) * (endpoint : ℂ)) := by
    unfold fullMellinTranslationCharacter
    congr 1
    ring
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (sourceMaterial coordinate endpoint)) test = _
  rw [sourceMaterial, map_sub, map_smul]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  change sourceRead coordinate test endpoint -
    fullMellinTranslationCharacter (star coordinate.value) endpoint *
      ((burnolCompletedMellinRieszVector coordinate : BurnolL2) : TemperedDistribution ℝ ℂ) test = _
  rw [character, original_finite_response, add_sub_cancel_left]

end
end OriginalRieszFiniteResponse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
