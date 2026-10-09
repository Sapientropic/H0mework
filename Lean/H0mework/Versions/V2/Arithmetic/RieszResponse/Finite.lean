import H0mework.Versions.V2.Arithmetic.RieszResponse.ResponseEquation
import H0mework.Arithmetic.RieszResponse.Integration

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteResponse

open Complex FourierTransform MeasureTheory
open scoped FourierTransform
open OriginalRieszSource
noncomputable section

theorem sourceRead_zero (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    sourceRead coordinate test 0 =
      ((burnolCompletedMellinRieszVector coordinate : BurnolL2) : TemperedDistribution ℝ ℂ) test := by
  rw [sourceRead, original_read, neg_zero, coPoissonSchwartzEnergyTranslation_zero]

theorem original_finite_response (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (endpoint : ℝ) :
    sourceRead coordinate test endpoint =
      Complex.exp (-(star coordinate.value - 1 / 2) * (endpoint : ℂ)) *
        ((burnolCompletedMellinRieszVector coordinate : BurnolL2) : TemperedDistribution ℝ ℂ) test +
      ∫ time : ℝ in (0 : ℝ)..endpoint,
        Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
          (Kernel.A coordinate * Response.Psi (coPoissonSchwartzEnergyTranslation (-time) test) +
            Kernel.beta coordinate * (𝓕 Response.Psi) (coPoissonSchwartzEnergyTranslation (-time) test)) := by
  have generated := _root_.OriginalRieszFiniteResponse.Integration.finite_response
    (sourceRead coordinate test) (forcingRead coordinate test) (star coordinate.value - 1 / 2)
    (source_derivative coordinate test) (forcingRead_continuous coordinate test) endpoint
  rw [sourceRead_zero] at generated
  exact generated

theorem source_term_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (endpoint : ℝ) :
    IntervalIntegrable (fun time : ℝ =>
      Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
        forcingRead coordinate test time) volume 0 endpoint := by
  have kernel : Continuous (fun time : ℝ =>
      Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ)))) :=
    (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)).cexp
  exact (kernel.mul (forcingRead_continuous coordinate test)).intervalIntegrable 0 endpoint

end
end OriginalRieszFiniteResponse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
