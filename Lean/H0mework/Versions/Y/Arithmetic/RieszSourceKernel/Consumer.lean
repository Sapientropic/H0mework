import H0mework.Versions.Y.Arithmetic.RieszSourceKernel.Generated
import H0mework.Versions.Y.Arithmetic.RieszSourceKernel.Controls
import H0mework.Versions.Y.Arithmetic.RieszEuler.Weak
import H0mework.Versions.Y.Arithmetic.RiemannDivision.AnalyticComplementExactOrderPhysicalRead
import H0mework.Versions.Y.Arithmetic.RiemannSpectral.PaDiagonalBoundary

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Kernel

open Complex FourierTransform MeasureTheory
open scoped FourierTransform
noncomputable section

theorem original_dilation_response (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun h : ℝ =>
      (burnolMultiplicativeDilation h (burnolCompletedMellinRieszVector coordinate : BurnolL2) :
        TemperedDistribution ℝ ℂ) test)
      (A coordinate * Response.Psi test + beta coordinate * (𝓕 Response.Psi) test -
        (star coordinate.value - 1 / 2) *
          ((burnolCompletedMellinRieszVector coordinate : BurnolL2) : TemperedDistribution ℝ ℂ) test) 0 := by
  have source := congrArg (fun value : TemperedDistribution ℝ ℂ => value test)
    (original_kernel_euler coordinate)
  simp only [add_apply, smul_apply, smul_eq_mul] at source
  have derivative := Dilation.original_weak_at_zero
    (burnolCompletedMellinRieszVector coordinate : BurnolL2) test
  exact derivative.congr_deriv (eq_sub_of_add_eq source)

theorem zero_owned_response {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    burnolZeroPaRieszState coordinate observation.mathlibZero ≠ 0 ∧
      type_of% (position_jump coordinate) ∧ type_of% (fourier_jump coordinate) ∧
      type_of% edge_mass_zero ∧ type_of% edge_quadratic_read ∧ type_of% edge_nonzero ∧
      (∀ test : SchwartzMap ℝ ℂ,
        HasDerivAt (fun h : ℝ =>
          (burnolMultiplicativeDilation h
            (burnolZeroPaRieszState coordinate observation.mathlibZero : BurnolL2) :
              TemperedDistribution ℝ ℂ) test)
          (A coordinate * Response.Psi test + beta coordinate * (𝓕 Response.Psi) test -
            (star coordinate.value - 1 / 2) *
              ((burnolZeroPaRieszState coordinate observation.mathlibZero : BurnolL2) :
                TemperedDistribution ℝ ℂ) test) 0) := by
  dsimp only
  refine ⟨?_, position_jump _, fourier_jump _, edge_mass_zero, edge_quadratic_read, edge_nonzero, ?_⟩
  · apply (burnolZeroPaRieszState_ne_zero_iff_evaluator_ne_zero
      (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) observation.mathlibZero).2
    exact burnolAnalyticComplementCompletedMellinEvaluator_ne_zero_generated observation nontrivial rightHalf
  · intro test
    exact original_dilation_response
      (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) test

end
end OriginalRieszSource.Kernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
