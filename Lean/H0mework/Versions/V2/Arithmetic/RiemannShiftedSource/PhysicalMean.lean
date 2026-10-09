import H0mework.Versions.V2.Arithmetic.RiemannShiftedSource.ActualSampling
import H0mework.Versions.V2.Arithmetic.RiemannUnitRegularity.Mass

/-! The actual dilated W retains its full source-owned mass. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem actual_dilation_integral (value : BurnolL2) (h : ℝ) :
    (∫ x : ℝ, burnolMultiplicativeDilation h value x) =
      (Real.exp (-h / 2) : ℂ) * ∫ x : ℝ, value x := by
  rw [integral_congr_ae (burnolMultiplicativeDilation_coeFn h value)]
  unfold burnolL2RawNormalizedDilation
  rw [integral_const_mul, Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr (Real.exp_pos h)),
    Complex.real_smul, Complex.ofReal_inv, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Real.exp_neg, ← Real.exp_add]
  congr 2
  ring

theorem original_shifted_wave_integrable {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (h : ℝ) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    Integrable (burnolMultiplicativeDilation h W : ℝ → ℂ) := by
  intro one W
  have original : Integrable (W : ℝ → ℂ) :=
    burnolZeroOwnedUnitOnePair_integrable observation nontrivial rightHalf
  have raw := ((integrable_comp_mul_left_iff (W : ℝ → ℂ) (Real.exp_ne_zero h)).mpr
    original).const_mul (Real.exp (h / 2) : ℂ)
  exact raw.congr (burnolMultiplicativeDilation_coeFn h W).symm

theorem original_shifted_wave_integral {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (h : ℝ) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    (∫ x : ℝ, burnolMultiplicativeDilation h W x) =
      (Real.exp (-h / 2) : ℂ) *
        (1 / observation.coordinate - 1 / (1 - observation.coordinate)) := by
  intro one W
  rw [actual_dilation_integral,
    burnolZeroOwnedUnitOnePair_integral observation nontrivial rightHalf]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
