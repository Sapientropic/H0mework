import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Core
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! The original Bochner resolvent generates its whole L² representative. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem indicator_inner_one (s : Set ℝ) (measurable : MeasurableSet s)
    (finite : volume s < ⊤) (raw : ℝ → ℂ) :
    (fun x => inner ℂ (indicatorConstLp 2 measurable finite.ne (1 : ℂ) x) (raw x)) =ᵐ[volume]
      s.indicator raw := by
  filter_upwards [@indicatorConstLp_coeFn ℝ ℂ _ 2 volume _ s measurable finite.ne (1 : ℂ)]
    with x read
  by_cases inside : x ∈ s
  · simp only [read, Set.indicator_of_mem inside, RCLike.inner_apply, map_one, mul_one]
  · simp only [read, Set.indicator_of_notMem inside, inner_zero_left]

/-- Actual L² Bochner integration generates its raw representative from the existing pairing. -/
theorem source_l2_bochner_coeFn (μ : Measure ℝ) [SFinite μ]
    (family : ℝ → BurnolL2) (integrable : Integrable family μ) (raw : ℝ × ℝ → ℂ)
    (measurable : Measurable raw)
    (reads : ∀ᵐ h ∂μ, (family h : ℝ → ℂ) =ᵐ[volume] fun x => raw (h, x)) :
    ((∫ h, family h ∂μ : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ h, raw (h, x) ∂μ := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs finite
    exact (integrable_indicator_iff hs).mp
      ((L2.integrable_inner (𝕜 := ℂ) (indicatorConstLp 2 hs finite.ne (1 : ℂ))
        (∫ h, family h ∂μ)).congr (indicator_inner_one s hs finite _))
  · intro s hs finite
    have native := burnolL2Bochner_pairing_raw μ family integrable raw measurable reads
      (indicatorConstLp 2 hs finite.ne (1 : ℂ))
    exact (integrable_indicator_iff hs).mp
      (native.1.congr (indicator_inner_one s hs finite _))
  · intro s hs finite
    have native := (burnolL2Bochner_pairing_raw μ family integrable raw measurable reads
      (indicatorConstLp 2 hs finite.ne (1 : ℂ))).2
    rw [L2.inner_def, integral_congr_ae (indicator_inner_one s hs finite _),
      integral_congr_ae (indicator_inner_one s hs finite _), integral_indicator hs,
      integral_indicator hs] at native
    exact native

theorem sourceVolterraResolvent_coeFn (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) :
    (sourceVolterraResolvent coordinate value : ℝ → ℂ) =ᵐ[volume]
      burnolFourierRightDivisionRaw (coordinate.value / 2) value := by
  let z := coordinate.value / 2
  let family : ℝ → BurnolL2 := fun h => positiveMellinQuarterRightResolventWeight z h •
    burnolMultiplicativeDilation (h / 2) value
  let raw : ℝ × ℝ → ℂ := fun point =>
    Complex.exp (((1 / 2 : ℂ) - z) * (point.1 : ℂ)) *
      value (Real.exp (point.1 / 2) * point.2)
  have rightQuarter : 1 / 4 < z.re := by
    dsimp only [z]
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  have integrable : IntegrableOn family (Ioi 0) := by
    have native := burnolDirectRightResolventIntegrand_integrableOn z rightQuarter
      (burnolTateReciprocalL2 value)
    apply (burnolTateReciprocalL2.integrable_comp native).congr
    filter_upwards with h
    unfold burnolDirectRightResolventIntegrand
    rw [map_smul]
    have action := burnolTateReciprocalL2_dilation_inverse (h / 2) (burnolTateReciprocalL2 value)
    rw [burnolTateReciprocalL2_involutive] at action
    simpa only [neg_div, family] using congrArg
      (fun current : BurnolL2 => positiveMellinQuarterRightResolventWeight z h • current) action.symm
  have measured : Measurable raw := by
    unfold raw
    exact (by fun_prop : Measurable (fun point : ℝ × ℝ =>
      Complex.exp (((1 / 2 : ℂ) - z) * (point.1 : ℂ)))).mul
        ((Lp.stronglyMeasurable value).measurable.comp (by fun_prop))
  have reads : ∀ᵐ h ∂volume.restrict (Ioi 0), (family h : ℝ → ℂ) =ᵐ[volume]
      fun x => raw (h, x) := by
    filter_upwards with h
    filter_upwards [Lp.coeFn_smul (positiveMellinQuarterRightResolventWeight z h)
      (burnolMultiplicativeDilation (h / 2) value),
      burnolMultiplicativeDilation_coeFn (h / 2) value] with x scaleRead dilationRead
    change (positiveMellinQuarterRightResolventWeight z h •
      burnolMultiplicativeDilation (h / 2) value : BurnolL2) x = _
    rw [scaleRead, Pi.smul_apply, smul_eq_mul, dilationRead,
      burnolFourierRightDivision_integrand_eq]
  have actual : sourceVolterraResolvent coordinate value =
      -(∫ h in Ioi 0, family h) := by
    change burnolTateReciprocalL2 (burnolDirectRightResolvent z
      (burnolTateReciprocalL2 value)) = _
    rw [burnolTateReciprocalL2_directRightResolvent z rightQuarter,
      burnolTateReciprocalL2_involutive]
  rw [actual]
  filter_upwards [Lp.coeFn_neg (∫ h in Ioi 0, family h),
    source_l2_bochner_coeFn (volume.restrict (Ioi 0)) family integrable raw measured reads]
      with x negRead rawRead
  rw [negRead, Pi.neg_apply, rawRead]
  rfl


end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
