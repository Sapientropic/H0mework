import H0mework.Arithmetic.MellinProjection.CompletedEvaluator
import H0mework.Versions.Y.Arithmetic.BurnolPhysical.L2DirectDilation
import H0mework.Versions.Y.Arithmetic.RiemannResolvent.QuarterFeatureCompletionRightResolvent

/-! # Burnol--de Branges direct division operator -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set Filter FourierTransform
open SourceGeneratedComplexFeaturePerfectification
open scoped ENNReal InnerProductSpace

noncomputable section

/-- The right-half completed-Mellin coordinate `rho = 2z`. -/
def burnolDivisionCoordinate (z : ℂ)
    (rightQuarter : 1 / 4 < z.re) (belowHalf : z.re < 1 / 2) :
    BurnolCompletedMellinCoordinate where
  value := 2 * z
  rightHalf := by
    simp only [mul_re]
    norm_num
    linarith
  belowOne := by
    simp only [mul_re]
    norm_num
    linarith

@[simp] theorem burnolDivisionCoordinate_half
    (z : ℂ) (rightQuarter : 1 / 4 < z.re) (belowHalf : z.re < 1 / 2) :
    (burnolDivisionCoordinate z rightQuarter belowHalf).value / 2 = z := by
  change (2 * z) / 2 = z
  ring

def burnolDirectRightResolventIntegrand
    (z : ℂ) (value : BurnolL2) (h : ℝ) : BurnolL2 :=
  positiveMellinQuarterRightResolventWeight z h •
    burnolMultiplicativeDilation (-h / 2) value

/-- The direct Burnol-coordinate right resolvent. -/
def burnolDirectRightResolvent (z : ℂ) (value : BurnolL2) : BurnolL2 :=
  -∫ h : ℝ in Ioi (0 : ℝ),
    burnolDirectRightResolventIntegrand z value h

/-- On the actual feature-completion range the direct Burnol integrand is
Bochner integrable, with no extra regularity premise. -/
theorem burnolDirectRightResolventIntegrand_integrableOn_feature
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : HilbertAmbient (quarterMellinL2Feature z)) :
    IntegrableOn
      (burnolDirectRightResolventIntegrand z
        (quarterMellinFeatureCompletionEvenAdditive z value))
      (Ioi (0 : ℝ)) := by
  have sourceIntegrable :=
    quarterFeatureCompletionRightResolventIntegrand_integrableOn
      z rightQuarter value
  have mappedIntegrable :=
    (quarterMellinFeatureCompletionEvenAdditive z).integrableOn_comp
      sourceIntegrable
  apply mappedIntegrable.congr
  filter_upwards with h
  change quarterMellinFeatureCompletionEvenAdditive z
      (quarterFeatureCompletionRightResolventIntegrand z value h) =
    burnolDirectRightResolventIntegrand z
      (quarterMellinFeatureCompletionEvenAdditive z value) h
  unfold burnolDirectRightResolventIntegrand
    quarterFeatureCompletionRightResolventIntegrand
  rw [map_smul, quarterMellinFeatureCompletionEvenAdditive_translation]

/-- Completion resolvent equals the direct Burnol-coordinate integral. -/
theorem quarterMellinFeatureCompletionEvenAdditive_rightResolvent_eq_direct
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : HilbertAmbient (quarterMellinL2Feature z)) :
    quarterMellinFeatureCompletionEvenAdditive z
        (quarterFeatureCompletionRightResolvent z value) =
      burnolDirectRightResolvent z
        (quarterMellinFeatureCompletionEvenAdditive z value) := by
  have integrable :=
    quarterFeatureCompletionRightResolventIntegrand_integrableOn
      z rightQuarter value
  unfold quarterFeatureCompletionRightResolvent burnolDirectRightResolvent
  rw [map_neg, ← (quarterMellinFeatureCompletionEvenAdditive z
    ).integral_comp_comm integrable]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h _
  unfold quarterFeatureCompletionRightResolventIntegrand
    burnolDirectRightResolventIntegrand
  change quarterMellinFeatureCompletionEvenAdditive z
      (positiveMellinQuarterRightResolventWeight z h •
        quarterFeatureCompletionTranslation z h value) = _
  rw [map_smul, quarterMellinFeatureCompletionEvenAdditive_translation]

theorem integral_mem_closedSubmodule
    (carrier : ClosedSubmodule ℂ BurnolL2)
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (integrand : α → BurnolL2) (integrable : Integrable integrand μ)
    (membership : ∀ᵐ x ∂μ, integrand x ∈ carrier) :
    (∫ x, integrand x ∂μ) ∈ carrier := by
  apply carrier.toSubmodule.starProjection_eq_self_iff.mp
  rw [← carrier.toSubmodule.starProjection.integral_comp_comm integrable]
  apply integral_congr_ae
  filter_upwards [membership] with x hx
  exact carrier.toSubmodule.starProjection_eq_self_iff.mpr hx

theorem burnolMultiplicativeDilation_mem_locallyConstantFace_of_nonpositive
    (radius : ℝ) (_positive : 0 < radius)
    (h : ℝ) (nonpositive : h ≤ 0) (value : BurnolL2)
    (membership : value ∈ locallyConstantFace radius) :
    burnolMultiplicativeDilation h value ∈ locallyConstantFace radius := by
  rw [mem_locallyConstantFace_iff_exists] at membership ⊢
  obtain ⟨coefficient, coefficientRead⟩ := membership
  refine ⟨(Real.exp (h / 2) : ℂ) * coefficient, ?_⟩
  apply Lp.ext
  have scaleLeOne : Real.exp h ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr nonpositive
  have scaleQmp : Measure.QuasiMeasurePreserving
      (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  have sourceRestricted :
      value =ᵐ[volume.restrict (symmetricInterval radius)]
        fun _ : ℝ => coefficient := by
    have restrictionCoe := LpToLpRestrictCLM_coeFn ℂ
      (symmetricInterval radius) value
    have constantRead := intervalConstant_coeFn radius
    have smulRead := Lp.coeFn_smul coefficient (intervalConstant radius)
    filter_upwards [restrictionCoe, constantRead, smulRead]
      with x target constant smul
    calc
      value x = restrictToInterval radius value x := target.symm
      _ = (coefficient • intervalConstant radius) x := by rw [coefficientRead]
      _ = coefficient * intervalConstant radius x := smul
      _ = coefficient := by rw [constant, mul_one]
  have sourceGlobal : ∀ᵐ x ∂volume,
      x ∈ symmetricInterval radius → value x = coefficient :=
    (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp
      sourceRestricted
  have sourceScaled : ∀ᵐ x ∂volume,
      Real.exp h * x ∈ symmetricInterval radius →
        value (Real.exp h * x) = coefficient := by
    filter_upwards [scaleQmp.ae sourceGlobal] with x hx
    exact hx
  filter_upwards [
    Lp.coeFn_smul ((Real.exp (h / 2) : ℂ) * coefficient)
      (intervalConstant radius),
    intervalConstant_coeFn radius,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius)
      (burnolMultiplicativeDilation h value),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn h value),
    ae_restrict_of_ae sourceScaled,
    ae_restrict_mem (measurableSet_symmetricInterval radius)]
      with x targetSmul constant targetRestriction dilationRead sourceRead inside
  have scaledInside : Real.exp h * x ∈ symmetricInterval radius := by
    simp only [symmetricInterval, mem_Icc] at inside ⊢
    constructor
    · nlinarith [Real.exp_pos h]
    · nlinarith [Real.exp_pos h]
  calc
    (((Real.exp (h / 2) : ℂ) * coefficient) • intervalConstant radius :
        Lp ℂ 2 (volume.restrict (symmetricInterval radius))) x =
        ((Real.exp (h / 2) : ℂ) * coefficient) *
          intervalConstant radius x := targetSmul
    _ = (Real.exp (h / 2) : ℂ) * coefficient := by rw [constant, mul_one]
    _ = (Real.exp (h / 2) : ℂ) * value (Real.exp h * x) := by
      rw [sourceRead scaledInside]
    _ = burnolL2RawNormalizedDilation h value x := rfl
    _ = burnolMultiplicativeDilation h value x := dilationRead.symm
    _ = restrictToInterval radius
        (burnolMultiplicativeDilation h value) x := targetRestriction.symm

theorem reflectL2_burnolMultiplicativeDilation
    (h : ℝ) (value : BurnolL2) :
    reflectL2 (burnolMultiplicativeDilation h value) =
      burnolMultiplicativeDilation h (reflectL2 value) := by
  rw [← fourierL2_fourierL2,
    fourierL2_burnolMultiplicativeDilation,
    fourierL2_burnolMultiplicativeDilation,
    fourierL2_fourierL2]
  rw [neg_neg]

theorem burnolMultiplicativeDilation_mem_evenL2ClosedFace
    (h : ℝ) (value : BurnolL2)
    (membership : value ∈ evenL2ClosedFace) :
    burnolMultiplicativeDilation h value ∈ evenL2ClosedFace := by
  rw [mem_evenL2ClosedFace_iff] at membership ⊢
  rw [reflectL2_burnolMultiplicativeDilation, membership]

theorem burnolDirectRightResolvent_position_even_of_integrable
    (radius : ℝ) (positive : 0 < radius) (z : ℂ)
    (value : EvenBurnolPhysicalCarrier radius)
    (integrable : IntegrableOn
      (burnolDirectRightResolventIntegrand z (value : BurnolL2))
      (Ioi (0 : ℝ))) :
    burnolDirectRightResolvent z (value : BurnolL2) ∈
        locallyConstantFace radius ∧
      burnolDirectRightResolvent z (value : BurnolL2) ∈
        evenL2ClosedFace := by
  have positionIntegrand : ∀ᵐ h ∂volume.restrict (Ioi (0 : ℝ)),
      burnolDirectRightResolventIntegrand z (value : BurnolL2) h ∈
        locallyConstantFace radius := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h positiveH
    unfold burnolDirectRightResolventIntegrand
    apply (locallyConstantFace radius).smul_mem
    apply burnolMultiplicativeDilation_mem_locallyConstantFace_of_nonpositive
      radius positive
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr positiveH.le)
        (by norm_num)
    · exact value.property.1.1
  have evenIntegrand : ∀ᵐ h ∂volume.restrict (Ioi (0 : ℝ)),
      burnolDirectRightResolventIntegrand z (value : BurnolL2) h ∈
        evenL2ClosedFace := by
    filter_upwards with h
    unfold burnolDirectRightResolventIntegrand
    apply evenL2ClosedFace.toSubmodule.smul_mem
    exact burnolMultiplicativeDilation_mem_evenL2ClosedFace
      (-h / 2) (value : BurnolL2) value.property.2
  have positionIntegral := integral_mem_closedSubmodule
    { toSubmodule := locallyConstantFace radius
      isClosed' := locallyConstantFace_isClosed radius }
    (volume.restrict (Ioi (0 : ℝ)))
    (burnolDirectRightResolventIntegrand z (value : BurnolL2))
    integrable positionIntegrand
  have evenIntegral := integral_mem_closedSubmodule evenL2ClosedFace
    (volume.restrict (Ioi (0 : ℝ)))
    (burnolDirectRightResolventIntegrand z (value : BurnolL2))
    integrable evenIntegrand
  exact ⟨(locallyConstantFace radius).neg_mem positionIntegral,
    evenL2ClosedFace.toSubmodule.neg_mem evenIntegral⟩

theorem fourierL2_burnolDirectRightResolvent
    (z : ℂ) (value : BurnolL2)
    (integrable : IntegrableOn
      (burnolDirectRightResolventIntegrand z value) (Ioi (0 : ℝ))) :
    fourierL2 (burnolDirectRightResolvent z value) =
      -∫ h : ℝ in Ioi (0 : ℝ),
        positiveMellinQuarterRightResolventWeight z h •
          burnolMultiplicativeDilation (h / 2) (fourierL2 value) := by
  let read : BurnolL2 →L[ℂ] BurnolL2 :=
    fourierL2.toLinearIsometry.toContinuousLinearMap
  unfold burnolDirectRightResolvent
  change read (-∫ h : ℝ in Ioi (0 : ℝ),
    burnolDirectRightResolventIntegrand z value h) = _
  rw [map_neg, ← read.integral_comp_comm integrable]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h _
  unfold burnolDirectRightResolventIntegrand
  change fourierL2
      (positiveMellinQuarterRightResolventWeight z h •
        burnolMultiplicativeDilation (-h / 2) value) = _
  rw [map_smul, fourierL2_burnolMultiplicativeDilation]
  have parameter : -(-h / 2) = h / 2 := by ring
  rw [parameter]

theorem burnolFourierExpandingOrbit_integrableOn_of_direct
    (z : ℂ) (value : BurnolL2)
    (integrable : IntegrableOn
      (burnolDirectRightResolventIntegrand z value) (Ioi (0 : ℝ))) :
    IntegrableOn (fun h : ℝ =>
      positiveMellinQuarterRightResolventWeight z h •
        burnolMultiplicativeDilation (h / 2) (fourierL2 value))
      (Ioi (0 : ℝ)) := by
  let read : BurnolL2 →L[ℂ] BurnolL2 :=
    fourierL2.toLinearIsometry.toContinuousLinearMap
  have mapped := read.integrableOn_comp integrable
  apply mapped.congr
  filter_upwards with h
  change fourierL2 (burnolDirectRightResolventIntegrand z value h) = _
  unfold burnolDirectRightResolventIntegrand
  rw [map_smul, fourierL2_burnolMultiplicativeDilation]
  have parameter : -(-h / 2) = h / 2 := by ring
  rw [parameter]

theorem burnolDirectRightResolventIntegrand_integrableOn_of_fourierExpanding
    (z : ℂ) (value : BurnolL2)
    (integrable : IntegrableOn (fun h : ℝ =>
      positiveMellinQuarterRightResolventWeight z h •
        burnolMultiplicativeDilation (h / 2) (fourierL2 value))
      (Ioi (0 : ℝ))) :
    IntegrableOn (burnolDirectRightResolventIntegrand z value)
      (Ioi (0 : ℝ)) := by
  let read : BurnolL2 →L[ℂ] BurnolL2 :=
    fourierL2.symm.toLinearIsometry.toContinuousLinearMap
  have mapped := read.integrableOn_comp integrable
  apply mapped.congr
  filter_upwards with h
  change fourierL2.symm
      (positiveMellinQuarterRightResolventWeight z h •
        burnolMultiplicativeDilation (h / 2) (fourierL2 value)) =
    burnolDirectRightResolventIntegrand z value h
  apply fourierL2.injective
  rw [fourierL2.apply_symm_apply]
  unfold burnolDirectRightResolventIntegrand
  rw [map_smul, fourierL2_burnolMultiplicativeDilation]
  have parameter : -(-h / 2) = h / 2 := by ring
  rw [parameter]

/-- The actual feature-completion source generates the expanding Fourier
orbit's Bochner integrability; callers supply no regularity certificate. -/
theorem fourierExpandingOrbit_integrableOn_of_featureCompletion
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : HilbertAmbient (quarterMellinL2Feature z)) :
    IntegrableOn (fun h : ℝ =>
      positiveMellinQuarterRightResolventWeight z h •
        burnolMultiplicativeDilation (h / 2)
          (fourierL2
            (quarterMellinFeatureCompletionEvenAdditive z value)))
      (Ioi (0 : ℝ)) := by
  apply burnolFourierExpandingOrbit_integrableOn_of_direct
  exact burnolDirectRightResolventIntegrand_integrableOn_feature
    z rightQuarter value

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
