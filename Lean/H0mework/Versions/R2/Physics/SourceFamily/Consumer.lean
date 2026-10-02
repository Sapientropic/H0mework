import H0mework.Versions.R2.Physics.SourceFamily.Field

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineCClassicalWorldAcceptance
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge StageNineFormNativeP286GaugeConstitutiveElimination
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous StageNineBlockwiseConstitutive

noncomputable section

private theorem uniform_constitutive (coframe : LorentzianCoframe) (coefficient : ℝ)
    (auxiliary : FormNativeP286GaugeTwoForm) :
    formNativeP286BlockwiseConstitutive coframe coefficient coefficient coefficient auxiliary =
      coefficient • formNativeP286LiftedCoframeHodge coframe auxiliary := by
  rw [formNativeP286BlockwiseConstitutive_eq_blockScale_hodge]
  rfl

/-- The changed source coupling enters the actual full constitutive action.
Reading the generated field with the original coupling exposes the exact
signed difference, without changing its coframe, curvature or auxiliary. -/
theorem original_coupling_residual (step : ℕ) (point : BasePoint) :
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary (sourceGeneratedUnifiedCouplings Runtime.source)
      (toContinuumPointField (fieldAt step) point) =
      (-(step : ℝ) / 2) • holonomicGaugeCurvature (fieldAt step) point := by
  have equation := field_auxiliary_equation step point
  unfold FormNativeP286GaugeAuxiliaryEquationAtBoundary at equation
  rw [(source_couplings step).1, (source_couplings step).2.1,
    (source_couplings step).2.2, uniform_constitutive] at equation
  have unit : (step + 2 : ℝ) * coupling step = 1 := by
    rw [coupling_value]
    field_simp
  have unscaled := congrArg (fun value => (step + 2 : ℝ) • value) equation
  rw [smul_smul, unit, one_smul] at unscaled
  change (step + 2 : ℝ) • holonomicGaugeCurvature (fieldAt step) point =
    formNativeP286LiftedCoframeHodge ((fieldAt step).coframe point)
      ((fieldAt step).gaugeAuxiliary point) at unscaled
  unfold formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
  change holonomicGaugeCurvature (fieldAt step) point -
    formNativeP286BlockwiseConstitutive ((fieldAt step).coframe point)
      sourceCoupling sourceCoupling sourceCoupling ((fieldAt step).gaugeAuxiliary point) = _
  rw [uniform_constitutive, ← unscaled, sourceCoupling_eq, smul_smul]
  conv_lhs => lhs; rw [← one_smul ℝ (holonomicGaugeCurvature (fieldAt step) point)]
  exact (sub_smul (1 : ℝ) ((1 / 2 : ℝ) * (step + 2))
    (holonomicGaugeCurvature (fieldAt step) point)).symm.trans
      (congrArg (fun coefficient : ℝ => coefficient • holonomicGaugeCurvature (fieldAt step) point)
        (by ring))

theorem field_curvature_nonzero (step : ℕ) (point : BasePoint) :
    holonomicGaugeCurvature (fieldAt step) point ≠ 0 := by
  rw [field_curvature, ← actual_gaugeCurvature point]
  exact actual_gaugeCurvature_nonzero point

theorem successor_original_residual_nonzero (step : ℕ) (point : BasePoint) :
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary (sourceGeneratedUnifiedCouplings Runtime.source)
      (toContinuumPointField (fieldAt (step + 1)) point) ≠ 0 := by
  rw [original_coupling_residual]
  exact smul_ne_zero (div_ne_zero (neg_ne_zero.mpr (by positivity)) (by norm_num))
    (field_curvature_nonzero (step + 1) point)

theorem field_zero_accepted : ClassicalWorldAcceptance Runtime.source (fieldAt 0) := by
  rw [field_zero, Runtime.configuration_eq, Runtime.source_eq]
  exact actual_classicalWorldAcceptance

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily
