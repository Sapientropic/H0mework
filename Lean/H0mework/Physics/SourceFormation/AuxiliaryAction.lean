import H0mework.Physics.DualVariation.MotherAction
import H0mework.Physics.GaugeAction.P286GaugeYangMillsReadout

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FullAuxiliary

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineBlockwiseConstitutive StageNineFormNativeMotherAction
open StageNineDiracDualFormNativeMotherAction StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeYangMillsReadout EmpiricalReferenceScaleCouplingBoundary

noncomputable section

theorem diracDualMatter_unchanged (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) (auxiliary : FormNativeP286GaugeTwoForm) :
    generatedDiracDualFormNativeMatterDensity source chart point
      (withFormNativeP286GaugeAuxiliary field auxiliary) =
      generatedDiracDualFormNativeMatterDensity source chart point field := rfl

/-- The paid complete gauge polynomial enters the current Dirac-dual epoch;
the original gravity and repaired matter blocks are retained literally. -/
theorem current_auxiliary_quadratic (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings) (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : FormNativeP286GaugeTwoForm) (parameter : ℝ) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point
      (withFormNativeP286GaugeAuxiliary field (field.gaugeAuxiliary + parameter • variation)) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point field +
      parameter * formNativeP286GaugeAuxiliaryFirstVariationDensityAtBoundary boundary field variation +
      parameter ^ 2 * formNativeP286GaugeAuxiliaryQuadraticCoefficientDensityAtBoundary
        boundary field variation := by
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
  rw [generatedFormNativeGaugeDensityAtBoundary_auxiliary_quadratic
    boundary field nondegenerate variation parameter,
    generatedFormNativeGravityBFDensity_withP286Auxiliary,
    generatedFormNativeGravityConstraintDensity_withP286Auxiliary,
    diracDualMatter_unchanged]
  ring

def generatedAuxiliary (source : SmoothUnifiedSource) (field : StageNineContinuumPointField) :
    FormNativeP286GaugeTwoForm :=
  formNativeP286GaugeEliminatedAuxiliaryAtBoundary (sourceGeneratedUnifiedCouplings source)
    field.coframe field.gaugeCurvature

def completedField (source : SmoothUnifiedSource) (field : StageNineContinuumPointField) :
    StageNineContinuumPointField :=
  withFormNativeP286GaugeAuxiliary field (generatedAuxiliary source field)

def auxiliaryResidual (source : SmoothUnifiedSource) (field : StageNineContinuumPointField) :
    FormNativeP286GaugeTwoForm := field.gaugeAuxiliary - generatedAuxiliary source field

theorem generated_auxiliary_solves (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField) (nondegenerate : Matrix.det field.coframe ≠ 0) :
    formNativeP286BlockwiseConstitutive field.coframe
      ((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ)
      ((sourceGeneratedUnifiedCouplings source).weakCouplingSquared : ℝ)
      ((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ)
      (generatedAuxiliary source field) = field.gaugeCurvature :=
  formNativeP286GaugeEliminatedAuxiliaryAtBoundary_solves _ _ nondegenerate _

/-- Complete P286 auxiliary elimination with its signed quadratic remainder.
No chosen center, inverse or field-equation witness is an input. -/
theorem action_decomposition (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point field =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point (completedField source field) -
      (1 / 2 : ℝ) * formNativeP286GaugeWedgeCoefficient (auxiliaryResidual source field)
        (formNativeP286BlockwiseConstitutive field.coframe
          ((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings source).weakCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ)
          (auxiliaryResidual source field)) := by
  have zeroFirst : formNativeP286GaugeAuxiliaryFirstVariationDensityAtBoundary
      (sourceGeneratedUnifiedCouplings source) (completedField source field)
      (auxiliaryResidual source field) = 0 := by
    unfold formNativeP286GaugeAuxiliaryFirstVariationDensityAtBoundary
      formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
    change formNativeP286GaugeWedgeCoefficient (auxiliaryResidual source field)
      (field.gaugeCurvature - formNativeP286BlockwiseConstitutive field.coframe
        ((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings source).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ)
        (generatedAuxiliary source field)) = 0
    rw [generated_auxiliary_solves source field nondegenerate]
    simp
  have restore : withFormNativeP286GaugeAuxiliary (completedField source field)
      ((completedField source field).gaugeAuxiliary + (1 : ℝ) • auxiliaryResidual source field) = field := by
    rw [one_smul]
    change withFormNativeP286GaugeAuxiliary field
      (generatedAuxiliary source field + (field.gaugeAuxiliary - generatedAuxiliary source field)) = field
    rw [← add_sub_assoc, add_sub_cancel_left]
    cases field
    rfl
  have expansion := current_auxiliary_quadratic source (sourceGeneratedUnifiedCouplings source)
    chart point (completedField source field) nondegenerate (auxiliaryResidual source field) 1
  rw [restore, zeroFirst] at expansion
  simpa only [sourceGeneratedDiracDualFormNativeUnifiedLocalDensity,
    formNativeP286GaugeAuxiliaryQuadraticCoefficientDensityAtBoundary,
    completedField, withFormNativeP286GaugeAuxiliary_coframe, one_pow, one_mul,
    mul_zero, add_zero, neg_mul, sub_eq_add_neg] using expansion

/-- Direct consumer on arbitrary complete holonomic fields. The center is
the existing source constitutive writer, with every other field retained. -/
theorem configuration_decomposition (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) (point : BasePoint) :
    let generated := formNativeP286GaugeConstitutiveReadout source configuration
    let residual := configuration.gaugeAuxiliary point - generated.gaugeAuxiliary point
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
      (toContinuumPointField configuration point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
        (toContinuumPointField generated point) -
      (1 / 2 : ℝ) * formNativeP286GaugeWedgeCoefficient residual
        (formNativeP286BlockwiseConstitutive (configuration.coframe point)
          ((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings source).weakCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ) residual) := by
  dsimp only
  rw [toContinuumPointField_formNativeP286GaugeConstitutiveReadout]
  exact action_decomposition source chart point (toContinuumPointField configuration point)
    (nondegenerate point)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FullAuxiliary
