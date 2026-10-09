import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationPreparedCoupledEuler

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherResidualDirections
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction
open EmpiricalReferenceScaleCouplingBoundary
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeGravityMultiplierAuxiliaryVariation
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeGaugeAuxiliaryVariation StageNineFormNativeGaugeWedge
open StageNineFormNativeMotherAction StageNineTopologicalFourFormPairing
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

private theorem quadratic_direction (constant linear quadratic : ℝ) :
    HasDerivAt (fun r : ℝ => constant+r*linear+r^2*quadratic) linear 0 := by
  convert!
    ((((hasDerivAt_id (x := (0 : ℝ))).mul_const linear).const_add constant).add
      (((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const quadratic)) using 1
  simp

/-- The primitive multiplier direction is differentiated in the repaired whole mother density. -/
theorem motherMultiplier_hasDerivAt (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings) (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) (direction : PhysicalBivector) :
    HasDerivAt (fun r : ℝ => generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
      source boundary chart point
      (withFormNativeGravityMultiplier field (field.gravitySimplicityMultiplier+r • direction)))
      (gravityTopologicalWedgeCoefficient direction (formNativeGravityMultiplierEulerResidual field)) 0 := by
  have formula : (fun r : ℝ => generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
      source boundary chart point
      (withFormNativeGravityMultiplier field (field.gravitySimplicityMultiplier+r • direction))) =
      fun r => generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point field+
        r*formNativeGravityMultiplierFirstVariationDensity field direction := by
    funext r
    exact generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_multiplier_affine
      source boundary chart point field direction r
  rw [formula]
  convert! ((hasDerivAt_id (x := (0 : ℝ))).mul_const
    (formNativeGravityMultiplierFirstVariationDensity field direction)).const_add
      (generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point field) using 1
  simp only [one_mul,formNativeGravityMultiplierFirstVariationDensity]

/-- The BF auxiliary direction returns the original variance-normalized wedge residual. -/
theorem motherGravityAuxiliary_hasDerivAt (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings) (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) (direction : PhysicalBivector) :
    HasDerivAt (fun r : ℝ => generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
      source boundary chart point (withFormNativeGravityAuxiliary field (field.gravityAuxiliary+r • direction)))
      (gravityTopologicalWedgeCoefficient direction (formNativeGravityAuxiliaryEulerResidual field)) 0 := by
  have formula : (fun r : ℝ => generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
      source boundary chart point (withFormNativeGravityAuxiliary field (field.gravityAuxiliary+r • direction))) =
      fun r => generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point field+
        r*formNativeGravityAuxiliaryFirstVariationDensity field direction+
        r^2*formNativeGravityAuxiliaryBFQuadraticCoefficientDensity direction := by
    funext r
    exact generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_auxiliary_quadratic
      source boundary chart point field direction r
  rw [formula]
  simpa only [formNativeGravityAuxiliaryFirstVariationDensity_eq_eulerPairing] using
    quadratic_direction
      (generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point field)
      (formNativeGravityAuxiliaryFirstVariationDensity field direction)
      (formNativeGravityAuxiliaryBFQuadraticCoefficientDensity direction)

private theorem repairedMatter_withGaugeAuxiliary (source : SmoothUnifiedSource)
    (chart : StageNineChart) (point : BasePoint) (field : StageNineContinuumPointField)
    (auxiliary : FormNativeP286GaugeTwoForm) :
    generatedDiracDualFormNativeMatterDensity source chart point
      (withFormNativeP286GaugeAuxiliary field auxiliary) =
      generatedDiracDualFormNativeMatterDensity source chart point field := rfl

private theorem repairedGaugeAuxiliary_quadratic (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings) (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) (nondegenerate : Matrix.det field.coframe ≠ 0)
    (direction : FormNativeP286GaugeTwoForm) (r : ℝ) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point
      (withFormNativeP286GaugeAuxiliary field (field.gaugeAuxiliary+r • direction)) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point field+
        r*formNativeP286GaugeAuxiliaryFirstVariationDensityAtBoundary boundary field direction+
        r^2*formNativeP286GaugeAuxiliaryQuadraticCoefficientDensityAtBoundary boundary field direction := by
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
  rw [generatedFormNativeGaugeDensityAtBoundary_auxiliary_quadratic boundary field nondegenerate direction r]
  simp only [generatedFormNativeGravityBFDensity_withP286Auxiliary,
    generatedFormNativeGravityConstraintDensity_withP286Auxiliary,repairedMatter_withGaugeAuxiliary]
  ring

/-- The actual coframe Hodge produces the full three-block gauge-auxiliary residual. -/
theorem motherGaugeAuxiliary_hasDerivAt (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings) (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) (nondegenerate : Matrix.det field.coframe ≠ 0)
    (direction : FormNativeP286GaugeTwoForm) :
    HasDerivAt (fun r : ℝ => generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
      source boundary chart point (withFormNativeP286GaugeAuxiliary field (field.gaugeAuxiliary+r • direction)))
      (formNativeP286GaugeWedgeCoefficient direction
        (formNativeP286GaugeAuxiliaryEulerResidualAtBoundary boundary field)) 0 := by
  have formula : (fun r : ℝ => generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
      source boundary chart point (withFormNativeP286GaugeAuxiliary field (field.gaugeAuxiliary+r • direction))) =
      fun r => generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point field+
        r*formNativeP286GaugeAuxiliaryFirstVariationDensityAtBoundary boundary field direction+
        r^2*formNativeP286GaugeAuxiliaryQuadraticCoefficientDensityAtBoundary boundary field direction := by
    funext r
    exact repairedGaugeAuxiliary_quadratic source boundary chart point field nondegenerate direction r
  rw [formula]
  exact quadratic_direction
    (generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point field)
    (formNativeP286GaugeAuxiliaryFirstVariationDensityAtBoundary boundary field direction)
    (formNativeP286GaugeAuxiliaryQuadraticCoefficientDensityAtBoundary boundary field direction)

end LowEnergy.SourcePropagationMotherResidualDirections
