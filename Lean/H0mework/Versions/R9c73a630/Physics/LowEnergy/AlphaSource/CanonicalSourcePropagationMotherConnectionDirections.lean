import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationMotherResidualPullback
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationMotherAlgebraicDirections

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherResidualDirections
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineCompactSupportIntegrationByParts StageNineResidualLinearPlebanskiTorsionReduction StageNineGravityBianchi
open StageNineTopologicalGravityCurvatureVariancePairing PreparationVacuumMixedFieldReturn
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLorentzConnectionVariation
open StageNineFormNativeLorentzConnectionLocalVariation StageNineLorentzConnectionActionVariation
open StageNineFormNativeP286GaugeConnectionLocalVariation StageNineP286GaugeConnectionActionVariation
open StageNineFormNativeLorentzGeometricFirstVariation StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeLorentzDerivativeIntegrationByParts StageNineFormNativeP286GaugeDerivativeIntegrationByParts
open StageNineFormNativeLorentzGeometricKinematics StageNineFormNativeP286GaugeGeometricKinematics
open StageNineTopologicalLorentzThreeFormDuality StageNineTopologicalP286GaugeThreeFormDuality
open StageNineFormNativeMotherAction StageNineScalarLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracMatterCoordinateCalculus StageNineMatterCovariantDerivativeAffine
open StageNineLorentzConnectionVariation StageNineP286GaugeConnectionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge StageNineTopologicalFourFormPairing
open SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open EmpiricalReferenceScaleCouplingBoundary
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
attribute [local irreducible] nativeConfiguration nativeEuler nativePoint
local instance : Module.Finite ℝ SU7MotherLieAlgebra.P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private theorem quadratic_direction (constant linear quadratic : ℝ) :
    HasDerivAt (fun r : ℝ => constant+r*linear+r^2*quadratic) linear 0 := by
  convert! ((((hasDerivAt_id (x := (0 : ℝ))).mul_const linear).const_add constant).add
    (((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const quadratic)) using 1
  simp

theorem motherLorentz_hasDerivAt (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) (point : BasePoint) :
    HasDerivAt (fun r : ℝ => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
      (toContinuumPointField (varyLorentzConnection configuration variation r) point))
      (holonomicFormNativeLorentzConnectionFirstVariationDensity source chart configuration variation point) 0 := by
  have formula : (fun r : ℝ => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
      (toContinuumPointField (varyLorentzConnection configuration variation r) point)) =
      fun r => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
        (toContinuumPointField configuration point)+
        r*holonomicFormNativeLorentzConnectionFirstVariationDensity source chart configuration variation point+
        r^2*holonomicFormNativeLorentzConnectionSecondVariationDensity configuration variation point := by
    funext r
    exact holonomicDiracDualFormNativeUnifiedLocalDensity_lorentzConnection_quadratic
      source chart configuration smooth variation r point
  rw [formula]
  exact quadratic_direction _ _ _

private theorem repairedP286Kinetic_affine (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) (curvature : P286GaugeTwoForm)
    (scalarDerivative : LorentzianIndex → ScalarCoordinateCarrier)
    (direction : LorentzianIndex → DiracExteriorMatterAction.DiracExteriorMatterCarrier) (r : ℝ) :
    generatedDensitizedContinuumMatterKineticDensity source chart point
      (withP286GaugeConnectionJets field curvature scalarDerivative (field.matterCovariantDerivative+r • direction)) =
      generatedDensitizedContinuumMatterKineticDensity source chart point field+
        r*(generatedVolumeDensity field*matterGaugeConnectionFirstVariationDensity source chart point field direction) := by
  change generatedVolumeDensity field*
      (matterDualFrameRelative source chart point field.conjugateMatter
        (matterCovariantDerivativeVariationVector source chart point field (field.matterCovariantDerivative+r • direction))).re =
      generatedVolumeDensity field*(matterDualFrameRelative source chart point field.conjugateMatter
        (matterCovariantDerivativeVariationVector source chart point field field.matterCovariantDerivative)).re+
      r*(generatedVolumeDensity field*matterGaugeConnectionFirstVariationDensity source chart point field direction)
  rw [matterCovariantDerivativeVariationVector_add,map_add,Complex.add_re]
  have scaled : (matterDualFrameRelative source chart point field.conjugateMatter
      (matterCovariantDerivativeVariationVector source chart point field (r • direction))).re =
      r*matterGaugeConnectionFirstVariationDensity source chart point field direction := by
    have coefficient : matterGaugeConnectionFirstVariationDensity source chart point field direction =
        matterCovariantDerivativeFirstVariationDensity source chart point field direction := rfl
    rw [coefficient,←matterCovariantDerivativeFirstVariationDensity_real_smul]
    rfl
  rw [scaled]
  ring

private theorem repairedP286Matter_quadratic (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) (curvature : P286GaugeTwoForm)
    (scalarDirection : LorentzianIndex → ScalarCoordinateCarrier)
    (matterDirection : LorentzianIndex → DiracExteriorMatterAction.DiracExteriorMatterCarrier) (r : ℝ) :
    generatedDiracDualFormNativeMatterDensity source chart point
      (withP286GaugeConnectionJets field curvature (field.scalarCovariantDerivative+r • scalarDirection)
        (field.matterCovariantDerivative+r • matterDirection)) =
      generatedDiracDualFormNativeMatterDensity source chart point field+
        r*(generatedVolumeDensity field*(scalarGaugeConnectionKineticFirstVariationDensity source chart point field scalarDirection+
          matterGaugeConnectionFirstVariationDensity source chart point field matterDirection))+
        r^2*(generatedVolumeDensity field*scalarGaugeConnectionKineticSecondVariationDensity source chart point field scalarDirection) := by
  have yukawa : generatedDensitizedContinuumDiracDualYukawaDensity source chart point
      (withP286GaugeConnectionJets field curvature (field.scalarCovariantDerivative+r • scalarDirection)
        (field.matterCovariantDerivative+r • matterDirection)) =
      generatedDensitizedContinuumDiracDualYukawaDensity source chart point field := rfl
  unfold generatedDiracDualFormNativeMatterDensity generatedDensitizedContinuumDiracDualMatterDensity
    generatedDensitizedContinuumScalarDensity
  rw [yukawa,generatedScalarKineticDensity_withP286GaugeConnectionJets_quadratic,repairedP286Kinetic_affine]
  simp only [withP286GaugeConnectionJets,generatedVolumeDensity]
  ring

private theorem repairedP286Jets_quadratic (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings) (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) (linearCurvature quadraticCurvature : P286GaugeTwoForm)
    (scalarDirection : LorentzianIndex → ScalarCoordinateCarrier)
    (matterDirection : LorentzianIndex → DiracExteriorMatterAction.DiracExteriorMatterCarrier) (r : ℝ) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point
      (withP286GaugeConnectionJets field (p286CurvatureCoordinate field+r • linearCurvature+r^2 • quadraticCurvature)
        (field.scalarCovariantDerivative+r • scalarDirection) (field.matterCovariantDerivative+r • matterDirection)) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary chart point field+
        r*formNativeP286GaugeConnectionFirstVariationDensity source chart point field linearCurvature scalarDirection matterDirection+
        r^2*formNativeP286GaugeConnectionSecondVariationDensity source chart point field quadraticCurvature scalarDirection := by
  have gravity : generatedFormNativeGravityBFDensity
      (withP286GaugeConnectionJets field (p286CurvatureCoordinate field+r • linearCurvature+r^2 • quadraticCurvature)
        (field.scalarCovariantDerivative+r • scalarDirection) (field.matterCovariantDerivative+r • matterDirection)) =
      generatedFormNativeGravityBFDensity field := rfl
  have constraint : generatedFormNativeGravityConstraintDensity
      (withP286GaugeConnectionJets field (p286CurvatureCoordinate field+r • linearCurvature+r^2 • quadraticCurvature)
        (field.scalarCovariantDerivative+r • scalarDirection) (field.matterCovariantDerivative+r • matterDirection)) =
      generatedFormNativeGravityConstraintDensity field := rfl
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
  rw [gravity,constraint,generatedFormNativeGaugeDensityAtBoundary_connectionJets_quadratic,repairedP286Matter_quadratic]
  unfold formNativeP286GaugeConnectionFirstVariationDensity formNativeP286GaugeConnectionSecondVariationDensity
  ring

private theorem repairedP286_quadratic (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) (r : ℝ) (point : BasePoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
      (toContinuumPointField (varyP286GaugeConnectionCoordinate configuration variation r) point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point (toContinuumPointField configuration point)+
        r*holonomicFormNativeP286GaugeConnectionFirstVariationDensity source chart configuration variation point+
        r^2*holonomicFormNativeP286GaugeConnectionSecondVariationDensity source chart configuration variation point := by
  rw [toContinuumPointField_varyP286GaugeConnectionCoordinate configuration smooth variation r point]
  exact repairedP286Jets_quadratic source (sourceGeneratedUnifiedCouplings source) chart point
    (toContinuumPointField configuration point)
    (p286GaugeConnectionLinearCurvatureVariation configuration variation point)
    (p286GaugeConnectionQuadraticCurvatureVariation variation point)
    (holonomicScalarGaugeConnectionVariation configuration variation point)
    (holonomicMatterGaugeConnectionVariation configuration variation point) r

theorem motherP286_hasDerivAt (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) (point : BasePoint) :
    HasDerivAt (fun r : ℝ => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
      (toContinuumPointField (varyP286GaugeConnectionCoordinate configuration variation r) point))
      (holonomicFormNativeP286GaugeConnectionFirstVariationDensity source chart configuration variation point) 0 := by
  have formula : (fun r : ℝ => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
      (toContinuumPointField (varyP286GaugeConnectionCoordinate configuration variation r) point)) =
      fun r => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point (toContinuumPointField configuration point)+
        r*holonomicFormNativeP286GaugeConnectionFirstVariationDensity source chart configuration variation point+
        r^2*holonomicFormNativeP286GaugeConnectionSecondVariationDensity source chart configuration variation point := by
    funext r
    exact repairedP286_quadratic source chart configuration smooth variation r point
  rw [formula]
  exact quadratic_direction _ _ _

def motherLorentzBoundaryCurrent (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) (mu : Fin 4) (point : BasePoint) : ℝ :=
  gravityExteriorPrincipalContinuousBilinear mu (configuration.gravityAuxiliary point) (variation point)

def motherLorentzBoundaryDivergence (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) (point : BasePoint) : ℝ :=
  ∑ mu : Fin 4,fieldDirectionalDerivative (motherLorentzBoundaryCurrent configuration variation mu) point mu

private theorem lorentzBoundary_generated (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (point : BasePoint) :
    motherLorentzBoundaryDivergence configuration variation point =
      (∑ mu : Fin 4,gravityExteriorPrincipalBilinear mu
        (fieldDirectionalDerivative configuration.gravityAuxiliary point mu) (variation point))+
      gravityTopologicalBFCoefficient (configuration.gravityAuxiliary point)
        (lorentzConnectionExteriorDerivativeVariation variation point) := by
  have product (mu : Fin 4) : fieldDirectionalDerivative (motherLorentzBoundaryCurrent configuration variation mu) point mu =
      gravityExteriorPrincipalBilinear mu (fieldDirectionalDerivative configuration.gravityAuxiliary point mu) (variation point)+
      gravityExteriorPrincipalBilinear mu (configuration.gravityAuxiliary point) (fieldDirectionalDerivative variation point mu) := by
    unfold motherLorentzBoundaryCurrent
    simpa only [gravityExteriorPrincipalContinuousBilinear_apply,
      gravityExteriorPrincipalBilinear_apply] using fieldDirectionalDerivative_continuousBilinear
        (gravityExteriorPrincipalContinuousBilinear mu) configuration.gravityAuxiliary variation
        (holonomicGravityAuxiliary_contDiff configuration smooth) variation.smooth point mu
  unfold motherLorentzBoundaryDivergence
  rw [←loweredLorentzBivectorExteriorDerivative_eq_actual variation point,
    gravityTopologicalBF_loweredExteriorDerivative_eq_principalSum]
  simp only [product,Finset.sum_add_distrib]

theorem motherLorentz_firstDensity_w13_divergence (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) (point : BasePoint) :
    holonomicFormNativeLorentzConnectionFirstVariationDensity source chart configuration variation point =
      lorentzOneFormThreeFormWedgeCoefficient (variation point)
        (holonomicFormNativeLorentzEulerThreeForm source chart configuration point)+
      motherLorentzBoundaryDivergence configuration variation point := by
  have stokes : -(∑ mu : Fin 4,gravityExteriorPrincipalBilinear mu
      (fieldDirectionalDerivative configuration.gravityAuxiliary point mu) (variation point)) =
      lorentzOneFormThreeFormWedgeCoefficient (variation point)
        (holonomicGravityAuxiliaryExteriorDerivative configuration point) := by
    exact gravityExteriorPrincipalSum_eq_w13 _ _
  rw [holonomicFormNativeLorentzConnectionFirstVariationDensity_eq_parts source chart configuration admissible]
  unfold holonomicFormNativeLorentzAlgebraicMatterFirstDensity holonomicFormNativeLorentzEulerThreeForm
  rw [holonomicGravityAuxiliaryExteriorCovariantDerivative_eq_parts]
  simp only [lorentzOneFormThreeFormWedgeCoefficient_add_right]
  rw [←stokes,lorentzBoundary_generated configuration smooth variation point]
  ring

def motherP286BoundaryCurrent (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (mu : Fin 4) (point : BasePoint) : ℝ :=
  p286GaugeExteriorPrincipalContinuousBilinear mu (holonomicP286GaugeAuxiliaryCoordinate configuration point) (variation point)

def motherP286BoundaryDivergence (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint) : ℝ :=
  ∑ mu : Fin 4,fieldDirectionalDerivative (motherP286BoundaryCurrent configuration variation mu) point mu

private theorem p286Boundary_generated (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (point : BasePoint) :
    motherP286BoundaryDivergence configuration variation point =
      (∑ mu : Fin 4,p286GaugeExteriorPrincipalBilinear mu
        (fieldDirectionalDerivative (holonomicP286GaugeAuxiliaryCoordinate configuration) point mu) (variation point))+
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing (holonomicP286GaugeAuxiliaryCoordinate configuration point)
        (p286GaugeConnectionExteriorDerivativeVariation variation point) := by
  have auxiliarySmooth : ContDiff ℝ ∞ (holonomicP286GaugeAuxiliaryCoordinate configuration) := by
    apply contDiff_pi'
    intro pair
    exact smooth.2.2.2.2.2.1 pair
  have product (mu : Fin 4) : fieldDirectionalDerivative (motherP286BoundaryCurrent configuration variation mu) point mu =
      p286GaugeExteriorPrincipalBilinear mu
        (fieldDirectionalDerivative (holonomicP286GaugeAuxiliaryCoordinate configuration) point mu) (variation point)+
      p286GaugeExteriorPrincipalBilinear mu (holonomicP286GaugeAuxiliaryCoordinate configuration point)
        (fieldDirectionalDerivative variation point mu) := by
    unfold motherP286BoundaryCurrent
    simpa only [p286GaugeExteriorPrincipalContinuousBilinear_apply,
      p286GaugeExteriorPrincipalBilinear_apply] using fieldDirectionalDerivative_continuousBilinear
        (p286GaugeExteriorPrincipalContinuousBilinear mu) (holonomicP286GaugeAuxiliaryCoordinate configuration)
        variation auxiliarySmooth variation.smooth point mu
  unfold motherP286BoundaryDivergence
  rw [←p286GaugeOneFormExteriorDerivative_eq_actual variation point,p286TopologicalGaugeBF_exteriorDerivative_eq_principalSum]
  simp only [product,Finset.sum_add_distrib]

theorem motherP286_firstDensity_w13_divergence (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) (point : BasePoint) :
    holonomicFormNativeP286GaugeConnectionFirstVariationDensity source chart configuration variation point =
      p286GaugeOneFormThreeFormWedgeCoefficient (variation point)
        (holonomicFormNativeP286GaugeEulerThreeForm source chart configuration point)+
      motherP286BoundaryDivergence configuration variation point := by
  have stokes : -(∑ mu : Fin 4,p286GaugeExteriorPrincipalBilinear mu
      (fieldDirectionalDerivative (holonomicP286GaugeAuxiliaryCoordinate configuration) point mu) (variation point)) =
      p286GaugeOneFormThreeFormWedgeCoefficient (variation point)
        (holonomicP286GaugeAuxiliaryExteriorDerivative configuration point) := by
    exact p286GaugeExteriorPrincipalSum_eq_w13 _ _
  rw [holonomicFormNativeP286GaugeConnectionFirstVariationDensity_eq_parts]
  unfold holonomicFormNativeP286GaugeAlgebraicChargedFirstDensity holonomicFormNativeP286GaugeEulerThreeForm
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts]
  simp only [p286GaugeOneFormThreeFormWedgeCoefficient_add_right]
  rw [←stokes,p286Boundary_generated configuration smooth variation point]
  ring

/-- The original repaired mother curve reads its generated native Lorentz residual plus actual boundary divergence. -/
theorem nativeMotherLorentz_direction (signal : BasePoint → Field289)
    (smooth : (nativeConfiguration signal).Smooth)
    (admissible : GravityConnectionLorentzAdmissible (nativeConfiguration signal))
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) (point : BasePoint) :
    HasDerivAt (fun r : ℝ => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (varyLorentzConnection (nativeConfiguration signal) variation r) point))
      (lorentzOneFormThreeFormWedgeCoefficient (variation point) (nativeEuler signal point).lorentzConnection+
        motherLorentzBoundaryDivergence (nativeConfiguration signal) variation point) 0 := by
  have generated := motherLorentz_hasDerivAt positiveSmoothUnifiedSource 0 (nativeConfiguration signal) smooth variation point
  rw [motherLorentz_firstDensity_w13_divergence positiveSmoothUnifiedSource 0 (nativeConfiguration signal) smooth admissible] at generated
  simpa only [nativeEuler_original,diracDualFormNativePointwiseJointResidual] using generated

/-- The complete charged three-block curve reads the generated native gauge residual without supplied current data. -/
theorem nativeMotherP286_direction (signal : BasePoint → Field289)
    (smooth : (nativeConfiguration signal).Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) (point : BasePoint) :
    HasDerivAt (fun r : ℝ => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (varyP286GaugeConnectionCoordinate (nativeConfiguration signal) variation r) point))
      (p286GaugeOneFormThreeFormWedgeCoefficient (variation point) (nativeEuler signal point).p286GaugeConnection+
        motherP286BoundaryDivergence (nativeConfiguration signal) variation point) 0 := by
  have generated := motherP286_hasDerivAt positiveSmoothUnifiedSource 0 (nativeConfiguration signal) smooth variation point
  rw [motherP286_firstDensity_w13_divergence positiveSmoothUnifiedSource 0 (nativeConfiguration signal) smooth] at generated
  simpa only [nativeEuler_original,diracDualFormNativePointwiseJointResidual] using generated

end LowEnergy.SourcePropagationMotherResidualDirections
