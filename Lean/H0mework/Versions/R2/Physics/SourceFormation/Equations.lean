import H0mework.Versions.R2.Physics.SourceFormation.Matter
import H0mework.Versions.R2.Physics.SourceFormation.Scalar

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeCoframeLocalVariation StageNineCoframeVariation
open StageNineP286GaugeConnectionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionActionVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricKinematics StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineMatterCovariantDerivativeAffine StageNineMatterVariation
open StageNineDiracDualYukawaLocalSpinDensity StageNineDiracKineticLocalSpinDensity
open StageNineFormNativeMotherAction StageNineBlockwiseConstitutive
open StageNineScalarLocalSpinDensity StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _

theorem conjugate_euler_zero (source : SmoothUnifiedSource) (point : BasePoint)
    (variation : MatterCoordinateCarrier) :
    diracDualConjugateMatterDirectionalCoefficient source (formedField source) variation point = 0 := by
  unfold diracDualConjugateMatterDirectionalCoefficient generatedContinuumDiracDualMatterVector
  rw [Scalar.yukawa_vector_zero, add_zero, Matter.kinetic_eq,
    SourceFamily.Dirac.kinetic_zero]
  simp

theorem charged_coefficient_eq (source : SmoothUnifiedSource) (point : BasePoint)
    (variation : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient source 0 point
      (toContinuumPointField (formedField source) point) variation =
      formNativeChargedGaugeFirstCoefficient (SourceFamily.sourceAt (index source)) 0 point
        (toContinuumPointField (SourceFamily.fieldAt (index source)) point) variation := by
  unfold formNativeChargedGaugeFirstCoefficient
  rw [Scalar.scalar_gauge_coefficient_zero, SourceFamily.Gauge.scalar_gauge_coefficient_zero]
  unfold generatedVolumeDensity matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum pointwiseMatterP286GaugeConnectionVariation
  simp only [matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart,
    toContinuumPointField, coframe_eq, matter_eq, dual_eq]

theorem charged_three_form_eq (source : SmoothUnifiedSource) (point : BasePoint) :
    formNativeChargedGaugeThreeForm source 0 point
      (toContinuumPointField (formedField source) point) =
      formNativeChargedGaugeThreeForm (SourceFamily.sourceAt (index source)) 0 point
        (toContinuumPointField (SourceFamily.fieldAt (index source)) point) := by
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro variation
  exact charged_coefficient_eq source point variation

theorem gauge_exterior_eq (source : SmoothUnifiedSource) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative (formedField source) point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative (SourceFamily.fieldAt (index source)) point := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [gauge_connection_eq, gauge_auxiliary_eq]

theorem gauge_euler_zero (source : SmoothUnifiedSource) (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source (formedField source) point).p286GaugeConnection = 0 := by
  change holonomicFormNativeP286GaugeEulerThreeForm source 0 (formedField source) point = 0
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [gauge_exterior_eq, charged_three_form_eq]
  exact SourceFamily.Gauge.gauge_euler_zero (index source) point

theorem gravity_curvature_eq (source : SmoothUnifiedSource) (point : BasePoint) :
    holonomicGravityCurvature (formedField source) point =
      holonomicGravityCurvature (SourceFamily.fieldAt (index source)) point := by
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [gravity_connection_eq]

theorem gauge_curvature_eq (source : SmoothUnifiedSource) (point : BasePoint) :
    holonomicGaugeCurvature (formedField source) point =
      holonomicGaugeCurvature (SourceFamily.fieldAt (index source)) point := by
  unfold holonomicGaugeCurvature p286ConnectionDerivative
  rw [gauge_connection_eq]

private theorem reference_scalar_zero (source : SmoothUnifiedSource) (point : BasePoint)
    (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumScalarDensity (SourceFamily.sourceAt (index source)) 0 point
      (withCoframe (toContinuumPointField (SourceFamily.fieldAt (index source)) point) candidate) = 0 := by
  simpa only [field_family] using
    Scalar.frozen_scalar_density_zero (SourceFamily.sourceAt (index source)) point candidate

private theorem reference_yukawa_zero (source : SmoothUnifiedSource) (point : BasePoint)
    (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumDiracDualYukawaDensity (SourceFamily.sourceAt (index source)) 0 point
      (withCoframe (toContinuumPointField (SourceFamily.fieldAt (index source)) point) candidate) = 0 := by
  simpa only [field_family] using
    Scalar.frozen_yukawa_density_zero (SourceFamily.sourceAt (index source)) point candidate

theorem coframe_density_eq (source : SmoothUnifiedSource) (point : BasePoint) :
    diracDualFormNativeCoframeLocalDensity source point (toContinuumPointField (formedField source) point) =
      diracDualFormNativeCoframeLocalDensity (SourceFamily.sourceAt (index source)) point
        (toContinuumPointField (SourceFamily.fieldAt (index source)) point) := by
  funext candidate
  unfold diracDualFormNativeCoframeLocalDensity sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  rw [Scalar.frozen_scalar_density_zero, Scalar.frozen_yukawa_density_zero,
    reference_scalar_zero, reference_yukawa_zero, Matter.frozen_kinetic_eq]
  unfold generatedFormNativeGravityBFDensity generatedFormNativeGravityConstraintDensity
    generatedFormNativeGaugeDensityAtBoundary gaugeConstitutiveOperatorAtBoundary
  simp only [withCoframe, toContinuumPointField, gravity_auxiliary_eq, gravity_multiplier_eq,
    gravity_curvature_eq, gauge_curvature_eq, gauge_auxiliary_eq, generatedGravitySimplicityResidual]
  simp only [sourceGeneratedUnifiedCouplings]
  have coupling := source_coupling source
  change source.legacy.sigma = (SourceFamily.sourceAt (index source)).legacy.sigma at coupling
  simp only [coupling]

theorem coframe_euler_zero (source : SmoothUnifiedSource) (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source (formedField source) point).coframe = 0 := by
  change diracDualFormNativeCoframeEulerCovector source point
    (toContinuumPointField (formedField source) point) = 0
  unfold diracDualFormNativeCoframeEulerCovector
  rw [coframe_density_eq]
  change fderiv ℝ _ ((formedField source).coframe point) = 0
  rw [coframe_eq]
  exact SourceFamily.Coframe.euler_zero (index source) point

theorem pointwise_zero (source : SmoothUnifiedSource) (point : BasePoint) :
    OnDiracDualFormNativePointwiseJointZeroFiber source (formedField source) point := by
  obtain ⟨multiplier, auxiliary, gaugeAuxiliary, lorentz⟩ := algebraic_channels source point
  exact (onDiracDualFormNativePointwiseJointZeroFiber_iff_components _ _ _).2
    ⟨multiplier, auxiliary, gaugeAuxiliary, lorentz, gauge_euler_zero source point,
      Scalar.residual_zero source point, funext (Matter.euler_zero source point),
      funext (conjugate_euler_zero source point), coframe_euler_zero source point⟩

theorem joint_zero (source : SmoothUnifiedSource) :
    DiracDualFormNativeJointZeroFiber source (formedField source) :=
  (diracDualFormNativeJointZeroFiber_iff_pointwise _ _).2 (pointwise_zero source)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation
