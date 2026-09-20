import H0mework.Physics.ConstitutiveAction.SpatialSectionResidual
import H0mework.Physics.FixedJoint.FixedConstitutiveDifferentialSectionResidual

/-!
# Gauge--scalar normal form of the constitutive spatial section

The section producer has already run before this module.  On its generated
time-zero slice we now identify two further coordinates of the complete
residual:

* the P286 connection coordinate is the existing contact-successor readout,
  because both configurations carry literally the same P286 connection and
  constitutive auxiliary fields, and the same charged point data on that
  slice;
* the scalar coordinate is the existing contact-successor readout, because
  the coframe, scalar, and P286 connection are whole-field equal while the
  matter and adjoint values agree on the slice.

Both equalities are diagnostic substitutions.  No residual coordinate,
support, sign, inverse image, or zero-fiber witness is consumed by a write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeScalarNormalForm

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionAlgebraicClosure
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeClosure
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionResidual
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveDifferentialSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineTopologicalP286GaugeThreeFormDuality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev SectionActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor

private abbrev ContactActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeConstitutiveJointActionSuccessor

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-! ## Whole-field and whole-slice seams -/

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_coframe_eq_contact :
    SectionActual.coframe = ContactActual.coframe := by
  calc
    SectionActual.coframe = InputActual.coframe :=
      diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_coframe
        positiveSmoothUnifiedSource InputActual
    _ = ContactActual.coframe :=
      fixedP506FormNativeConstitutiveJointActionSuccessor_coframe.symm

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeConnection_eq_contact :
    SectionActual.gaugeConnection = ContactActual.gaugeConnection := by
  calc
    SectionActual.gaugeConnection = InputActual.gaugeConnection :=
      diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeConnection
        positiveSmoothUnifiedSource InputActual
    _ = ContactActual.gaugeConnection :=
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection.symm

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalar_eq_contact :
    SectionActual.scalar = ContactActual.scalar := by
  calc
    SectionActual.scalar = InputActual.scalar :=
      diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_scalar
        positiveSmoothUnifiedSource InputActual
    _ = ContactActual.scalar :=
      fixedP506FormNativeConstitutiveJointActionSuccessor_scalar.symm

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeAuxiliary_eq_contact :
    SectionActual.gaugeAuxiliary = ContactActual.gaugeAuxiliary := by
  funext point pair
  change
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
      positiveSmoothUnifiedSource InputActual).gaugeAuxiliary point pair =
      FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeAuxiliary
        point pair
  rw [
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary
      positiveSmoothUnifiedSource InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth point,
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeAuxiliary]
  rfl

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_matter_zeroSlice_eq_contact
    (space : StageNineSpatialPoint) :
    SectionActual.matter (canonicalCauchySlicePoint 0 space) =
      ContactActual.matter (canonicalCauchySlicePoint 0 space) := by
  calc
    SectionActual.matter (canonicalCauchySlicePoint 0 space) =
        InputActual.matter (canonicalCauchySlicePoint 0 space) :=
      diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_matter_zeroSlice
        positiveSmoothUnifiedSource InputActual space
    _ = ContactActual.matter (canonicalCauchySlicePoint 0 space) := by
      change
        InputActual.matter (canonicalCauchySlicePoint 0 space) =
          FixedP506FormNativeConstitutiveJointActionSuccessor.matter
            (canonicalCauchySlicePoint 0 space)
      rw [
        fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator]
      exact
        (diracDualFormNativeConstitutiveJointActionResponseOperator_matter_zeroSlice
          positiveSmoothUnifiedSource InputActual space).symm

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_conjugateMatter_zeroSlice_eq_contact
    (space : StageNineSpatialPoint) :
    SectionActual.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      ContactActual.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
  calc
    SectionActual.conjugateMatter (canonicalCauchySlicePoint 0 space) =
        InputActual.conjugateMatter (canonicalCauchySlicePoint 0 space) :=
      diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_conjugateMatter_zeroSlice
        positiveSmoothUnifiedSource InputActual space
    _ =
        ContactActual.conjugateMatter
          (canonicalCauchySlicePoint 0 space) := by
      change
        InputActual.conjugateMatter (canonicalCauchySlicePoint 0 space) =
          FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter
            (canonicalCauchySlicePoint 0 space)
      rw [
        fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator]
      exact
        (diracDualFormNativeConstitutiveJointActionResponseOperator_conjugateMatter_zeroSlice
          positiveSmoothUnifiedSource InputActual space).symm

/-! ## P286 connection coordinate -/

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeAuxiliaryExteriorCovariantDerivative_eq_contact
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative SectionActual
        point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative ContactActual
        point := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeConnection_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeAuxiliary_eq_contact]

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarCovariantDerivative_eq_contact :
    holonomicScalarCovariantDerivative SectionActual =
      holonomicScalarCovariantDerivative ContactActual := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalar_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeConnection_eq_contact]

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_volume_eq_contact
    (point : BasePoint) :
    generatedVolumeDensity (toContinuumPointField SectionActual point) =
      generatedVolumeDensity (toContinuumPointField ContactActual point) := by
  unfold generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_coframe_eq_contact]

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarGaugeKinetic_eq_contact
    (point : BasePoint)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 point
        (toContinuumPointField SectionActual point) variation =
      scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 point
        (toContinuumPointField ContactActual point) variation := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  simp only [toContinuumPointField]
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_coframe_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarCovariantDerivative_eq_contact]

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarPotential_zeroSlice_eq_contact
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField SectionActual
          (canonicalCauchySlicePoint 0 space))
        direction =
      scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField ContactActual
          (canonicalCauchySlicePoint 0 space))
        direction := by
  unfold scalarPotentialFirstVariation
  simp only [toContinuumPointField]
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalar_eq_contact]

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarYukawa_zeroSlice_eq_contact
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarYukawaFirstVariationDensity
        (toContinuumPointField SectionActual
          (canonicalCauchySlicePoint 0 space))
        direction =
      diracDualScalarYukawaFirstVariationDensity
        (toContinuumPointField ContactActual
          (canonicalCauchySlicePoint 0 space))
        direction := by
  unfold diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
  simp only [toContinuumPointField]
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_matter_zeroSlice_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_conjugateMatter_zeroSlice_eq_contact]

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_pointwiseScalarGaugeVariation_zeroSlice_eq_contact
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField SectionActual
          (canonicalCauchySlicePoint 0 space))
        direction =
      pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField ContactActual
          (canonicalCauchySlicePoint 0 space))
        direction := by
  funext formDirection
  unfold pointwiseScalarP286GaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalar_eq_contact]

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_pointwiseMatterGaugeVariation_zeroSlice_eq_contact
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField SectionActual
          (canonicalCauchySlicePoint 0 space))
        direction =
      pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField ContactActual
          (canonicalCauchySlicePoint 0 space))
        direction := by
  funext formDirection
  unfold pointwiseMatterP286GaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_matter_zeroSlice_eq_contact]

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_matterGaugeKinetic_zeroSlice_eq_contact
    (space : StageNineSpatialPoint)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField SectionActual
          (canonicalCauchySlicePoint 0 space))
        variation =
      matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField ContactActual
          (canonicalCauchySlicePoint 0 space))
        variation := by
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [toContinuumPointField]
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_coframe_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_conjugateMatter_zeroSlice_eq_contact]

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_chargedGaugeThreeForm_zeroSlice_eq_contact
    (space : StageNineSpatialPoint) :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField SectionActual
          (canonicalCauchySlicePoint 0 space)) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField ContactActual
          (canonicalCauchySlicePoint 0 space)) := by
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro direction
  change
    formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField SectionActual
          (canonicalCauchySlicePoint 0 space))
        direction =
      formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField ContactActual
          (canonicalCauchySlicePoint 0 space))
        direction
  unfold formNativeChargedGaugeFirstCoefficient
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_volume_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_pointwiseScalarGaugeVariation_zeroSlice_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_pointwiseMatterGaugeVariation_zeroSlice_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarGaugeKinetic_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_matterGaugeKinetic_zeroSlice_eq_contact]

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_p286GaugeConnection_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).p286GaugeConnection =
      fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
        space := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        SectionActual (canonicalCauchySlicePoint 0 space) =
      _
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeAuxiliaryExteriorCovariantDerivative_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_chargedGaugeThreeForm_zeroSlice_eq_contact]
  exact
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_zeroSlice_explicitNormalForm
      space

/-! ## Scalar coordinate -/

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarDifferentialMomentum_eq_contact
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource SectionActual
        direction derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource ContactActual
        direction derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_volume_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarGaugeKinetic_eq_contact]

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarDifferentialMomentumDivergence_eq_contact
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        SectionActual direction =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        ContactActual direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarDifferentialMomentum_eq_contact]

private theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarAlgebraic_zeroSlice_eq_contact
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        SectionActual direction (canonicalCauchySlicePoint 0 space) =
    diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        ContactActual direction (canonicalCauchySlicePoint 0 space) := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  have algebraicDirection :
      holonomicScalarVariationAlgebraicDirection SectionActual direction
          (canonicalCauchySlicePoint 0 space) =
        holonomicScalarVariationAlgebraicDirection ContactActual direction
          (canonicalCauchySlicePoint 0 space) := by
    unfold holonomicScalarVariationAlgebraicDirection
    rw [
      fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeConnection_eq_contact]
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_volume_eq_contact,
    algebraicDirection,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarGaugeKinetic_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarPotential_zeroSlice_eq_contact,
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarYukawa_zeroSlice_eq_contact]

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_scalar_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).scalar =
      fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
        space := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource SectionActual direction
          (canonicalCauchySlicePoint 0 space) =
      _
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarAlgebraic_zeroSlice_eq_contact,
    congrFun
      (fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_scalarDifferentialMomentumDivergence_eq_contact
        direction)
      (canonicalCauchySlicePoint 0 space)]
  exact
    congrFun
      (fixedP506FormNativeConstitutiveJointActionSuccessorResidual_scalar_zeroSlice_normalForm
        space)
      direction

/-! ## Six-channel carrier checkpoint -/

def
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSixChannelResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { fixedP506FormNativeConstitutiveJointActionSpatialSectionFourChannelResidualZeroSliceNormalForm
      space with
    p286GaugeConnection :=
      fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
        space
    scalar :=
      fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
        space }

/-- Six coordinates of the one complete residual carrier are now in exact
normal form.  Matter, adjoint, and coframe remain literal coordinates of the
same section actual until the shared first-jet seam is computed. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_zeroSlice_sixChannelNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveJointActionSpatialSectionResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSpatialSectionSixChannelResidualZeroSliceNormalForm
        space := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_gravityMultiplier_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_gravityAuxiliary_normalForm
        0 space
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_p286GaugeAuxiliary_zeroSlice
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_lorentzConnection_zeroSlice_normalForm
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_p286GaugeConnection_zeroSlice_normalForm
        space
  · exact
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_scalar_zeroSlice_normalForm
        space
  · rfl
  · rfl
  · rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeScalarNormalForm
