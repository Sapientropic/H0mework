import H0mework.Physics.ConstitutiveAction.SpatialSectionGaugeScalarNormalForm
import H0mework.Physics.RepairedAction.ActionSpatialSectionResidual

/-!
# Gauge--scalar normal form of the repaired spatial section

The repaired and historical section operators preserve the same whole
coframe, P286 connection, scalar, and constitutive auxiliary fields.  Their
matter and adjoint values also agree on the generated time-zero slice.
Consequently the P286 and scalar residual coordinates can be recomputed on
the repaired actual and compared to the already explicit historical
readouts.

This comparison transports field occurrences, not equation receipts.  The
resulting residual coordinates remain diagnostic and do not select a write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionGaugeScalarNormalForm

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeClosure
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeScalarNormalForm
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveDifferentialSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual
open StageNineDiracDualFormNativeScalarVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineTopologicalP286GaugeThreeFormDuality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev RepairedActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor

private abbrev HistoricalActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-! ## Field-occurrence seams -/

theorem repairedSection_coframe_eq_historical :
    RepairedActual.coframe = HistoricalActual.coframe := by
  calc
    RepairedActual.coframe = InputActual.coframe :=
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe
        positiveSmoothUnifiedSource InputActual
    _ = HistoricalActual.coframe :=
      (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_coframe
        positiveSmoothUnifiedSource InputActual).symm

theorem repairedSection_gaugeConnection_eq_historical :
    RepairedActual.gaugeConnection =
      HistoricalActual.gaugeConnection := by
  calc
    RepairedActual.gaugeConnection = InputActual.gaugeConnection :=
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection
        positiveSmoothUnifiedSource InputActual
    _ = HistoricalActual.gaugeConnection :=
      (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeConnection
        positiveSmoothUnifiedSource InputActual).symm

theorem repairedSection_scalar_eq_historical :
    RepairedActual.scalar = HistoricalActual.scalar := by
  calc
    RepairedActual.scalar = InputActual.scalar :=
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar
        positiveSmoothUnifiedSource InputActual
    _ = HistoricalActual.scalar :=
      (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_scalar
        positiveSmoothUnifiedSource InputActual).symm

theorem repairedSection_gaugeAuxiliary_eq_historical :
    RepairedActual.gaugeAuxiliary =
      HistoricalActual.gaugeAuxiliary := by
  funext point
  change
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      positiveSmoothUnifiedSource InputActual).gaugeAuxiliary point =
      (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        positiveSmoothUnifiedSource InputActual).gaugeAuxiliary point
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary
      positiveSmoothUnifiedSource InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth point,
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary
      positiveSmoothUnifiedSource InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth point]

theorem repairedSection_matter_zeroSlice_eq_historical
    (space : StageNineSpatialPoint) :
    RepairedActual.matter (canonicalCauchySlicePoint 0 space) =
      HistoricalActual.matter (canonicalCauchySlicePoint 0 space) := by
  calc
    RepairedActual.matter (canonicalCauchySlicePoint 0 space) =
        InputActual.matter (canonicalCauchySlicePoint 0 space) :=
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_matter_zeroSlice
        positiveSmoothUnifiedSource InputActual space
    _ = HistoricalActual.matter (canonicalCauchySlicePoint 0 space) :=
      (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_matter_zeroSlice
        positiveSmoothUnifiedSource InputActual space).symm

theorem repairedSection_conjugateMatter_zeroSlice_eq_historical
    (space : StageNineSpatialPoint) :
    RepairedActual.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      HistoricalActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) := by
  calc
    RepairedActual.conjugateMatter (canonicalCauchySlicePoint 0 space) =
        InputActual.conjugateMatter (canonicalCauchySlicePoint 0 space) :=
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_zeroSlice
        positiveSmoothUnifiedSource InputActual space
    _ = HistoricalActual.conjugateMatter
          (canonicalCauchySlicePoint 0 space) :=
      (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_conjugateMatter_zeroSlice
        positiveSmoothUnifiedSource InputActual space).symm

/-! ## P286 connection coordinate -/

private theorem repairedSection_gaugeAuxiliaryExteriorCovariantDerivative_eq_historical
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative RepairedActual
        point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative HistoricalActual
        point := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [repairedSection_gaugeConnection_eq_historical,
    repairedSection_gaugeAuxiliary_eq_historical]

private theorem repairedSection_scalarCovariantDerivative_eq_historical :
    holonomicScalarCovariantDerivative RepairedActual =
      holonomicScalarCovariantDerivative HistoricalActual := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [repairedSection_scalar_eq_historical,
    repairedSection_gaugeConnection_eq_historical]

private theorem repairedSection_volume_eq_historical
    (point : BasePoint) :
    generatedVolumeDensity (toContinuumPointField RepairedActual point) =
      generatedVolumeDensity
        (toContinuumPointField HistoricalActual point) := by
  unfold generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [repairedSection_coframe_eq_historical]

private theorem repairedSection_scalarGaugeKinetic_eq_historical
    (point : BasePoint)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 point
        (toContinuumPointField RepairedActual point) variation =
      scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 point
        (toContinuumPointField HistoricalActual point) variation := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  simp only [toContinuumPointField]
  rw [repairedSection_coframe_eq_historical,
    repairedSection_scalarCovariantDerivative_eq_historical]

private theorem repairedSection_scalarPotential_zeroSlice_eq_historical
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField RepairedActual
          (canonicalCauchySlicePoint 0 space))
        direction =
      scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField HistoricalActual
          (canonicalCauchySlicePoint 0 space))
        direction := by
  unfold scalarPotentialFirstVariation
  simp only [toContinuumPointField]
  rw [repairedSection_scalar_eq_historical]

private theorem repairedSection_scalarYukawa_zeroSlice_eq_historical
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarYukawaFirstVariationDensity
        (toContinuumPointField RepairedActual
          (canonicalCauchySlicePoint 0 space))
        direction =
      diracDualScalarYukawaFirstVariationDensity
        (toContinuumPointField HistoricalActual
          (canonicalCauchySlicePoint 0 space))
        direction := by
  unfold diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
  simp only [toContinuumPointField]
  rw [repairedSection_matter_zeroSlice_eq_historical,
    repairedSection_conjugateMatter_zeroSlice_eq_historical]

private theorem repairedSection_pointwiseScalarGaugeVariation_zeroSlice_eq_historical
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField RepairedActual
          (canonicalCauchySlicePoint 0 space))
        direction =
      pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField HistoricalActual
          (canonicalCauchySlicePoint 0 space))
        direction := by
  funext formDirection
  unfold pointwiseScalarP286GaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [repairedSection_scalar_eq_historical]

private theorem repairedSection_pointwiseMatterGaugeVariation_zeroSlice_eq_historical
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField RepairedActual
          (canonicalCauchySlicePoint 0 space))
        direction =
      pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField HistoricalActual
          (canonicalCauchySlicePoint 0 space))
        direction := by
  funext formDirection
  unfold pointwiseMatterP286GaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [repairedSection_matter_zeroSlice_eq_historical]

private theorem repairedSection_matterGaugeKinetic_zeroSlice_eq_historical
    (space : StageNineSpatialPoint)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField RepairedActual
          (canonicalCauchySlicePoint 0 space))
        variation =
      matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField HistoricalActual
          (canonicalCauchySlicePoint 0 space))
        variation := by
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [toContinuumPointField]
  rw [repairedSection_coframe_eq_historical,
    repairedSection_conjugateMatter_zeroSlice_eq_historical]

private theorem repairedSection_chargedGaugeThreeForm_zeroSlice_eq_historical
    (space : StageNineSpatialPoint) :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField RepairedActual
          (canonicalCauchySlicePoint 0 space)) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField HistoricalActual
          (canonicalCauchySlicePoint 0 space)) := by
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro direction
  change
    formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField RepairedActual
          (canonicalCauchySlicePoint 0 space))
        direction =
      formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField HistoricalActual
          (canonicalCauchySlicePoint 0 space))
        direction
  unfold formNativeChargedGaugeFirstCoefficient
  rw [repairedSection_volume_eq_historical,
    repairedSection_pointwiseScalarGaugeVariation_zeroSlice_eq_historical,
    repairedSection_pointwiseMatterGaugeVariation_zeroSlice_eq_historical,
    repairedSection_scalarGaugeKinetic_eq_historical,
    repairedSection_matterGaugeKinetic_zeroSlice_eq_historical]

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_p286GaugeConnection_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).p286GaugeConnection =
      fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
        space := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        RepairedActual (canonicalCauchySlicePoint 0 space) =
      _
  calc
    _ =
        holonomicFormNativeP286GaugeEulerThreeForm
          positiveSmoothUnifiedSource 0 HistoricalActual
          (canonicalCauchySlicePoint 0 space) := by
      unfold holonomicFormNativeP286GaugeEulerThreeForm
      rw [
        repairedSection_gaugeAuxiliaryExteriorCovariantDerivative_eq_historical,
        repairedSection_chargedGaugeThreeForm_zeroSlice_eq_historical]
    _ = _ :=
      fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_p286GaugeConnection_zeroSlice_normalForm
        space

/-! ## Scalar coordinate -/

private theorem repairedSection_scalarDifferentialMomentum_eq_historical
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource RepairedActual
        direction derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource HistoricalActual
        direction derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
  rw [repairedSection_volume_eq_historical,
    repairedSection_scalarGaugeKinetic_eq_historical]

private theorem repairedSection_scalarDifferentialMomentumDivergence_eq_historical
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        RepairedActual direction =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        HistoricalActual direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [repairedSection_scalarDifferentialMomentum_eq_historical]

private theorem repairedSection_scalarAlgebraic_zeroSlice_eq_historical
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        RepairedActual direction (canonicalCauchySlicePoint 0 space) =
      diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource HistoricalActual direction
        (canonicalCauchySlicePoint 0 space) := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  have algebraicDirection :
      holonomicScalarVariationAlgebraicDirection RepairedActual direction
          (canonicalCauchySlicePoint 0 space) =
        holonomicScalarVariationAlgebraicDirection HistoricalActual direction
          (canonicalCauchySlicePoint 0 space) := by
    unfold holonomicScalarVariationAlgebraicDirection
    rw [repairedSection_gaugeConnection_eq_historical]
  rw [repairedSection_volume_eq_historical, algebraicDirection,
    repairedSection_scalarGaugeKinetic_eq_historical,
    repairedSection_scalarPotential_zeroSlice_eq_historical,
    repairedSection_scalarYukawa_zeroSlice_eq_historical]

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_scalar_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).scalar =
      fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
        space := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource RepairedActual direction
          (canonicalCauchySlicePoint 0 space) =
      _
  calc
    _ =
        diracDualScalarEulerLagrangeDirectionalCoefficient
          positiveSmoothUnifiedSource HistoricalActual direction
          (canonicalCauchySlicePoint 0 space) := by
      unfold diracDualScalarEulerLagrangeDirectionalCoefficient
      rw [repairedSection_scalarAlgebraic_zeroSlice_eq_historical,
        congrFun
          (repairedSection_scalarDifferentialMomentumDivergence_eq_historical
            direction)
          (canonicalCauchySlicePoint 0 space)]
    _ = _ :=
      congrFun
        (fixedP506FormNativeConstitutiveJointActionSpatialSectionResidual_scalar_zeroSlice_normalForm
          space)
        direction

/-! ## Six-channel checkpoint -/

def
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSixChannelResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFourChannelResidualZeroSliceNormalForm
      space with
    p286GaugeConnection :=
      fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
        space
    scalar :=
      fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
        space }

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_zeroSlice_sixChannelNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSixChannelResidualZeroSliceNormalForm
        space := by
  have fourChannel :=
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_zeroSlice_fourChannelNormalForm
      space
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · simpa [
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSixChannelResidualZeroSliceNormalForm]
      using congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.gravityMultiplier
        fourChannel
  · simpa [
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSixChannelResidualZeroSliceNormalForm]
      using congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.gravityAuxiliary
        fourChannel
  · simpa [
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSixChannelResidualZeroSliceNormalForm]
      using congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.p286GaugeAuxiliary
        fourChannel
  · simpa [
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSixChannelResidualZeroSliceNormalForm]
      using congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.lorentzConnection
        fourChannel
  · exact
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_p286GaugeConnection_zeroSlice_normalForm
        space
  · exact
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_scalar_zeroSlice_normalForm
        space
  · rfl
  · rfl
  · rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionGaugeScalarNormalForm
