import H0mework.Physics.FullOccurrence.FixedP286ZeroSliceObstruction
import H0mework.Physics.Cauchy.P286ConnectionRelativeScalarCauchyDevelopmentOperator

/-!
# Fixed P506/L0 U6 connection-relative scalar diagnostic

The full-occurrence U6 diagonal kept the source-generated P286 connection but
retained a scalar first jet that was not horizontal for its point-dependent
temporal connection.  This module applies the connection-relative scalar
Cauchy diagnostic to that same U6.  The derived actual is determined by U6
alone, retains the entire zero-slice scalar value and every other primitive
field, and makes the temporal scalar covariant derivative vanish on the zero
slice.

The construction consumes no P286 residual, no `7/36` coordinate, no support
witness, and no target actual.  The old U6 nonzero theorem remains the negative
regression showing exactly what the horizontal read-after-write calculation
changes.  This module does not claim that the scalar mother action generated
that first jet; the explicit authority boundary is recorded below.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6ConnectionRelativeScalarSettlement

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConnectionSectorSourceBalance
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ConnectionRelativeScalarCauchyDevelopmentOperator
open StageNineP286ConnectionGeneratedScalarParallelTransport
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source Input

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source Input

private abbrev PreEC : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private def SpatialE0 : StageNineSpatialPoint :=
  EuclideanSpace.single 0 1

/-- The connection-horizontal diagnostic actual derived from fixed U6. -/
def fixedP506L0U6ConnectionRelativeScalarActual :
    StageNineHolonomicConfiguration :=
  p286ConnectionRelativeScalarCauchyDevelopmentOperator U6

private def SmoothReference : StageNineHolonomicConfiguration :=
  { Input with gaugeConnection := U6.gaugeConnection }

private theorem smoothReference_smooth : SmoothReference.Smooth := by
  rcases fixedP506FormNativeJointActionSolvedSuccessor_smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, _gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  refine ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    multiplierSmooth, ?_, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
    conjugateMatterSmooth⟩
  intro direction
  unfold SmoothReference
  rw [
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current]
  exact
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnectionCoordinate_contDiff
      direction

private abbrev ReferenceHorizontal : StageNineHolonomicConfiguration :=
  p286ConnectionRelativeScalarCauchyDevelopmentOperator SmoothReference

private theorem u5_scalar_eq_temporal : U5.scalar = Temporal.scalar := by
  calc
    U5.scalar =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.scalar :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC
    _ = fixedP506L0CompleteJointGlobalDevelopmentActual.scalar :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_eq_existing
    _ = Temporal.scalar := by rfl

private theorem algebraic_eq_zeroCandidate :
    Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source Temporal 0 := by
  exact fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate

private theorem algebraic_coframe_eq_temporal :
    Algebraic.coframe = Temporal.coframe := by
  rw [algebraic_eq_zeroCandidate]
  rfl

private theorem algebraic_gaugeConnection_eq_temporal :
    Algebraic.gaugeConnection = Temporal.gaugeConnection := by
  rw [algebraic_eq_zeroCandidate,
    diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rfl

private theorem preEC_coframe_eq_temporal :
    PreEC.coframe = Temporal.coframe := by
  calc
    PreEC.coframe = Algebraic.coframe :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe
        Source Input
    _ = Temporal.coframe := algebraic_coframe_eq_temporal

private theorem preEC_gaugeConnection_eq_temporal :
    PreEC.gaugeConnection = Temporal.gaugeConnection := by
  calc
    PreEC.gaugeConnection = Algebraic.gaugeConnection :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
        Source Input
    _ = Temporal.gaugeConnection := algebraic_gaugeConnection_eq_temporal

private theorem u5_coframe_eq_temporal : U5.coframe = Temporal.coframe :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC.trans
    preEC_coframe_eq_temporal

private theorem u5_gaugeConnection_eq_temporal :
    U5.gaugeConnection = Temporal.gaugeConnection :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC.trans
    preEC_gaugeConnection_eq_temporal

private theorem u6_scalar_eq_u5 : U6.scalar = U5.scalar := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source U5).scalar = U5.scalar
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
      Source U5

private theorem u6_coframe_eq_temporal : U6.coframe = Temporal.coframe := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source U5).coframe = Temporal.coframe
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
      Source U5).trans u5_coframe_eq_temporal

private theorem u6_gaugeConnection_eq_temporal :
    U6.gaugeConnection = Temporal.gaugeConnection :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current.trans
    u5_gaugeConnection_eq_temporal

private theorem u6_scalar_eq_temporal : U6.scalar = Temporal.scalar :=
  u6_scalar_eq_u5.trans u5_scalar_eq_temporal

private theorem u6_scalarCovariantDerivative_eq_temporal
    (point : BasePoint) :
    holonomicScalarCovariantDerivative U6 point =
      holonomicScalarCovariantDerivative Temporal point := by
  unfold holonomicScalarCovariantDerivative
  rw [u6_scalar_eq_temporal, u6_gaugeConnection_eq_temporal]

private theorem u6_scalarCurrent_eq_temporal
    (point : BasePoint)
    (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient Source U6 direction point =
      p286ScalarCurrentCoefficient Source Temporal direction point := by
  unfold p286ScalarCurrentCoefficient generatedVolumeDensity
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
    holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [toContinuumPointField,
    StageNineP286GaugeConnectionVariationDensity.scalarFrameRelativeCoordinates_zeroChart]
  rw [congrFun u6_coframe_eq_temporal point,
    congrFun u6_scalar_eq_temporal point,
    u6_scalarCovariantDerivative_eq_temporal]

private theorem u6_scalar_zeroSlice_eq_input
    (space : StageNineSpatialPoint) :
    U6.scalar (canonicalCauchySlicePoint 0 space) =
      Input.scalar (canonicalCauchySlicePoint 0 space) := by
  calc
    U6.scalar (canonicalCauchySlicePoint 0 space) =
        U5.scalar (canonicalCauchySlicePoint 0 space) :=
      congrFun u6_scalar_eq_u5 _
    _ = Temporal.scalar (canonicalCauchySlicePoint 0 space) := by
      rw [u5_scalar_eq_temporal]
    _ = Input.scalar (canonicalCauchySlicePoint 0 space) :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
        Source Input space

/-! ## Exact authority boundary

The connection read by U6 has genuine fixed P506/L0 action-write provenance.
The representation exponential below therefore uses the correct physical
connection occurrence.  These theorems deliberately stop short of claiming
that the scalar mother action selected the parallel first jet: connection
authority is necessary but not sufficient for scalar-write authority.
-/

/-- U6 retains the connection of the fixed source/action solved input. -/
theorem fixedP506L0U6_gaugeConnection_eq_actionSolvedInput :
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gaugeConnection =
      FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection := by
  exact u6_gaugeConnection_eq_temporal.trans rfl

/-- The retained U6 connection is exactly the existing P286 action write,
not a connection reconstructed from the later `7/36` readout. -/
theorem fixedP506L0U6_gaugeConnection_eq_actionWrite :
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gaugeConnection =
      (installP286HolonomicConnectionSecondJet
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        fixedP506FormNativeCompleteActionSecondJet 1).gaugeConnection := by
  exact fixedP506L0U6_gaugeConnection_eq_actionSolvedInput.trans
    fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnection_actionWrite

/-- Representation orbit anchored in the fixed solved input whose connection
was generated by the P286 action write. -/
def fixedP506L0ActionWrittenConnectionScalarParallelOrbit
    (space : StageNineSpatialPoint) (time : ℝ) : ScalarCoordinateCarrier :=
  p286ConnectionGeneratedScalarParallelOrbit Input space time

/-- U6's diagnostic orbit is literally the orbit of the action-written
connection and the same zero-slice scalar anchor. -/
theorem fixedP506L0U6_scalarParallelOrbit_eq_actionWrittenConnectionOrbit
    (space : StageNineSpatialPoint) :
    p286ConnectionGeneratedScalarParallelOrbit U6 space =
      fixedP506L0ActionWrittenConnectionScalarParallelOrbit space := by
  funext time
  unfold fixedP506L0ActionWrittenConnectionScalarParallelOrbit
    p286ConnectionGeneratedScalarParallelOrbit
    p286CurrentTemporalConnectionCoordinate
    p286CurrentScalarZeroSliceAnchor
  rw [fixedP506L0U6_gaugeConnection_eq_actionSolvedInput,
    u6_scalar_zeroSlice_eq_input]

/-- The installed diagnostic velocity is the tangent of a representation
orbit using the exact action-written U6 connection.  It remains a transporter
fact, not a scalar mother-action producer theorem. -/
theorem
    fixedP506L0U6_connectionRelativeScalarVelocity_is_actionConnectionOrbitDerivative
    (space : StageNineSpatialPoint) :
    NormedHasDerivAt
      (fixedP506L0ActionWrittenConnectionScalarParallelOrbit space)
      (p286ConnectionRelativeScalarVelocity U6 space) 0 := by
  have generated :=
    p286ConnectionRelativeScalarVelocity_is_parallelOrbitDerivative U6 space
  rw [fixedP506L0U6_scalarParallelOrbit_eq_actionWrittenConnectionOrbit] at generated
  exact generated

private theorem u6_zeroSliceAnchor_eq_reference :
    p286ConnectionRelativeScalarZeroSliceAnchor U6 =
      p286ConnectionRelativeScalarZeroSliceAnchor SmoothReference := by
  funext space
  exact u6_scalar_zeroSlice_eq_input space

private theorem u6_velocity_eq_reference :
    p286ConnectionRelativeScalarVelocity U6 =
      p286ConnectionRelativeScalarVelocity SmoothReference := by
  funext space
  unfold p286ConnectionRelativeScalarVelocity
    p286ConnectionGeneratedScalarParallelVelocity
    p286CurrentTemporalConnectionCoordinate
    p286CurrentScalarZeroSliceAnchor
  rw [u6_scalar_zeroSlice_eq_input]
  rfl

private theorem horizontal_scalar_eq_reference :
    fixedP506L0U6ConnectionRelativeScalarActual.scalar =
      ReferenceHorizontal.scalar := by
  funext point
  unfold fixedP506L0U6ConnectionRelativeScalarActual ReferenceHorizontal
    p286ConnectionRelativeScalarCauchyDevelopmentOperator
  rw [u6_zeroSliceAnchor_eq_reference, u6_velocity_eq_reference]

private theorem horizontal_scalar_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      fixedP506L0U6ConnectionRelativeScalarActual.scalar
      (canonicalCauchySlicePoint 0 space) := by
  rw [horizontal_scalar_eq_reference]
  exact
    (p286ConnectionRelativeScalarCauchyDevelopmentOperator_smooth
      SmoothReference smoothReference_smooth
      ).2.2.2.2.2.2.1.differentiable (by simp) |>.differentiableAt

private theorem input_scalar_vacuum :
    Input.scalar = fun _ => sourceGeneratedVacuumCoordinates Source := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar,
    fixedP506JointActual_scalar_vacuum]

private theorem referenceHorizontal_scalar_spatialDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    fieldDirectionalDerivative ReferenceHorizontal.scalar
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  rw [
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_scalar_spatialDirectionalDerivative_zeroSlice
      SmoothReference space axis
      (smoothReference_smooth.2.2.2.2.2.2.1.differentiable (by simp)
        |>.differentiableAt)
      ((p286ConnectionRelativeScalarCauchyDevelopmentOperator_smooth
        SmoothReference smoothReference_smooth
        ).2.2.2.2.2.2.1.differentiable (by simp) |>.differentiableAt)]
  change
    fieldDirectionalDerivative Input.scalar
      (canonicalCauchySlicePoint 0 space) axis.succ = 0
  rw [input_scalar_vacuum]
  simp [fieldDirectionalDerivative]

private theorem horizontal_scalar_spatialDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    fieldDirectionalDerivative
        fixedP506L0U6ConnectionRelativeScalarActual.scalar
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  rw [horizontal_scalar_eq_reference]
  exact referenceHorizontal_scalar_spatialDerivative_zeroSlice space axis

private theorem input_connectionCoordinate_zeroSlice_spatial
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    holonomicP286GaugeConnectionCoordinate Input
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_connection_normalForm]
  have line :=
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line
      (-(canonicalCauchySlicePoint 0 space)) axis.succ
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm]
      at line
  unfold fixedP506FormNativeJointActionSolvedConnectionNormalForm
  simp only [Pi.neg_apply, line]
  fin_cases axis <;>
    simp [c3h181FullConnectionCoefficient, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection]

private theorem horizontal_gaugeConnection_zeroSlice_spatial
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    fixedP506L0U6ConnectionRelativeScalarActual.gaugeConnection
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  have coordinateZero :
      holonomicP286GaugeConnectionCoordinate
          fixedP506L0U6ConnectionRelativeScalarActual
          (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
    unfold fixedP506L0U6ConnectionRelativeScalarActual
    unfold holonomicP286GaugeConnectionCoordinate
    rw [p286ConnectionRelativeScalarCauchyDevelopmentOperator_gaugeConnection]
    rw [congrFun u6_gaugeConnection_eq_temporal
      (canonicalCauchySlicePoint 0 space)]
    change
      holonomicP286GaugeConnectionCoordinate Input
          (canonicalCauchySlicePoint 0 space) axis.succ = 0
    exact input_connectionCoordinate_zeroSlice_spatial space axis
  apply p286CoordinateEquiv.injective
  simpa only [holonomicP286GaugeConnectionCoordinate, map_zero] using
    coordinateZero

private theorem
    fixedP506L0U6ConnectionRelativeScalarActual_scalarCovariantDerivative_spatial_zeroSlice
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    holonomicScalarCovariantDerivative
        fixedP506L0U6ConnectionRelativeScalarActual
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  unfold holonomicScalarCovariantDerivative
  rw [horizontal_scalar_spatialDerivative_zeroSlice,
    horizontal_gaugeConnection_zeroSlice_spatial]
  simp

/-- The U6-derived diagnostic actual realizes the connection-horizontal
scalar law on every point of the complete zero slice. -/
theorem
    fixedP506L0U6ConnectionRelativeScalarActual_temporalCovariantDerivative_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative
        fixedP506L0U6ConnectionRelativeScalarActual
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection = 0 := by
  exact
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_temporalCovariantDerivative_zeroSlice_of_differentiable
      U6 space (horizontal_scalar_differentiableAt_zeroSlice space)

/-- On the fixed P506/L0 zero slice the diagnostic horizontal realization is
horizontal in all four spacetime directions: the temporal representation law
is combined with the inherited constant vacuum and the action-generated
vanishing spatial connection. -/
theorem
    fixedP506L0U6ConnectionRelativeScalarActual_scalarCovariantDerivative_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative
        fixedP506L0U6ConnectionRelativeScalarActual
        (canonicalCauchySlicePoint 0 space) = 0 := by
  funext direction
  fin_cases direction
  · simpa [canonicalLorentzianTimeDirection] using
      fixedP506L0U6ConnectionRelativeScalarActual_temporalCovariantDerivative_zeroSlice
        space
  · exact
      fixedP506L0U6ConnectionRelativeScalarActual_scalarCovariantDerivative_spatial_zeroSlice
        space 0
  · exact
      fixedP506L0U6ConnectionRelativeScalarActual_scalarCovariantDerivative_spatial_zeroSlice
        space 1
  · exact
      fixedP506L0U6ConnectionRelativeScalarActual_scalarCovariantDerivative_spatial_zeroSlice
        space 2

private theorem u6_coframe_one_zeroSlice
    (space : StageNineSpatialPoint) :
    U6.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
  rw [congrFun u6_coframe_eq_temporal
    (canonicalCauchySlicePoint 0 space)]
  change Input.coframe (canonicalCauchySlicePoint 0 space) = 1
  exact fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space

private theorem u6_temporalHypercharge_scalarCurrent_e0 :
    p286ScalarCurrentCoefficient Source U6
        (p286TemporalGaugeOneForm hyperchargeCoordinate)
        (canonicalCauchySlicePoint 0 SpatialE0) = 7 / 36 := by
  rw [u6_scalarCurrent_eq_temporal]
  change
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
        (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor)
        (p286TemporalGaugeOneForm hyperchargeCoordinate)
        (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1)) =
      7 / 36
  exact
    StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286ZeroSliceObstruction.fixedP506L0_Temporal_scalarCurrent_zeroSlice_spatialE0_temporalHypercharge_eq

/-- The connection-relative diagnostic removes the scalar contribution to
every temporal P286 variation on the complete zero slice. -/
theorem
    fixedP506L0U6ConnectionRelativeScalarActual_scalarCurrent_temporal_zeroSlice
    (space : StageNineSpatialPoint)
    (component : P286CoordinateCarrier) :
    p286ScalarCurrentCoefficient Source
        fixedP506L0U6ConnectionRelativeScalarActual
        (p286TemporalGaugeOneForm component)
        (canonicalCauchySlicePoint 0 space) = 0 := by
  apply p286ScalarCurrentCoefficient_temporal_eq_zero
  · change U6.coframe (canonicalCauchySlicePoint 0 space) = 1
    exact u6_coframe_one_zeroSlice space
  · exact
      fixedP506L0U6ConnectionRelativeScalarActual_temporalCovariantDerivative_zeroSlice
        space

/-- The complete scalar current, not only its temporal test family, vanishes
on the diagnostic zero slice. -/
theorem
    fixedP506L0U6ConnectionRelativeScalarActual_scalarCurrent_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient Source
        fixedP506L0U6ConnectionRelativeScalarActual direction
        (canonicalCauchySlicePoint 0 space) = 0 := by
  exact
    p286ScalarCurrentCoefficient_eq_zero_of_covariantDerivative_zero
      Source fixedP506L0U6ConnectionRelativeScalarActual
      (canonicalCauchySlicePoint 0 space) direction
      (fixedP506L0U6ConnectionRelativeScalarActual_scalarCovariantDerivative_zeroSlice
        space)

private theorem p286TemporalGaugeOneForm_wedge_reads_spatial123
    (coordinate : P286CoordinateCarrier)
    (threeForm : P286GaugeThreeForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient
        (p286TemporalGaugeOneForm coordinate) threeForm =
      p286CoordinateLiePairing coordinate (threeForm 3) := by
  classical
  unfold p286GaugeOneFormThreeFormWedgeCoefficient
    p286TemporalGaugeOneForm canonicalLorentzianTimeDirection
    oneWedgeThreeSign missingTripleOfOneForm
  simp [Fin.sum_univ_four]

private theorem formNativeChargedGaugeFirstCoefficient_eq_currentSectors
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm)
    (point : BasePoint) :
    formNativeChargedGaugeFirstCoefficient Source 0 point
        (toContinuumPointField configuration point) direction =
      p286ScalarCurrentCoefficient Source configuration direction point +
        p286MatterCurrentCoefficient Source configuration direction point := by
  unfold formNativeChargedGaugeFirstCoefficient
    p286ScalarCurrentCoefficient p286MatterCurrentCoefficient
  rw [pointwiseScalarP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point,
    pointwiseMatterP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point]
  rw [mul_add]

private theorem p286Euler_spatial123_coordinate_eq_sectors
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (component : P286CoordinateCarrier) :
    p286CoordinateLiePairing component
        ((holonomicFormNativeP286GaugeEulerThreeForm Source 0 configuration
          point) 3) =
      p286CoordinateLiePairing component
          ((holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
            configuration point) 3) +
        p286ScalarCurrentCoefficient Source configuration
          (p286TemporalGaugeOneForm component) point +
        p286MatterCurrentCoefficient Source configuration
          (p286TemporalGaugeOneForm component) point := by
  rw [← p286TemporalGaugeOneForm_wedge_reads_spatial123]
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
    formNativeChargedGaugeThreeForm_evaluation,
    formNativeChargedGaugeFirstCoefficient_eq_currentSectors,
    p286TemporalGaugeOneForm_wedge_reads_spatial123]
  ring

private theorem horizontal_exterior_eq_u6
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        fixedP506L0U6ConnectionRelativeScalarActual point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative U6 point := by
  unfold fixedP506L0U6ConnectionRelativeScalarActual
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [p286ConnectionRelativeScalarCauchyDevelopmentOperator_gaugeConnection,
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_gaugeAuxiliary]

private theorem p286MatterCurrentCoefficient_eq_of_primitiveFields
    (first second : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm)
    (point : BasePoint)
    (coframeEq : first.coframe point = second.coframe point)
    (matterEq : first.matter point = second.matter point)
    (conjugateMatterEq :
      first.conjugateMatter point = second.conjugateMatter point) :
    p286MatterCurrentCoefficient Source first direction point =
      p286MatterCurrentCoefficient Source second direction point := by
  unfold p286MatterCurrentCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
    holonomicMatterGaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [coframeEq, matterEq, conjugateMatterEq]

private theorem horizontal_matterCurrent_eq_u6
    (direction : P286GaugeOneForm)
    (point : BasePoint) :
    p286MatterCurrentCoefficient Source
        fixedP506L0U6ConnectionRelativeScalarActual direction point =
      p286MatterCurrentCoefficient Source U6 direction point := by
  unfold fixedP506L0U6ConnectionRelativeScalarActual
  apply p286MatterCurrentCoefficient_eq_of_primitiveFields
  · exact congrFun
      (p286ConnectionRelativeScalarCauchyDevelopmentOperator_coframe U6) point
  · exact congrFun
      (p286ConnectionRelativeScalarCauchyDevelopmentOperator_matter U6) point
  · exact congrFun
      (p286ConnectionRelativeScalarCauchyDevelopmentOperator_conjugateMatter U6)
      point

/-- Positive read-after-write diagnostic at the original U6 counterexample:
the old `7/36` total read is exactly its scalar contribution; the horizontal
realization removes that contribution while preserving the exterior and
matter sectors. -/
theorem
    fixedP506L0U6ConnectionRelativeScalarActual_p286_zeroSlice_e0_spatial123_hypercharge_eq_zero :
    p286CoordinateLiePairing hyperchargeCoordinate
        ((diracDualFormNativePointwiseJointResidual Source
          fixedP506L0U6ConnectionRelativeScalarActual
          (canonicalCauchySlicePoint 0 SpatialE0)).p286GaugeConnection 3) =
      0 := by
  have oldTotal :=
    StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286ZeroSliceObstruction.fixedP506L0_U6_p286_zeroSlice_e0_spatial123_hypercharge_eq
  change
    p286CoordinateLiePairing hyperchargeCoordinate
        ((holonomicFormNativeP286GaugeEulerThreeForm Source 0
          fixedP506L0U6ConnectionRelativeScalarActual
          (canonicalCauchySlicePoint 0 SpatialE0)) 3) = 0
  rw [p286Euler_spatial123_coordinate_eq_sectors,
    horizontal_exterior_eq_u6,
    fixedP506L0U6ConnectionRelativeScalarActual_scalarCurrent_temporal_zeroSlice,
    horizontal_matterCurrent_eq_u6]
  change
    p286CoordinateLiePairing hyperchargeCoordinate
          ((holonomicFormNativeP286GaugeEulerThreeForm Source 0 U6
            (canonicalCauchySlicePoint 0 SpatialE0)) 3) =
        7 / 36 at oldTotal
  rw [p286Euler_spatial123_coordinate_eq_sectors,
    u6_temporalHypercharge_scalarCurrent_e0] at oldTotal
  linarith

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6ConnectionRelativeScalarSettlement
