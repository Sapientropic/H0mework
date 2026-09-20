import H0mework.Physics.FullOccurrence.FixedWriterPreECCongruence
import H0mework.Physics.FullOccurrence.FixedP286ZeroSliceObstruction
import H0mework.Physics.GaugeAction.P286RadialQuarticActionPrincipal
import H0mework.Physics.GaugeAction.P286SpatialVolumeTemporalActionDuality

/-!
# Fixed U6 occurrence P286 zero-slice action profile

The fixed P506/L0 source and the actual U6 mother-action fields make the
zero-write P286 Euler three-form radial-quadratic on the complete zero slice.
The proof is whole-carrier: the canonical exterior and matter terms are
constant, the scalar current is radial-quadratic, and their constant part is
cancelled by the already generated origin action equation.

This module uses only the fixed source/current action fields.  No residual
coordinate, support witness, target profile, branch, or free coefficient is
fed into the construction.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile

open ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction
open StageNineConnectionSectorSourceBalance
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointP286CanonicalOccurrenceWriteProfile
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286ZeroSliceObstruction
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionConstitutivePhysicalClosure
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveDifferentialSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveFirstJet
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveZeroFiber
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalWriterPreECCongruence
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286RadialQuarticActionPrincipal
open StageNineP286SpatialVolumeTemporalActionDuality
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceGeneratedHolonomicChartAction
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDuality
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance occurrenceRadialP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

private def SpatialE0 : StageNineSpatialPoint :=
  EuclideanSpace.single 0 1

private def spatialRadiusSquared (space : StageNineSpatialPoint) : ℝ :=
  ∑ axis : Fin 3, (space axis) ^ 2

private theorem spatialRadiusSquared_eq_globalActionRadius
    (space : StageNineSpatialPoint) :
    spatialRadiusSquared space =
      p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) := by
  simp [spatialRadiusSquared, p286SpatialRadiusSquared,
    p286SpatialMetricCovectorOperator, canonicalCauchySlicePoint,
    p286BaseCoordinate_apply, Fin.sum_univ_three]
  ring

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source FixedInput

private abbrev Constitutive : StageNineHolonomicConfiguration :=
  FixedP506FormNativeConstitutiveJointActionSuccessor

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev Canonical : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev Charge : P286CoordinateCarrier :=
  positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge

private theorem scalarCoordinatePairingRe_zero_left_local
    (second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe 0 second = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem scalarCoordinatePairingRe_zero_right_local
    (first : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first 0 = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem scalarCoordinatePairingRe_comm_local
    (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first second =
      scalarCoordinatePairingRe second first := by
  unfold scalarCoordinatePairingRe
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.mul_re, mul_comm]

private theorem canonical_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
      (0 : BasePoint) := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem fixedSolvedConnection_zeroSlice_time_radial
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeJointActionSolvedConnectionNormalForm
        (canonicalCauchySlicePoint 0 space) 0 =
      (spatialRadiusSquared space / 12 : ℝ) • Charge := by
  have line :=
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line
      (-(canonicalCauchySlicePoint 0 space)) 0
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm]
      at line
  have couplingValue : c3h181StrongCouplingSquared = 1 / 2 := by
    change positiveSmoothUnifiedSource.legacy.sigma = (1 / 2 : ℝ)
    exact
      StageNinePositiveSourceGravityMouthResidualTransportIteration.positiveSmoothUnifiedSource_legacy_sigma_eq_half
  unfold fixedP506FormNativeJointActionSolvedConnectionNormalForm
  simp only [Pi.neg_apply, line]
  unfold c3h181FullConnectionCoefficient
  rw [couplingValue]
  simp [spatialRadiusSquared, canonicalCauchySlicePoint,
    canonicalLorentzianTimeDirection, Fin.sum_univ_three]
  ring

private theorem fixedSolvedConnection_zeroSlice_spatial
    (space : StageNineSpatialPoint) (axis : Fin 3) :
    fixedP506FormNativeJointActionSolvedConnectionNormalForm
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
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

private theorem constitutive_connectionCoordinate_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeConnectionCoordinate Constitutive
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeJointActionSolvedConnectionNormalForm
        (canonicalCauchySlicePoint 0 space) := by
  have connectionEquality :
      Constitutive.gaugeConnection = FixedInput.gaugeConnection := by
    simpa only [Constitutive, FixedInput] using
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection
  calc
    _ = holonomicP286GaugeConnectionCoordinate FixedInput
          (canonicalCauchySlicePoint 0 space) := by
      unfold holonomicP286GaugeConnectionCoordinate
      rw [connectionEquality]
    _ = _ :=
      fixedP506FormNativeJointActionSolvedSuccessor_connection_normalForm
        (canonicalCauchySlicePoint 0 space)

private theorem constitutive_auxiliary_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate Constitutive
        (canonicalCauchySlicePoint 0 space) =
      c3h181FullAuxiliaryCoordinateNormalForm
        (-(canonicalCauchySlicePoint 0 space)) := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryCoordinate,
    fixedP506FormNativeConstitutiveAuxiliaryCoordinate_zeroSlice]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_auxiliaryCoordinate_normalForm
      _

private theorem solved_connection_zeroSlice_line
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fixedP506FormNativeJointActionSolvedConnectionNormalForm
        (canonicalCauchySlicePoint 0 space) direction =
      (-c3h181FullConnectionCoefficient
          (-(canonicalCauchySlicePoint 0 space)) direction) • Charge := by
  have line :=
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line
      (-(canonicalCauchySlicePoint 0 space)) direction
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm]
      at line
  unfold fixedP506FormNativeJointActionSolvedConnectionNormalForm
  simp only [Pi.neg_apply, line, neg_smul]

private theorem charge_bracket_neg_smul_self_zero
    (coefficient : ℝ) :
    p286CoordinateLieBracket Charge (-(coefficient • Charge)) = 0 := by
  rw [← neg_smul, p286CoordinateLieBracket_smul_right,
    p286CoordinateLieBracket_self, smul_zero]

private theorem constitutive_connectionExteriorAction_zeroSlice
    (space : StageNineSpatialPoint) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate Constitutive
          (canonicalCauchySlicePoint 0 space))
        (holonomicP286GaugeAuxiliaryCoordinate Constitutive
          (canonicalCauchySlicePoint 0 space)) = 0 := by
  rw [constitutive_connectionCoordinate_zeroSlice,
    constitutive_auxiliary_zeroSlice]
  unfold pointwiseP286GaugeTwoFormConnectionExteriorAction
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormCovariantDerivative
    p286GaugeTwoFormAdjoint
  funext triple
  fin_cases triple <;>
    simp_rw [solved_connection_zeroSlice_line]
  all_goals
    simp [c3h181FullAuxiliaryCoordinateNormalForm,
      c3h181FullConnectionCoefficient,
      canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six,
      p286CoordinateLieBracket_smul_left,
      p286CoordinateLieBracket_smul_right,
      charge_bracket_neg_smul_self_zero,
      p286CoordinateLieBracket_self]

private theorem constitutive_exteriorCovariantDerivative_zeroSlice_eq_origin
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Constitutive
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Constitutive 0 := by
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    constitutive_connectionExteriorAction_zeroSlice]
  have originActionZero :
      pointwiseP286GaugeTwoFormConnectionExteriorAction
          (holonomicP286GaugeConnectionCoordinate Constitutive 0)
          (holonomicP286GaugeAuxiliaryCoordinate Constitutive 0) = 0 := by
    simpa [canonical_zero] using
      constitutive_connectionExteriorAction_zeroSlice
        (0 : StageNineSpatialPoint)
  rw [originActionZero, add_zero, add_zero]
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  congr 1
  funext direction
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryDirectionalDerivative_zeroSlice]
  exact
    (fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryDirectionalDerivative
      direction).symm

private theorem fixedCanonicalConnectionCandidate_zero_local :
    fixedP506L0P286CanonicalConnectionCandidate 0 =
      fixedP506L0P286CanonicalActionInput := by
  simpa [fixedP506L0P286CanonicalConnectionCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate] using
    (diracDualFormNativeP286CanonicalConnectionCandidate_zero
      fixedP506L0P286CanonicalActionInput)

private theorem fixedCanonicalGeneratedWrite_zero_local :
    fixedP506L0P286CanonicalGeneratedWrite = 0 := by
  simpa only using fixedP506L0P286CanonicalGeneratedWrite_zero

private theorem canonical_gaugeConnection_eq_constitutive :
    Canonical.gaugeConnection = Constitutive.gaugeConnection := by
  change
    (fixedP506L0P286CanonicalJointCandidate
      fixedP506L0P286CanonicalGeneratedWrite).gaugeConnection = _
  rw [fixedCanonicalGeneratedWrite_zero_local,
    fixedP506L0P286CanonicalJointCandidate_gaugeConnection,
    fixedCanonicalConnectionCandidate_zero_local,
    fixedP506L0FinalCommonActionActual_gaugeConnection_eq_constitutive]

private theorem canonical_gaugeAuxiliary_eq_constitutive :
    Canonical.gaugeAuxiliary = Constitutive.gaugeAuxiliary := by
  funext point
  rw [fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliary,
    fixedCanonicalGeneratedWrite_zero_local,
    fixedCanonicalConnectionCandidate_zero_local]
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeAuxiliary]
  unfold fixedP506FormNativeConstitutiveAuxiliaryField
  rw [fixedP506L0FinalCommonActionActual_coframe_eq_solved]
  rw [holonomicGaugeCurvature_eq_of_connection_eq_current
    fixedP506L0P286CanonicalActionInput FixedInput
    fixedP506L0FinalCommonActionActual_gaugeConnection_eq_solved point]

private theorem canonical_exterior_eq_constitutive :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Constitutive := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [canonical_gaugeConnection_eq_constitutive,
    canonical_gaugeAuxiliary_eq_constitutive]

private theorem canonical_exterior_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical
        (canonicalCauchySlicePoint 0 SpatialE0) := by
  rw [congrFun canonical_exterior_eq_constitutive
      (canonicalCauchySlicePoint 0 space),
    congrFun canonical_exterior_eq_constitutive
      (canonicalCauchySlicePoint 0 SpatialE0),
    constitutive_exteriorCovariantDerivative_zeroSlice_eq_origin space,
    constitutive_exteriorCovariantDerivative_zeroSlice_eq_origin SpatialE0]

private theorem constitutive_scalar_vacuum :
    Constitutive.scalar =
      fun _ => sourceGeneratedVacuumCoordinates Source := by
  rw [show Constitutive.scalar = FixedInput.scalar by
      exact fixedP506FormNativeConstitutiveJointActionSuccessor_scalar]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar, fixedP506JointActual_scalar_vacuum]

private theorem constitutive_gaugeConnection_zeroSlice_radial
    (space : StageNineSpatialPoint) :
    Constitutive.gaugeConnection (canonicalCauchySlicePoint 0 space) =
      spatialRadiusSquared space •
        Constitutive.gaugeConnection
          (canonicalCauchySlicePoint 0 SpatialE0) := by
  funext direction
  apply p286CoordinateEquiv.injective
  simp only [Pi.smul_apply, map_smul]
  have coordinateSpace := congrFun
    (constitutive_connectionCoordinate_zeroSlice space) direction
  have coordinateE0 := congrFun
    (constitutive_connectionCoordinate_zeroSlice SpatialE0) direction
  unfold holonomicP286GaugeConnectionCoordinate at coordinateSpace coordinateE0
  change
    p286CoordinateEquiv
        (Constitutive.gaugeConnection
          (canonicalCauchySlicePoint 0 space) direction) =
      spatialRadiusSquared space •
        p286CoordinateEquiv
          (Constitutive.gaugeConnection
            (canonicalCauchySlicePoint 0 SpatialE0) direction)
  rw [coordinateSpace, coordinateE0]
  by_cases h : direction = 0
  · subst direction
    rw [fixedSolvedConnection_zeroSlice_time_radial,
      fixedSolvedConnection_zeroSlice_time_radial]
    have e0Radius : spatialRadiusSquared SpatialE0 = 1 := by
      simp [spatialRadiusSquared, SpatialE0]
    rw [e0Radius]
    module
  · have directionEq : (direction.pred h).succ = direction :=
      Fin.succ_pred direction h
    rw [← directionEq,
      fixedSolvedConnection_zeroSlice_spatial,
      fixedSolvedConnection_zeroSlice_spatial]
    simp

private theorem constitutive_scalarCovariantDerivative_zeroSlice_radial
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative Constitutive
        (canonicalCauchySlicePoint 0 space) =
      spatialRadiusSquared space •
        holonomicScalarCovariantDerivative Constitutive
          (canonicalCauchySlicePoint 0 SpatialE0) := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [constitutive_scalar_vacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add, Pi.smul_apply]
  rw [congrFun (constitutive_gaugeConnection_zeroSlice_radial space)
    direction]
  simp only [Pi.smul_apply, p286LieBlockEmbed_real_smul,
    scalarMotherLieAction_real_smul]

private theorem constitutive_scalarVariation_zeroSlice_constant
    (space : StageNineSpatialPoint) (direction : P286GaugeOneForm) :
    holonomicScalarGaugeConnectionVariation Constitutive
        (fun _ => direction) (canonicalCauchySlicePoint 0 space) =
      holonomicScalarGaugeConnectionVariation Constitutive
        (fun _ => direction) (canonicalCauchySlicePoint 0 SpatialE0) := by
  funext derivativeDirection
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  rw [constitutive_scalar_vacuum]

private theorem constitutive_scalarCurrent_zeroSlice_radial
    (space : StageNineSpatialPoint) (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient Source Constitutive direction
        (canonicalCauchySlicePoint 0 space) =
      spatialRadiusSquared space *
        p286ScalarCurrentCoefficient Source Constitutive direction
          (canonicalCauchySlicePoint 0 SpatialE0) := by
  unfold p286ScalarCurrentCoefficient
  rw [constitutive_scalarVariation_zeroSlice_constant]
  simp only [toContinuumPointField]
  rw [constitutive_scalarCovariantDerivative_zeroSlice_radial]
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice,
    fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice]
  simp only [generatedVolumeDensity, Matrix.det_one, abs_one, one_mul]
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [scalarFrameRelativeCoordinates_zeroChart, Pi.smul_apply,
    scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right, Fin.sum_univ_four]
  ring

private theorem constitutive_scalarCovariantDerivative_e0_normalForm :
    holonomicScalarCovariantDerivative Constitutive
        (canonicalCauchySlicePoint 0 SpatialE0) =
      fun direction =>
        if direction = 0 then
          (1 / 12 : ℝ) •
            scalarP286ActionBilinear Charge
              (sourceGeneratedVacuumCoordinates Source)
        else 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [constitutive_scalar_vacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add]
  have coordinateEq := congrFun
    (constitutive_connectionCoordinate_zeroSlice SpatialE0) direction
  unfold holonomicP286GaugeConnectionCoordinate at coordinateEq
  have rawEq := congrArg p286CoordinateEquiv.symm coordinateEq
  simp only [p286CoordinateEquiv.symm_apply_apply] at rawEq
  rw [rawEq]
  change
    scalarP286ActionBilinear
        (fixedP506FormNativeJointActionSolvedConnectionNormalForm
          (canonicalCauchySlicePoint 0 SpatialE0) direction)
        (sourceGeneratedVacuumCoordinates Source) = _
  by_cases h : direction = 0
  · subst direction
    rw [fixedSolvedConnection_zeroSlice_time_radial]
    simp [spatialRadiusSquared, SpatialE0]
  · have directionEq : (direction.pred h).succ = direction :=
      Fin.succ_pred direction h
    rw [← directionEq,
      fixedSolvedConnection_zeroSlice_spatial SpatialE0]
    simp [h]

private theorem constitutive_spatialScalarVariation_e0
    (axis : Fin 3) (coordinate : P286CoordinateCarrier) :
    holonomicScalarGaugeConnectionVariation Constitutive
        (fun _ => singleP286GaugeOneForm axis.succ coordinate)
        (canonicalCauchySlicePoint 0 SpatialE0) =
      fun direction =>
        if direction = axis.succ then
          scalarP286ActionBilinear coordinate
            (sourceGeneratedVacuumCoordinates Source)
        else 0 := by
  funext direction
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  rw [constitutive_scalar_vacuum]
  change
    scalarP286ActionBilinear
        (singleP286GaugeOneForm axis.succ coordinate direction)
        (sourceGeneratedVacuumCoordinates Source) = _
  classical
  by_cases h : direction = axis.succ <;>
    simp [singleP286GaugeOneForm, h]

private theorem constitutive_spatialScalarCurrent_e0_zero
    (axis : Fin 3) (coordinate : P286CoordinateCarrier) :
    p286ScalarCurrentCoefficient Source Constitutive
        (singleP286GaugeOneForm axis.succ coordinate)
        (canonicalCauchySlicePoint 0 SpatialE0) = 0 := by
  unfold p286ScalarCurrentCoefficient
  rw [constitutive_spatialScalarVariation_e0]
  simp only [toContinuumPointField]
  rw [constitutive_scalarCovariantDerivative_e0_normalForm,
    fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice]
  simp only [generatedVolumeDensity, Matrix.det_one, abs_one, one_mul]
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [scalarFrameRelativeCoordinates_zeroChart]
  rw [
    StageNinePositiveSourceNativeGravityCurvatureBridge.lorentzianMetricOfCoframe_one_inv]
  fin_cases axis <;>
    simp [Fin.sum_univ_four, minkowskiInternalMetric, Matrix.diagonal_apply,
      scalarCoordinatePairingRe_zero_left_local,
      scalarCoordinatePairingRe_zero_right_local]

private theorem temporal_scalar_firstJet_zeroSlice
    (space : StageNineSpatialPoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative Temporal.scalar
        (canonicalCauchySlicePoint 0 space) direction =
      fieldDirectionalDerivative FixedInput.scalar
        (canonicalCauchySlicePoint 0 space) direction := by
  have currentDifferentiable :
      DifferentiableAt ℝ FixedInput.scalar
        (canonicalCauchySlicePoint 0 space) :=
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
      ).differentiable (by simp) |>.differentiableAt
  by_cases generatedDifferentiable :
      DifferentiableAt ℝ Temporal.scalar
        (canonicalCauchySlicePoint 0 space)
  · have generated :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_firstJet_zeroSlice
        Source FixedInput space currentDifferentiable
        (by simpa [Temporal, completeJointGlobalTemporalCurrent] using
          generatedDifferentiable) direction
    simpa [Temporal, completeJointGlobalTemporalCurrent] using generated
  · have generatedDerivativeZero :
        fieldDirectionalDerivative Temporal.scalar
            (canonicalCauchySlicePoint 0 space) direction = 0 := by
      unfold fieldDirectionalDerivative
      rw [fderiv_zero_of_not_differentiableAt generatedDifferentiable]
      rfl
    have currentDerivativeZero :
        fieldDirectionalDerivative FixedInput.scalar
            (canonicalCauchySlicePoint 0 space) direction = 0 := by
      rw [← fixedP506FormNativeConstitutiveJointActionSuccessor_scalar,
        constitutive_scalar_vacuum]
      simp [fieldDirectionalDerivative]
    rw [generatedDerivativeZero, currentDerivativeZero]

private theorem temporal_scalarCovariantDerivative_zeroSlice_eq_constitutive
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative Temporal
        (canonicalCauchySlicePoint 0 space) =
      holonomicScalarCovariantDerivative Constitutive
        (canonicalCauchySlicePoint 0 space) := by
  funext direction
  calc
    holonomicScalarCovariantDerivative Temporal
          (canonicalCauchySlicePoint 0 space) direction =
        holonomicScalarCovariantDerivative FixedInput
          (canonicalCauchySlicePoint 0 space) direction := by
      unfold holonomicScalarCovariantDerivative
      rw [temporal_scalar_firstJet_zeroSlice space direction]
      have scalarPointEq :
          Temporal.scalar (canonicalCauchySlicePoint 0 space) =
            FixedInput.scalar (canonicalCauchySlicePoint 0 space) := by
        exact
          sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
            Source FixedInput space
      rw [scalarPointEq]
      rfl
    _ = holonomicScalarCovariantDerivative Constitutive
          (canonicalCauchySlicePoint 0 space) direction := by
      unfold holonomicScalarCovariantDerivative
      rw [fixedP506FormNativeConstitutiveJointActionSuccessor_scalar,
        fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]

private theorem p286ScalarCurrentCoefficient_eq_of_contacts
    (first second : StageNineHolonomicConfiguration)
    (point secondPoint : BasePoint)
    (coframeEq : first.coframe point = second.coframe secondPoint)
    (scalarEq : first.scalar point = second.scalar secondPoint)
    (covariantDerivativeEq :
      holonomicScalarCovariantDerivative first point =
        holonomicScalarCovariantDerivative second secondPoint)
    (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient Source first direction point =
      p286ScalarCurrentCoefficient Source second direction secondPoint := by
  unfold p286ScalarCurrentCoefficient generatedVolumeDensity
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
    holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]
  rw [coframeEq, scalarEq, covariantDerivativeEq]

private theorem temporal_scalarCurrent_zeroSlice_eq_constitutive
    (space : StageNineSpatialPoint) (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient Source Temporal direction
        (canonicalCauchySlicePoint 0 space) =
      p286ScalarCurrentCoefficient Source Constitutive direction
        (canonicalCauchySlicePoint 0 space) := by
  apply p286ScalarCurrentCoefficient_eq_of_contacts
  · calc
      Temporal.coframe (canonicalCauchySlicePoint 0 space) =
          FixedInput.coframe (canonicalCauchySlicePoint 0 space) := by rfl
      _ = Constitutive.coframe (canonicalCauchySlicePoint 0 space) :=
        (congrFun
          fixedP506FormNativeConstitutiveJointActionSuccessor_coframe _).symm
  · calc
      Temporal.scalar (canonicalCauchySlicePoint 0 space) =
          FixedInput.scalar (canonicalCauchySlicePoint 0 space) :=
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
          Source FixedInput space
      _ = Constitutive.scalar (canonicalCauchySlicePoint 0 space) :=
        (congrFun
          fixedP506FormNativeConstitutiveJointActionSuccessor_scalar _).symm
  · exact temporal_scalarCovariantDerivative_zeroSlice_eq_constitutive space

private theorem temporal_scalarCurrent_zeroSlice_radial
    (space : StageNineSpatialPoint) (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient Source Temporal direction
        (canonicalCauchySlicePoint 0 space) =
      spatialRadiusSquared space *
        p286ScalarCurrentCoefficient Source Temporal direction
          (canonicalCauchySlicePoint 0 SpatialE0) := by
  rw [temporal_scalarCurrent_zeroSlice_eq_constitutive,
    constitutive_scalarCurrent_zeroSlice_radial,
    temporal_scalarCurrent_zeroSlice_eq_constitutive]

private theorem temporal_spatialScalarCurrent_e0_zero
    (axis : Fin 3) (coordinate : P286CoordinateCarrier) :
    p286ScalarCurrentCoefficient Source Temporal
        (singleP286GaugeOneForm axis.succ coordinate)
        (canonicalCauchySlicePoint 0 SpatialE0) = 0 := by
  rw [temporal_scalarCurrent_zeroSlice_eq_constitutive]
  exact constitutive_spatialScalarCurrent_e0_zero axis coordinate

private theorem primitive_matter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  have diagonalZeroSlice := congrArg
    (fun state : StageNineCauchyState => state.matter space)
    fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.matter
        (canonicalCauchySlicePoint 0 space) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.matter
        space at diagonalZeroSlice
  rw [diagonalZeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      Source positiveP506MatterCurrentFullSynchronizedCauchyState space
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      Source positiveP506MatterCurrentFullSynchronizedCauchyState).matter space =
      diracSpinTwoMatterProbe
  rw [reads.2.2.2.2.2.2.2.2.1]
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
  exact fixedCartanReactionContact_matter_origin space

private theorem primitive_conjugateMatter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinZeroMatterCoordinate := by
  have diagonalZeroSlice := congrArg
    (fun state : StageNineCauchyState => state.conjugateMatter space)
    fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.conjugateMatter
        space at diagonalZeroSlice
  rw [diagonalZeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      Source positiveP506MatterCurrentFullSynchronizedCauchyState space
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      Source positiveP506MatterCurrentFullSynchronizedCauchyState).conjugateMatter
        space = diracSpinZeroMatterCoordinate
  rw [reads.2.2.2.2.2.2.2.2.2]
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
  exact fixedCartanReactionContact_conjugateMatter_origin space

private theorem constitutive_matter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    Constitutive.matter (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_matter_zeroSlice,
    primitive_matter_zeroSlice_constant]

private theorem constitutive_conjugateMatter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    Constitutive.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      diracSpinZeroMatterCoordinate := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter_zeroSlice,
    primitive_conjugateMatter_zeroSlice_constant]

private theorem p286MatterCurrentCoefficient_eq_of_contacts
    (first second : StageNineHolonomicConfiguration)
    (point secondPoint : BasePoint)
    (coframeEq : first.coframe point = second.coframe secondPoint)
    (matterEq : first.matter point = second.matter secondPoint)
    (conjugateEq :
      first.conjugateMatter point = second.conjugateMatter secondPoint)
    (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient Source first direction point =
      p286MatterCurrentCoefficient Source second direction secondPoint := by
  unfold p286MatterCurrentCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
    holonomicMatterGaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [coframeEq, matterEq, conjugateEq]
  simp only [matterDualFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart,
    p286GaugeConnectionMotherVariation]

private theorem temporal_matterCurrent_zeroSlice_eq_constitutive
    (space : StageNineSpatialPoint) (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient Source Temporal direction
        (canonicalCauchySlicePoint 0 space) =
      p286MatterCurrentCoefficient Source Constitutive direction
        (canonicalCauchySlicePoint 0 space) := by
  apply p286MatterCurrentCoefficient_eq_of_contacts
  · calc
      Temporal.coframe (canonicalCauchySlicePoint 0 space) =
          FixedInput.coframe (canonicalCauchySlicePoint 0 space) := by rfl
      _ = Constitutive.coframe (canonicalCauchySlicePoint 0 space) :=
        (congrFun
          fixedP506FormNativeConstitutiveJointActionSuccessor_coframe _).symm
  · calc
      Temporal.matter (canonicalCauchySlicePoint 0 space) =
          FixedInput.matter (canonicalCauchySlicePoint 0 space) :=
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
          Source FixedInput space
      _ = Constitutive.matter (canonicalCauchySlicePoint 0 space) :=
        (congrFun
          fixedP506FormNativeConstitutiveJointActionSuccessor_matter _).symm
  · calc
      Temporal.conjugateMatter (canonicalCauchySlicePoint 0 space) =
          FixedInput.conjugateMatter (canonicalCauchySlicePoint 0 space) :=
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
          Source FixedInput space
      _ = Constitutive.conjugateMatter
            (canonicalCauchySlicePoint 0 space) :=
        (congrFun
          fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter
          _).symm

private theorem temporal_matterCurrent_zeroSlice_constant
    (space : StageNineSpatialPoint) (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient Source Temporal direction
        (canonicalCauchySlicePoint 0 space) =
      p286MatterCurrentCoefficient Source Temporal direction
        (canonicalCauchySlicePoint 0 SpatialE0) := by
  calc
    _ = p286MatterCurrentCoefficient Source Constitutive direction
          (canonicalCauchySlicePoint 0 space) :=
      temporal_matterCurrent_zeroSlice_eq_constitutive space direction
    _ = p286MatterCurrentCoefficient Source Constitutive direction
          (canonicalCauchySlicePoint 0 SpatialE0) := by
      apply p286MatterCurrentCoefficient_eq_of_contacts
      · rw [fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice,
          fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice]
      · rw [constitutive_matter_zeroSlice_constant,
          constitutive_matter_zeroSlice_constant]
      · rw [constitutive_conjugateMatter_zeroSlice_constant,
          constitutive_conjugateMatter_zeroSlice_constant]
    _ = p286MatterCurrentCoefficient Source Temporal direction
          (canonicalCauchySlicePoint 0 SpatialE0) :=
      (temporal_matterCurrent_zeroSlice_eq_constitutive
        SpatialE0 direction).symm

private theorem formNativeChargedGaugeFirstCoefficient_eq_currentSectors_local
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) :
    (fun point =>
      formNativeChargedGaugeFirstCoefficient Source 0 point
        (toContinuumPointField configuration point) direction) =
      p286ScalarCurrentCoefficient Source configuration direction +
        p286MatterCurrentCoefficient Source configuration direction := by
  funext point
  unfold formNativeChargedGaugeFirstCoefficient
    p286ScalarCurrentCoefficient p286MatterCurrentCoefficient
  rw [pointwiseScalarP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point,
    pointwiseMatterP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point]
  rw [mul_add]
  rfl

private theorem canonical_exterior_origin_eq_e0 :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical 0 =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical
        (canonicalCauchySlicePoint 0 SpatialE0) := by
  simpa [canonical_zero] using
    canonical_exterior_zeroSlice_constant (0 : StageNineSpatialPoint)

private theorem temporal_scalarCurrent_origin_zero
    (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient Source Temporal direction 0 = 0 := by
  have radial :=
    temporal_scalarCurrent_zeroSlice_radial
      (0 : StageNineSpatialPoint) direction
  simpa [canonical_zero, spatialRadiusSquared] using radial

private theorem temporal_matterCurrent_origin_eq_e0
    (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient Source Temporal direction 0 =
      p286MatterCurrentCoefficient Source Temporal direction
        (canonicalCauchySlicePoint 0 SpatialE0) := by
  simpa [canonical_zero] using
    temporal_matterCurrent_zeroSlice_constant
      (0 : StageNineSpatialPoint) direction

private theorem canonicalExterior_add_temporalMatterCurrent_e0_zero
    (direction : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical
          (canonicalCauchySlicePoint 0 SpatialE0)) +
      p286MatterCurrentCoefficient Source Temporal direction
        (canonicalCauchySlicePoint 0 SpatialE0) = 0 := by
  have originSupport :=
    fixedP506L0_Algebraic_p286Euler_zeroSlice_support
      (0 : StageNineSpatialPoint)
  rw [canonical_zero] at originSupport
  have originEuler := congrArg
    (fun form =>
      p286GaugeOneFormThreeFormWedgeCoefficient direction form)
    fixedP506L0_Algebraic_p286Euler_origin_zero
  rw [originSupport,
    p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
    formNativeChargedGaugeThreeForm_evaluation,
    congrFun
      (formNativeChargedGaugeFirstCoefficient_eq_currentSectors_local
        Temporal direction) 0] at originEuler
  simp only [Pi.add_apply] at originEuler
  change
    p286GaugeOneFormThreeFormWedgeCoefficient direction
          (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical 0) +
        (p286ScalarCurrentCoefficient Source Temporal direction 0 +
          p286MatterCurrentCoefficient Source Temporal direction 0) =
      p286GaugeOneFormThreeFormWedgeCoefficient direction 0 at originEuler
  rw [
    temporal_scalarCurrent_origin_zero,
    zero_add,
    canonical_exterior_origin_eq_e0,
    temporal_matterCurrent_origin_eq_e0] at originEuler
  simpa [p286GaugeOneFormThreeFormWedgeCoefficient] using originEuler

private theorem algebraicEuler_e0_wedge_eq_temporalScalarCurrent
    (direction : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (canonicalCauchySlicePoint 0 SpatialE0)) =
      p286ScalarCurrentCoefficient Source Temporal direction
        (canonicalCauchySlicePoint 0 SpatialE0) := by
  rw [fixedP506L0_Algebraic_p286Euler_zeroSlice_support,
    p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
    formNativeChargedGaugeThreeForm_evaluation,
    congrFun
      (formNativeChargedGaugeFirstCoefficient_eq_currentSectors_local
        Temporal direction) (canonicalCauchySlicePoint 0 SpatialE0),
    Pi.add_apply]
  have cancellation :=
    canonicalExterior_add_temporalMatterCurrent_e0_zero direction
  linear_combination cancellation

private abbrev AlgebraicEulerE0 : P286GaugeThreeForm :=
  holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
    (canonicalCauchySlicePoint 0 SpatialE0)

/-- Internal charge read from the distinguished component of the fixed
mother-action Euler three-form.  It is an action output, not a source slot or
a residual-supplied coefficient. -/
def fixedP506L0U6OccurrenceP286MotherActionCharge :
    P286CoordinateCarrier :=
  AlgebraicEulerE0 3

/-- The distinguished mother-action charge is the faithful P286 Riesz read
of the temporal scalar current at the same `e0` occurrence.  This exposes the
action provenance of the charge without storing a current, residual, or
target coordinate in its constructor. -/
theorem fixedP506L0U6OccurrenceP286MotherActionCharge_pairing_eq_temporalScalarCurrent
    (coordinate : P286CoordinateCarrier) :
    p286CoordinateLiePairing coordinate
        fixedP506L0U6OccurrenceP286MotherActionCharge =
      p286ScalarCurrentCoefficient Source Temporal
        (p286TemporalGaugeOneForm coordinate)
        (canonicalCauchySlicePoint 0 SpatialE0) := by
  have actionRead :=
    algebraicEuler_e0_wedge_eq_temporalScalarCurrent
      (p286TemporalGaugeOneForm coordinate)
  simpa [fixedP506L0U6OccurrenceP286MotherActionCharge,
    p286GaugeOneFormThreeFormWedgeCoefficient,
    p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection,
    oneWedgeThreeSign, missingTripleOfOneForm, Fin.sum_univ_four] using
    actionRead

/-- Finite representation normal form of the same mother-action charge.
The right-hand side consumes the pre-existing temporal connection charge and
the source-generated vacuum; it does not accept a residual or target charge.
-/
theorem fixedP506L0U6OccurrenceP286MotherActionCharge_pairing_eq_scalarActionPairing
    (coordinate : P286CoordinateCarrier) :
    p286CoordinateLiePairing coordinate
        fixedP506L0U6OccurrenceP286MotherActionCharge =
      -(1 / 12 : ℝ) *
        scalarCoordinatePairingRe
          (scalarP286ActionBilinear coordinate
            (sourceGeneratedVacuumCoordinates Source))
          (scalarP286ActionBilinear Charge
            (sourceGeneratedVacuumCoordinates Source)) := by
  rw [fixedP506L0U6OccurrenceP286MotherActionCharge_pairing_eq_temporalScalarCurrent,
    temporal_scalarCurrent_zeroSlice_eq_constitutive]
  have scalarVariation :
      holonomicScalarGaugeConnectionVariation Constitutive
          (fun _ => p286TemporalGaugeOneForm coordinate)
          (canonicalCauchySlicePoint 0 SpatialE0) =
        fun direction =>
          if direction = 0 then
            scalarP286ActionBilinear coordinate
              (sourceGeneratedVacuumCoordinates Source)
          else 0 := by
    funext direction
    unfold holonomicScalarGaugeConnectionVariation
      p286GaugeConnectionMotherVariation
    rw [constitutive_scalar_vacuum]
    change
      scalarP286ActionBilinear
          (p286TemporalGaugeOneForm coordinate direction)
          (sourceGeneratedVacuumCoordinates Source) = _
    fin_cases direction <;>
      simp [p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection]
  unfold p286ScalarCurrentCoefficient
  rw [scalarVariation]
  simp only [toContinuumPointField]
  rw [constitutive_scalarCovariantDerivative_e0_normalForm,
    fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice]
  simp only [generatedVolumeDensity, Matrix.det_one, abs_one, one_mul]
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [scalarFrameRelativeCoordinates_zeroChart]
  rw [
    StageNinePositiveSourceNativeGravityCurvatureBridge.lorentzianMetricOfCoframe_one_inv]
  simp [Fin.sum_univ_four, minkowskiInternalMetric, Matrix.diagonal_apply,
    scalarCoordinatePairingRe_zero_right_local,
    scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  rw [scalarCoordinatePairingRe_comm_local
    (scalarP286ActionBilinear Charge
      (sourceGeneratedVacuumCoordinates Source))]
  ring

private theorem AlgebraicEulerE0_component_eq_zero_of_ne_spatialVolume
    (triple : Fin 4) (notSpatialVolume : triple ≠ 3) :
    AlgebraicEulerE0 triple = 0 := by
  let direction : LorentzianIndex := missingTripleOfOneForm triple
  have directionNeZero : direction ≠ 0 := by
    intro directionZero
    have : triple = 3 := by
      calc
        triple = missingTripleOfOneForm direction := by
          simpa [direction] using
            (missingTripleOfOneForm_involutive triple).symm
        _ = 3 := by rw [directionZero]; rfl
    exact notSpatialVolume this
  let axis : Fin 3 := direction.pred directionNeZero
  have axisSucc : axis.succ = direction :=
    Fin.succ_pred direction directionNeZero
  let component : P286CoordinateCarrier := AlgebraicEulerE0 triple
  have evaluated :=
    algebraicEuler_e0_wedge_eq_temporalScalarCurrent
      (singleP286GaugeOneForm axis.succ component)
  rw [temporal_spatialScalarCurrent_e0_zero axis component] at evaluated
  change
    p286GaugeThreeFormWedgeLinearDual AlgebraicEulerE0
        (singleP286GaugeOneForm axis.succ component) = 0 at evaluated
  rw [p286GaugeThreeFormWedgeLinearDual_single_apply] at evaluated
  have missingEq : missingTripleOfOneForm axis.succ = triple := by
    rw [axisSucc]
    simpa [direction] using missingTripleOfOneForm_involutive triple
  rw [missingEq] at evaluated
  have signNeZero : oneWedgeThreeSign axis.succ ≠ 0 :=
    oneWedgeThreeSign_ne_zero axis.succ
  have pairingZero :
      p286CoordinateLiePairing component component = 0 :=
    (mul_eq_zero.mp evaluated).resolve_left signNeZero
  exact
    (p286CoordinateLiePairing_self_eq_zero_iff component).mp pairingZero

/-- On the distinguished zero-slice occurrence the complete fixed
mother-action Euler form has exactly spatial-volume support. -/
theorem fixedP506L0_Algebraic_p286Euler_zeroSlice_e0_eq_spatialVolume :
    AlgebraicEulerE0 =
      p286SpatialVolumeGaugeThreeForm
        fixedP506L0U6OccurrenceP286MotherActionCharge := by
  funext triple
  by_cases spatialVolume : triple = 3
  · subst triple
    simp [fixedP506L0U6OccurrenceP286MotherActionCharge,
      p286SpatialVolumeGaugeThreeForm]
  · rw [AlgebraicEulerE0_component_eq_zero_of_ne_spatialVolume
      triple spatialVolume]
    classical
    simp [p286SpatialVolumeGaugeThreeForm, spatialVolume]

private theorem algebraic_eq_zeroCandidate :
    Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source Temporal 0 :=
  fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate

private theorem recentered_p286ConnectionDerivative
    (current : StageNineHolonomicConfiguration)
    (contact localPoint : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286ConnectionDerivative
        (fullyRecenterHolonomicConfiguration current contact) localPoint
        derivativeDirection formDirection =
      p286ConnectionDerivative current
        (canonicalSpacetimeContactTranslation contact localPoint)
        derivativeDirection formDirection := by
  unfold p286ConnectionDerivative
  apply congrArg p286CoordinateEquiv.symm
  change
    fieldDirectionalDerivative
        ((fun point =>
          p286CoordinateEquiv
            (current.gaugeConnection point formDirection)) ∘
          canonicalSpacetimeContactTranslation contact)
        localPoint derivativeDirection = _
  exact
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      (fun point =>
        p286CoordinateEquiv (current.gaugeConnection point formDirection))
      contact localPoint derivativeDirection

private theorem recentered_gaugeCurvature
    (current : StageNineHolonomicConfiguration)
    (contact localPoint : BasePoint) :
    holonomicGaugeCurvature
        (fullyRecenterHolonomicConfiguration current contact) localPoint =
      holonomicGaugeCurvature current
        (canonicalSpacetimeContactTranslation contact localPoint) := by
  funext pair
  unfold holonomicGaugeCurvature
  rw [recentered_p286ConnectionDerivative,
    recentered_p286ConnectionDerivative]
  rfl

/-- Recentring commutes with the fixed zero-write constitutive candidate.
This is the exact matching-contact seam used by the occurrence mother-action
forcing; it is independent of any residual read. -/
theorem fixedP506L0_recenteredTemporal_zeroWriteCandidate_eq_recenteredAlgebraic
    (contact : BasePoint) :
    diracDualFormNativeP286CanonicalJointCandidate Source
        (fullyRecenterHolonomicConfiguration Temporal contact) 0 =
      fullyRecenterHolonomicConfiguration Algebraic contact := by
  rw [diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rw [algebraic_eq_zeroCandidate,
    diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  apply StageNineHolonomicConfiguration.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext localPoint
    change
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          (sourceGeneratedUnifiedCouplings Source)
          ((fullyRecenterHolonomicConfiguration Temporal contact).coframe
            localPoint)
          (holonomicGaugeCurvature
            (fullyRecenterHolonomicConfiguration Temporal contact)
            localPoint) =
        formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          (sourceGeneratedUnifiedCouplings Source)
          (Temporal.coframe
            (canonicalSpacetimeContactTranslation contact localPoint))
          (holonomicGaugeCurvature Temporal
            (canonicalSpacetimeContactTranslation contact localPoint))
    rw [recentered_gaugeCurvature]
    rfl
  · rfl
  · rfl
  · rfl

theorem fixedP506L0_Algebraic_p286Euler_zeroSlice_radialQuadratic
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
        (canonicalCauchySlicePoint 0 space) =
      spatialRadiusSquared space •
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (canonicalCauchySlicePoint 0 SpatialE0) := by
  apply p286GaugeThreeFormWedgeDualOperator_injective
  apply LinearMap.ext
  intro direction
  change
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (canonicalCauchySlicePoint 0 space)) =
      p286GaugeOneFormThreeFormWedgeCoefficient direction
        (spatialRadiusSquared space •
          holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
            (canonicalCauchySlicePoint 0 SpatialE0))
  rw [p286GaugeOneFormThreeFormWedgeCoefficient_smul_right]
  rw [fixedP506L0_Algebraic_p286Euler_zeroSlice_support,
    fixedP506L0_Algebraic_p286Euler_zeroSlice_support,
    p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
    p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
    formNativeChargedGaugeThreeForm_evaluation,
    formNativeChargedGaugeThreeForm_evaluation,
    congrFun
      (formNativeChargedGaugeFirstCoefficient_eq_currentSectors_local
        Temporal direction) (canonicalCauchySlicePoint 0 space),
    congrFun
      (formNativeChargedGaugeFirstCoefficient_eq_currentSectors_local
        Temporal direction) (canonicalCauchySlicePoint 0 SpatialE0),
    Pi.add_apply]
  change
    p286GaugeOneFormThreeFormWedgeCoefficient direction
          (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical
            (canonicalCauchySlicePoint 0 space)) +
        (p286ScalarCurrentCoefficient Source Temporal direction
            (canonicalCauchySlicePoint 0 space) +
          p286MatterCurrentCoefficient Source Temporal direction
            (canonicalCauchySlicePoint 0 space)) =
      spatialRadiusSquared space *
        (p286GaugeOneFormThreeFormWedgeCoefficient direction
            (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical
              (canonicalCauchySlicePoint 0 SpatialE0)) +
          (p286ScalarCurrentCoefficient Source Temporal direction
              (canonicalCauchySlicePoint 0 SpatialE0) +
            p286MatterCurrentCoefficient Source Temporal direction
              (canonicalCauchySlicePoint 0 SpatialE0)))
  rw [
    canonical_exterior_zeroSlice_constant,
    temporal_scalarCurrent_zeroSlice_radial,
    temporal_matterCurrent_zeroSlice_constant]
  linear_combination
    (1 - spatialRadiusSquared space) *
      canonicalExterior_add_temporalMatterCurrent_e0_zero direction

/-- The same radial law in the global action-principal radius used by the
explicit radial-quartic whole-field producer. -/
theorem fixedP506L0_Algebraic_p286Euler_zeroSlice_eq_globalActionRadius
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
        (canonicalCauchySlicePoint 0 space) =
      p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) •
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (canonicalCauchySlicePoint 0 SpatialE0) := by
  rw [← spatialRadiusSquared_eq_globalActionRadius]
  exact fixedP506L0_Algebraic_p286Euler_zeroSlice_radialQuadratic space

/-- Complete source/action-owned zero-slice normal form: the fixed algebraic
Euler three-form is the spatial radius squared times one spatial-volume
three-form whose internal charge is read from the mother action at `e0`. -/
theorem fixedP506L0_Algebraic_p286Euler_zeroSlice_spatialVolumeNormalForm
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
        (canonicalCauchySlicePoint 0 space) =
      p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) •
        p286SpatialVolumeGaugeThreeForm
          fixedP506L0U6OccurrenceP286MotherActionCharge := by
  rw [fixedP506L0_Algebraic_p286Euler_zeroSlice_eq_globalActionRadius,
    show
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (canonicalCauchySlicePoint 0 SpatialE0) =
        p286SpatialVolumeGaugeThreeForm
          fixedP506L0U6OccurrenceP286MotherActionCharge from
      fixedP506L0_Algebraic_p286Euler_zeroSlice_e0_eq_spatialVolume]

private theorem canonical_connectionExteriorAction_zeroSlice
    (space : StageNineSpatialPoint) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate Canonical
          (canonicalCauchySlicePoint 0 space))
        (holonomicP286GaugeAuxiliaryCoordinate Canonical
          (canonicalCauchySlicePoint 0 space)) = 0 := by
  rw [show
      holonomicP286GaugeConnectionCoordinate Canonical
          (canonicalCauchySlicePoint 0 space) =
        holonomicP286GaugeConnectionCoordinate Constitutive
          (canonicalCauchySlicePoint 0 space) by
      unfold holonomicP286GaugeConnectionCoordinate
      rw [canonical_gaugeConnection_eq_constitutive],
    show
      holonomicP286GaugeAuxiliaryCoordinate Canonical
          (canonicalCauchySlicePoint 0 space) =
        holonomicP286GaugeAuxiliaryCoordinate Constitutive
          (canonicalCauchySlicePoint 0 space) by
      unfold holonomicP286GaugeAuxiliaryCoordinate
      rw [canonical_gaugeAuxiliary_eq_constitutive]]
  exact constitutive_connectionExteriorAction_zeroSlice space

/-- Pure exterior derivative of the source/action-generated algebraic P286
current on the complete Cauchy slice.  This is intentionally public because
later whole-section readbacks compare their spatial `123` assembly component
with this already generated action profile. -/
theorem algebraic_pureExterior_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative Algebraic
        (canonicalCauchySlicePoint 0 space) =
      ![positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0,
        -positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge] := by
  calc
    holonomicP286GaugeAuxiliaryExteriorDerivative Algebraic
          (canonicalCauchySlicePoint 0 space) =
        holonomicP286GaugeAuxiliaryExteriorDerivative Canonical
          (canonicalCauchySlicePoint 0 space) := by
      exact congrFun
        fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorDerivative_eq_canonical
        (canonicalCauchySlicePoint 0 space)
    _ = holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical
          (canonicalCauchySlicePoint 0 space) := by
      rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
        canonical_connectionExteriorAction_zeroSlice, add_zero]
    _ = holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Constitutive
          (canonicalCauchySlicePoint 0 space) := by
      exact congrFun canonical_exterior_eq_constitutive
        (canonicalCauchySlicePoint 0 space)
    _ = holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Constitutive 0 :=
      constitutive_exteriorCovariantDerivative_zeroSlice_eq_origin space
    _ = holonomicP286GaugeAuxiliaryExteriorDerivative Constitutive 0 := by
      rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts]
      have actionZero :
          pointwiseP286GaugeTwoFormConnectionExteriorAction
              (holonomicP286GaugeConnectionCoordinate Constitutive 0)
              (holonomicP286GaugeAuxiliaryCoordinate Constitutive 0) = 0 := by
        simpa [canonical_zero] using
          (constitutive_connectionExteriorAction_zeroSlice
            (0 : StageNineSpatialPoint))
      rw [actionZero, add_zero]
    _ = _ :=
      fixedP506L0ConstitutiveP286ExteriorDerivative_origin_normalForm

/-- Whole zero-slice action read needed by the fixed complete-joint P286
writer.  Spatial variation is confined to the `123` coordinate; the three
time-containing coordinates remain the exact source-owned `Q/0/0` profile. -/
theorem fixedP506L0_Algebraic_pointwiseDirectRequiredExterior_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    pointwiseDirectP286RequiredExteriorDerivative Source Algebraic
        (canonicalCauchySlicePoint 0 space) =
      ![positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0,
        -positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge -
          p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) •
            fixedP506L0U6OccurrenceP286MotherActionCharge] := by
  have actionIdentity :
      pointwiseDirectP286RequiredExteriorDerivative Source Algebraic
          (canonicalCauchySlicePoint 0 space) =
        holonomicP286GaugeAuxiliaryExteriorDerivative Algebraic
            (canonicalCauchySlicePoint 0 space) -
          holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
            (canonicalCauchySlicePoint 0 space) := by
    unfold pointwiseDirectP286RequiredExteriorDerivative
      holonomicFormNativeP286GaugeEulerThreeForm
      formNativePhysicalChargedGaugeCurrentThreeForm
    rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts]
    abel
  rw [actionIdentity,
    algebraic_pureExterior_zeroSlice_normalForm,
    fixedP506L0_Algebraic_p286Euler_zeroSlice_spatialVolumeNormalForm]
  funext triple
  fin_cases triple <;>
    simp [p286SpatialVolumeGaugeThreeForm]

private theorem fixedInput_pointwiseDirectRequiredExterior_eq_constitutive_zeroSlice
    (space : StageNineSpatialPoint) :
    pointwiseDirectP286RequiredExteriorDerivative Source FixedInput
        (canonicalCauchySlicePoint 0 space) =
      pointwiseDirectP286RequiredExteriorDerivative Source Constitutive
        (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  have coframeEq : FixedInput.coframe point = Constitutive.coframe point :=
    congrFun fixedP506FormNativeConstitutiveJointActionSuccessor_coframe.symm
      point
  have connectionEq :
      holonomicP286GaugeConnectionCoordinate FixedInput point =
        holonomicP286GaugeConnectionCoordinate Constitutive point := by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]
  have auxiliaryEq :
      holonomicP286GaugeAuxiliaryCoordinate FixedInput point =
        holonomicP286GaugeAuxiliaryCoordinate Constitutive point := by
    unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeAuxiliary]
    exact congrArg formNativeP286GaugeActualToCoordinateLinear
      (fixedP506FormNativeConstitutiveAuxiliaryField_zeroSlice space).symm
  have scalarEq : FixedInput.scalar point = Constitutive.scalar point :=
    congrFun fixedP506FormNativeConstitutiveJointActionSuccessor_scalar.symm
      point
  have scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative FixedInput point =
        holonomicScalarCovariantDerivative Constitutive point := by
    unfold holonomicScalarCovariantDerivative
    rw [fixedP506FormNativeConstitutiveJointActionSuccessor_scalar,
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]
  have matterEq : FixedInput.matter point = Constitutive.matter point :=
    congrFun fixedP506FormNativeConstitutiveJointActionSuccessor_matter.symm
      point
  have conjugateMatterEq :
      FixedInput.conjugateMatter point = Constitutive.conjugateMatter point :=
    congrFun
      fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter.symm
      point
  have chargedEq :=
    formNativeChargedGaugeThreeForm_eq_of_actionData_eq Source
      FixedInput Constitutive point coframeEq scalarEq
      scalarCovariantDerivativeEq matterEq conjugateMatterEq
  unfold pointwiseDirectP286RequiredExteriorDerivative
    formNativePhysicalChargedGaugeCurrentThreeForm
  rw [chargedEq, connectionEq, auxiliaryEq]

/-- Pure exterior derivative of the fixed live constitutive current on the
complete Cauchy slice.  This public normal form is the spatial anchor used by
the later source/current-only whole-section assembly. -/
theorem constitutive_pureExterior_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative Constitutive
        (canonicalCauchySlicePoint 0 space) =
      ![positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0,
        -positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge] := by
  calc
    holonomicP286GaugeAuxiliaryExteriorDerivative Constitutive
          (canonicalCauchySlicePoint 0 space) =
        holonomicP286GaugeAuxiliaryExteriorDerivative Constitutive 0 := by
      unfold holonomicP286GaugeAuxiliaryExteriorDerivative
      congr 1
      funext direction
      rw [
        fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryDirectionalDerivative_zeroSlice]
      exact
        (fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryDirectionalDerivative
          direction).symm
    _ = _ := fixedP506L0ConstitutiveP286ExteriorDerivative_origin_normalForm

private theorem constitutive_chargedGaugeThreeForm_eq_temporal_zeroSlice
    (space : StageNineSpatialPoint) :
    formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Constitutive
          (canonicalCauchySlicePoint 0 space)) =
      formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Temporal
          (canonicalCauchySlicePoint 0 space)) := by
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro direction
  simp only [formNativeChargedGaugeFirstLinearMap_apply]
  rw [congrFun
      (formNativeChargedGaugeFirstCoefficient_eq_currentSectors_local
        Constitutive direction) (canonicalCauchySlicePoint 0 space),
    congrFun
      (formNativeChargedGaugeFirstCoefficient_eq_currentSectors_local
        Temporal direction) (canonicalCauchySlicePoint 0 space)]
  simp only [Pi.add_apply]
  rw [
    temporal_scalarCurrent_zeroSlice_eq_constitutive,
    temporal_matterCurrent_zeroSlice_eq_constitutive]

private theorem constitutive_p286Euler_eq_algebraic_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Constitutive
        (canonicalCauchySlicePoint 0 space) =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
        (canonicalCauchySlicePoint 0 space) := by
  calc
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Constitutive
          (canonicalCauchySlicePoint 0 space) =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Constitutive
            (canonicalCauchySlicePoint 0 space) +
          formNativeChargedGaugeThreeForm Source 0
            (canonicalCauchySlicePoint 0 space)
            (toContinuumPointField Constitutive
              (canonicalCauchySlicePoint 0 space)) := by
      rfl
    _ = holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Canonical
            (canonicalCauchySlicePoint 0 space) +
          formNativeChargedGaugeThreeForm Source 0
            (canonicalCauchySlicePoint 0 space)
            (toContinuumPointField Temporal
              (canonicalCauchySlicePoint 0 space)) := by
      rw [congrFun canonical_exterior_eq_constitutive
          (canonicalCauchySlicePoint 0 space),
        constitutive_chargedGaugeThreeForm_eq_temporal_zeroSlice]
    _ = _ := (fixedP506L0_Algebraic_p286Euler_zeroSlice_support space).symm

/-- The same complete direct mother-action read on the solved fixed input.
This is transported through the already generated algebraic leg; no target
coordinate or residual value is supplied to either producer. -/
theorem fixedP506L0_FixedInput_pointwiseDirectRequiredExterior_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    pointwiseDirectP286RequiredExteriorDerivative Source FixedInput
        (canonicalCauchySlicePoint 0 space) =
      ![positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0,
        -positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge -
          p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) •
            fixedP506L0U6OccurrenceP286MotherActionCharge] := by
  rw [fixedInput_pointwiseDirectRequiredExterior_eq_constitutive_zeroSlice]
  have actionIdentity :
      pointwiseDirectP286RequiredExteriorDerivative Source Constitutive
          (canonicalCauchySlicePoint 0 space) =
        holonomicP286GaugeAuxiliaryExteriorDerivative Constitutive
            (canonicalCauchySlicePoint 0 space) -
          holonomicFormNativeP286GaugeEulerThreeForm Source 0 Constitutive
            (canonicalCauchySlicePoint 0 space) := by
    unfold pointwiseDirectP286RequiredExteriorDerivative
      holonomicFormNativeP286GaugeEulerThreeForm
      formNativePhysicalChargedGaugeCurrentThreeForm
    rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts]
    abel
  rw [actionIdentity,
    constitutive_pureExterior_zeroSlice_normalForm,
    constitutive_p286Euler_eq_algebraic_zeroSlice,
    fixedP506L0_Algebraic_p286Euler_zeroSlice_spatialVolumeNormalForm]
  funext triple
  fin_cases triple <;>
    simp [p286SpatialVolumeGaugeThreeForm]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
