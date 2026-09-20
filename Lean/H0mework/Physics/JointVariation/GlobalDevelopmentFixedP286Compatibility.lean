import H0mework.Physics.JointVariation.GlobalDevelopmentFixed
import H0mework.Physics.ActualGerms.FixedP286AuxiliaryFirstJet
import H0mework.Physics.GaugeAction.P286RequiredExteriorActionDataCongruence

/-!
# Fixed P506/L0 global-development P286 compatibility

The global complete-joint writer first changes the temporal matter, adjoint,
and scalar fields and then asks the same mother action for its canonical P286
connection response.  The fixed-contact action data theorem proves that this
response is the already generated P506/L0 write.

This module transports the complete P286 primitive projection of that
algebraic global current to the established canonical actual.  No residual,
support coordinate, target field, or equation receipt is accepted by either
producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualP286AuxiliaryFirstJet
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286RequiredExteriorActionDataCongruence
open StageNineGlobalIntegratedAction
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineScalarActionSecondJetLocalActualLift
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev FixedTemporalCurrent : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

private abbrev FixedAlgebraicCurrent : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

private abbrev FixedProfileRestartCurrent :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    positiveSmoothUnifiedSource FixedAlgebraicCurrent

private abbrev FixedProfileRepairedCurrent :
    StageNineHolonomicConfiguration :=
  completeJointRepairedConstitutiveCurrent positiveSmoothUnifiedSource
    FixedProfileRestartCurrent

private abbrev FixedProfileAcceleration : ScalarCoordinateCarrier :=
  genericDiracDualScalarGeneratedAcceleration positiveSmoothUnifiedSource
    FixedProfileRepairedCurrent

private abbrev FixedProfileScalarCurrent :
    StageNineHolonomicConfiguration :=
  completeJointScalarSecondJetCurrent positiveSmoothUnifiedSource
    FixedProfileRestartCurrent

private abbrev FixedCanonicalInput : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalActionInput

private abbrev FixedCanonicalActual : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

theorem fixedP506L0CompleteJointGlobalTemporalCurrent_coframe_eq_canonicalInput :
    FixedTemporalCurrent.coframe = FixedCanonicalInput.coframe := by
  rw [FixedTemporalCurrent, completeJointGlobalTemporalCurrent,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe]
  exact fixedP506L0FinalCommonActionActual_coframe_eq_solved.symm

theorem
    fixedP506L0CompleteJointGlobalTemporalCurrent_gaugeConnection_eq_canonicalInput :
    FixedTemporalCurrent.gaugeConnection =
      FixedCanonicalInput.gaugeConnection := by
  change
    FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection =
      (fixedP506L0FinalCommonActionActual 0).gaugeConnection
  exact fixedP506L0FinalCommonActionActual_gaugeConnection_eq_solved.symm

/-- The post-write P286 connection is the same whole field as the established
canonical P506/L0 connection. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnection_eq_canonical :
    FixedAlgebraicCurrent.gaugeConnection =
      FixedCanonicalActual.gaugeConnection := by
  change
    (diracDualFormNativeP286CanonicalConnectionCandidate
      FixedTemporalCurrent
      (diracDualFormNativeP286CanonicalGeneratedWrite
        positiveSmoothUnifiedSource FixedTemporalCurrent)).gaugeConnection =
      (fixedP506L0P286CanonicalConnectionCandidate
        fixedP506L0P286CanonicalGeneratedWrite).gaugeConnection
  have writeEq :
      diracDualFormNativeP286CanonicalGeneratedWrite
          positiveSmoothUnifiedSource FixedTemporalCurrent =
        fixedP506L0P286CanonicalGeneratedWrite := by
    simpa [FixedTemporalCurrent] using
      fixedP506L0CompleteJointGlobalTemporalCurrent_p286CanonicalGeneratedWrite
  rw [writeEq]
  unfold diracDualFormNativeP286CanonicalConnectionCandidate
    fixedP506L0P286CanonicalConnectionCandidate
    installP286HolonomicConnectionSecondJet
  funext point direction
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate,
    gaugeConnection_varyP286GaugeConnectionCoordinate,
    fixedP506L0CompleteJointGlobalTemporalCurrent_gaugeConnection_eq_canonicalInput]

/-- The same algebraic current retains the fixed canonical coframe. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_coframe_eq_canonical :
    FixedAlgebraicCurrent.coframe =
      FixedCanonicalActual.coframe :=
  fixedP506L0CompleteJointGlobalTemporalCurrent_coframe_eq_canonicalInput

/-- Recomputing the constitutive auxiliary from equal coframe and connection
fields gives the same whole P286 auxiliary field. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeAuxiliary_eq_canonical :
    FixedAlgebraicCurrent.gaugeAuxiliary =
      FixedCanonicalActual.gaugeAuxiliary := by
  funext point pair
  change
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          (FixedTemporalCurrent.coframe point)
          (holonomicGaugeCurvature
            (diracDualFormNativeP286CanonicalConnectionCandidate
              FixedTemporalCurrent
              (diracDualFormNativeP286CanonicalGeneratedWrite
                positiveSmoothUnifiedSource FixedTemporalCurrent))
            point) pair =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          (FixedCanonicalInput.coframe point)
          (holonomicGaugeCurvature
            (fixedP506L0P286CanonicalConnectionCandidate
              fixedP506L0P286CanonicalGeneratedWrite)
            point) pair
  rw [
    fixedP506L0CompleteJointGlobalTemporalCurrent_coframe_eq_canonicalInput]
  apply congrFun
  apply congrArg
    (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (FixedCanonicalInput.coframe point))
  apply holonomicGaugeCurvature_eq_of_connection_eq
  exact
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnection_eq_canonical

theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_eq_canonical :
    holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent =
      holonomicP286GaugeAuxiliaryCoordinate FixedCanonicalActual := by
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeAuxiliary_eq_canonical]

/-- Consequently every pure-exterior first-jet readout of the new algebraic
current is the established canonical normal-form readout. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorDerivative_eq_canonical :
    holonomicP286GaugeAuxiliaryExteriorDerivative FixedAlgebraicCurrent =
      holonomicP286GaugeAuxiliaryExteriorDerivative FixedCanonicalActual := by
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
    p286GaugeAuxiliaryDirectionalDerivative
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_eq_canonical]

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_origin_eq_canonical :
    FixedAlgebraicCurrent.scalar 0 =
      FixedCanonicalActual.scalar 0 := by
  change
    (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor).scalar 0 =
      (fixedP506L0FinalCommonActionActual 0).scalar 0
  calc
    (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor).scalar 0 =
        FixedP506FormNativeJointActionSolvedSuccessor.scalar 0 := by
      rw [completeJointGlobalTemporalCurrent]
      simpa [canonicalCauchySlicePoint_zero_zero] using
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0
    _ = FixedP506FormNativeConstitutiveJointActionSuccessor.scalar 0 :=
      (congrFun fixedP506FormNativeConstitutiveJointActionSuccessor_scalar
        0).symm
    _ = (fixedP506L0FinalCommonActionActual 0).scalar 0 :=
      fixedP506L0FinalCommonActionActual_scalar_origin_eq_constitutive.symm

theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matter_origin_eq_canonical :
    FixedAlgebraicCurrent.matter 0 =
      FixedCanonicalActual.matter 0 := by
  change
    (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor).matter 0 =
      (fixedP506L0FinalCommonActionActual 0).matter 0
  calc
    (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor).matter 0 =
        FixedP506FormNativeJointActionSolvedSuccessor.matter 0 := by
      rw [completeJointGlobalTemporalCurrent]
      simpa [canonicalCauchySlicePoint_zero_zero] using
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0
    _ = FixedP506FormNativeConstitutiveJointActionSuccessor.matter 0 :=
      fixedP506FormNativeConstitutiveJointActionSuccessor_matter_origin.symm
    _ = (fixedP506L0FinalCommonActionActual 0).matter 0 :=
      fixedP506L0FinalCommonActionActual_matter_origin_eq_constitutive.symm

theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_conjugateMatter_origin_eq_canonical :
    FixedAlgebraicCurrent.conjugateMatter 0 =
      FixedCanonicalActual.conjugateMatter 0 := by
  change
    (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor).conjugateMatter 0 =
      (fixedP506L0FinalCommonActionActual 0).conjugateMatter 0
  calc
    (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor).conjugateMatter 0 =
        FixedP506FormNativeJointActionSolvedSuccessor.conjugateMatter 0 := by
      rw [completeJointGlobalTemporalCurrent]
      simpa [canonicalCauchySlicePoint_zero_zero] using
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0
    _ =
        FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter 0 :=
      fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter_origin.symm
    _ = (fixedP506L0FinalCommonActionActual 0).conjugateMatter 0 :=
      fixedP506L0FinalCommonActionActual_conjugateMatter_origin_eq_constitutive.symm

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_eq_temporal :
    holonomicScalarCovariantDerivative FixedAlgebraicCurrent 0 =
      holonomicScalarCovariantDerivative FixedTemporalCurrent 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  change
    fieldDirectionalDerivative FixedTemporalCurrent.scalar 0 direction +
        scalarMotherLieAction
          (p286LieBlockEmbed
            ((diracDualFormNativeP286CanonicalConnectionCandidate
              FixedTemporalCurrent
              (diracDualFormNativeP286CanonicalGeneratedWrite
                positiveSmoothUnifiedSource FixedTemporalCurrent)
              ).gaugeConnection 0 direction))
          (FixedTemporalCurrent.scalar 0) =
      _
  unfold diracDualFormNativeP286CanonicalConnectionCandidate
    installP286HolonomicConnectionSecondJet
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate]
  rw [p286HolonomicSecondJetQuadraticRealization_origin]
  simp only [Pi.zero_apply, map_zero, smul_zero, add_zero]

private theorem
    fixedP506L0P286CanonicalGeneratedActual_scalarCovariantDerivative_eq_input :
    holonomicScalarCovariantDerivative FixedCanonicalActual 0 =
      holonomicScalarCovariantDerivative FixedCanonicalInput 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  change
    fieldDirectionalDerivative FixedCanonicalInput.scalar 0 direction +
        scalarMotherLieAction
          (p286LieBlockEmbed
            ((fixedP506L0P286CanonicalConnectionCandidate
              fixedP506L0P286CanonicalGeneratedWrite).gaugeConnection
                0 direction))
          (FixedCanonicalInput.scalar 0) =
      _
  unfold fixedP506L0P286CanonicalConnectionCandidate
    installP286HolonomicConnectionSecondJet
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate]
  rw [p286HolonomicSecondJetQuadraticRealization_origin]
  simp only [Pi.zero_apply, map_zero, smul_zero, add_zero]

theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_origin_eq_canonical :
    holonomicScalarCovariantDerivative FixedAlgebraicCurrent 0 =
      holonomicScalarCovariantDerivative FixedCanonicalActual 0 := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_eq_temporal,
    fixedP506L0CompleteJointGlobalTemporalCurrent_scalarCovariantDerivative_origin_eq_solved,
    fixedP506L0P286CanonicalGeneratedActual_scalarCovariantDerivative_eq_input,
    fixedP506L0FinalCommonActionActual_scalarCovariantDerivative_origin_eq_solved]

/-- The new global algebraic current reads the same complete charged action
data at the fixed occurrence as the established canonical generated actual. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_chargedGaugeThreeForm_origin_eq_canonical :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedAlgebraicCurrent 0) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedCanonicalActual 0) := by
  apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
  · exact congrFun
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_coframe_eq_canonical
      0
  · exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_origin_eq_canonical
  · exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_origin_eq_canonical
  · exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matter_origin_eq_canonical
  · exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_conjugateMatter_origin_eq_canonical

theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_physicalChargedGaugeCurrent_origin_eq_canonical :
    formNativePhysicalChargedGaugeCurrentThreeForm
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedAlgebraicCurrent 0) =
      formNativePhysicalChargedGaugeCurrentThreeForm
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedCanonicalActual 0) := by
  unfold formNativePhysicalChargedGaugeCurrentThreeForm
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_chargedGaugeThreeForm_origin_eq_canonical]

/-- Equal primitive connection and auxiliary fields transport the complete
covariant exterior derivative, not merely its six-coordinate projection. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorCovariantDerivative_eq_canonical :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        FixedAlgebraicCurrent =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        FixedCanonicalActual := by
  funext point
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts]
  rw [congrFun
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorDerivative_eq_canonical
    point]
  unfold holonomicP286GaugeConnectionCoordinate
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnection_eq_canonical]
  rw [congrFun
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_eq_canonical
    point]

/-- The algebraic stage of the new global producer therefore already closes
the authoritative P286 connection equation at the fixed occurrence.  This is
transport of one source-generated action write, not a residual-built patch. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eulerThreeForm_origin_zero :
    holonomicFormNativeP286GaugeEulerThreeForm
        positiveSmoothUnifiedSource 0 FixedAlgebraicCurrent 0 =
      0 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [congrFun
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorCovariantDerivative_eq_canonical
    0]
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_chargedGaugeThreeForm_origin_eq_canonical]
  exact fixedP506L0P286CanonicalGeneratedActual_eulerThreeForm_origin_zero

theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorDerivative_origin_eq_required :
    holonomicP286GaugeAuxiliaryExteriorDerivative FixedAlgebraicCurrent 0 =
      formNativeCurrentP286RequiredExteriorDerivative
        positiveSmoothUnifiedSource FixedAlgebraicCurrent := by
  have connectionEquation :=
    (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_current
      positiveSmoothUnifiedSource 0 FixedAlgebraicCurrent 0).1
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eulerThreeForm_origin_zero
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts] at connectionEquation
  unfold formNativeCurrentP286RequiredExteriorDerivative
  exact eq_sub_of_add_eq connectionEquation

private theorem fixedProfileScalarCurrent_gaugeAuxiliary_origin :
    FixedProfileScalarCurrent.gaugeAuxiliary 0 =
      FixedAlgebraicCurrent.gaugeAuxiliary 0 := by
  change
    diracDualFormNativeConstitutiveAuxiliaryField
        positiveSmoothUnifiedSource FixedProfileRestartCurrent 0 =
      FixedAlgebraicCurrent.gaugeAuxiliary 0
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  rw [holonomicGaugeCurvature_eq_of_connection_eq
    FixedProfileRestartCurrent FixedAlgebraicCurrent
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
      positiveSmoothUnifiedSource FixedAlgebraicCurrent) 0]
  rfl

private theorem fixedProfileScalarCurrent_matter_origin :
    FixedProfileScalarCurrent.matter 0 =
      FixedAlgebraicCurrent.matter 0 := by
  unfold FixedProfileScalarCurrent completeJointScalarSecondJetCurrent
  rw [genericDiracDualScalarSecondJetActionResponse_matter]
  unfold completeJointRepairedConstitutiveCurrent
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_matter,
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_matter_origin]
  rfl

private theorem fixedProfileScalarCurrent_conjugateMatter_origin :
    FixedProfileScalarCurrent.conjugateMatter 0 =
      FixedAlgebraicCurrent.conjugateMatter 0 := by
  unfold FixedProfileScalarCurrent completeJointScalarSecondJetCurrent
  rw [genericDiracDualScalarSecondJetActionResponse_conjugateMatter]
  unfold completeJointRepairedConstitutiveCurrent
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin]
  rfl

private theorem fixedProfileScalarCurrent_scalar_eq :
    FixedProfileScalarCurrent.scalar =
      fun point =>
        FixedAlgebraicCurrent.scalar point +
          scalarQuadraticTimeCorrection FixedProfileAcceleration point := by
  rfl

private theorem fixedProfileScalarCurrent_gaugeConnection_eq :
    FixedProfileScalarCurrent.gaugeConnection =
      FixedAlgebraicCurrent.gaugeConnection := by
  rfl

private theorem fixedProfileScalarCurrent_scalar_origin :
    FixedProfileScalarCurrent.scalar 0 =
      FixedAlgebraicCurrent.scalar 0 := by
  rw [fixedProfileScalarCurrent_scalar_eq]
  simp

private theorem fixedProfileRepairedCurrent_scalar_eq :
    FixedProfileRepairedCurrent.scalar =
      FixedAlgebraicCurrent.scalar := by
  rfl

private theorem fixedProfileRepairedCurrent_gaugeConnection_eq :
    FixedProfileRepairedCurrent.gaugeConnection =
      FixedAlgebraicCurrent.gaugeConnection := by
  rfl

private theorem fixedProfileRepairedCurrent_scalarCovariantDerivative_origin :
    holonomicScalarCovariantDerivative FixedProfileRepairedCurrent 0 =
      holonomicScalarCovariantDerivative FixedAlgebraicCurrent 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [fixedProfileRepairedCurrent_scalar_eq,
    fixedProfileRepairedCurrent_gaugeConnection_eq]

/-- The scalar second-jet action write preserves the complete scalar first
jet at its common origin even when the supplied ambient scalar is not assumed
differentiable.  In the non-differentiable branch Lean's total `fderiv`
vanishes on both the base field and its smooth quadratic translate. -/
private theorem
    fixedProfileScalarCurrent_scalarCovariantDerivative_origin :
    holonomicScalarCovariantDerivative FixedProfileScalarCurrent 0 =
      holonomicScalarCovariantDerivative FixedAlgebraicCurrent 0 := by
  by_cases baseDifferentiable :
      DifferentiableAt ℝ FixedAlgebraicCurrent.scalar 0
  · have repairedDifferentiable :
        DifferentiableAt ℝ FixedProfileRepairedCurrent.scalar 0 := by
      rw [fixedProfileRepairedCurrent_scalar_eq]
      exact baseDifferentiable
    have generated :=
      holonomicScalarCovariantDerivative_installScalarQuadraticTimeCorrection_origin
        FixedProfileRepairedCurrent FixedProfileAcceleration
        repairedDifferentiable
    have generatedEq :
        holonomicScalarCovariantDerivative FixedProfileScalarCurrent 0 =
          holonomicScalarCovariantDerivative FixedProfileRepairedCurrent 0 := by
      simpa [FixedProfileScalarCurrent, completeJointScalarSecondJetCurrent,
        genericDiracDualScalarSecondJetActionResponse,
        installScalarQuadraticTimeCorrection] using generated
    exact generatedEq.trans
      fixedProfileRepairedCurrent_scalarCovariantDerivative_origin
  · have correctionDifferentiable :
        DifferentiableAt ℝ
          (scalarQuadraticTimeCorrection FixedProfileAcceleration) 0 :=
      ((scalarQuadraticTimeCoefficient_hasFDerivAt (0 : BasePoint)
        ).smul_const FixedProfileAcceleration).differentiableAt
    have generatedNotDifferentiable :
        ¬ DifferentiableAt ℝ FixedProfileScalarCurrent.scalar 0 := by
      intro generatedDifferentiable
      have recovered :
          DifferentiableAt ℝ
            (fun point =>
              FixedProfileScalarCurrent.scalar point -
                scalarQuadraticTimeCorrection FixedProfileAcceleration point)
            0 :=
        generatedDifferentiable.sub correctionDifferentiable
      have recoveredEq :
          (fun point =>
            FixedProfileScalarCurrent.scalar point -
              scalarQuadraticTimeCorrection FixedProfileAcceleration point) =
            FixedAlgebraicCurrent.scalar := by
        funext point
        rw [fixedProfileScalarCurrent_scalar_eq]
        module
      rw [recoveredEq] at recovered
      exact baseDifferentiable recovered
    funext direction
    unfold holonomicScalarCovariantDerivative fieldDirectionalDerivative
    rw [fderiv_zero_of_not_differentiableAt generatedNotDifferentiable,
      fderiv_zero_of_not_differentiableAt baseDifferentiable]
    rw [fixedProfileScalarCurrent_gaugeConnection_eq,
      fixedProfileScalarCurrent_scalar_origin]

/-- At the fixed occurrence the dependency-ordered profile producer reads
exactly the direct P286 action target of the algebraic current that entered
it.  The profile is therefore a forward mother-action read, not a residual
fed back into the temporal constructor. -/
theorem
    fixedP506L0CompleteJointP286RequiredExteriorProfile_origin_eq_direct :
    completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent 0 =
      formNativeCurrentP286RequiredExteriorDerivative
        positiveSmoothUnifiedSource FixedAlgebraicCurrent := by
  have actionData :=
    formNativeCurrentP286RequiredExteriorDerivative_eq_of_originActionData_eq
      positiveSmoothUnifiedSource FixedProfileScalarCurrent
      FixedAlgebraicCurrent
      (by rfl)
      (by rfl)
      (by
        unfold holonomicP286GaugeAuxiliaryCoordinate
        rw [fixedProfileScalarCurrent_gaugeAuxiliary_origin])
      fixedProfileScalarCurrent_scalar_origin
      fixedProfileScalarCurrent_scalarCovariantDerivative_origin
      fixedProfileScalarCurrent_matter_origin
      fixedProfileScalarCurrent_conjugateMatter_origin
  simpa [completeJointP286RequiredExteriorProfile,
    sourceActionGeneratedDiracDualCompleteJointProfiles,
    completeJointGeneratedProfileRestartCurrent,
    completeJointGeneratedProfilesFromCurrent,
    FixedProfileScalarCurrent, FixedProfileRestartCurrent] using actionData

theorem
    fixedP506L0CompleteJointP286RequiredExteriorProfile_origin_eq_canonicalExterior :
    completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent 0 =
      holonomicP286GaugeAuxiliaryExteriorDerivative
        FixedCanonicalActual 0 := by
  rw [
    fixedP506L0CompleteJointP286RequiredExteriorProfile_origin_eq_direct,
    ←
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorDerivative_origin_eq_required,
    congrFun
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_exteriorDerivative_eq_canonical
      0]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
