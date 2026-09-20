import H0mework.Physics.FixedJoint.FixedSectionResponseResidual
import H0mework.Physics.RepairedAction.ActionResponseOperator

/-!
# Fixed P506/L0 repaired constitutive joint successor

This is the fixed-lineage specialization of the repaired action-owned
operator.  It is an origin/contact checkpoint on the path to the global
section zero fiber, not a claim that an origin equation alone closes S9-C.
No residual is supplied to the constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506RepairedConstitutiveJointActionSuccessor

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-- Same-source fixed P506/L0 output of the repaired common action
operator. -/
def FixedP506FormNativeRepairedConstitutiveJointActionSuccessor :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
    positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSuccessor_exactLineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506FormNativeJointActionSolvedSuccessor_exactLineage

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem fixedP506FormNativeRepairedCurrent_noncharacteristic :
    coframeTemporalPrincipalScalar
        (FixedP506FormNativeJointActionSolvedSuccessor.coframe 0) ≠
      0 := by
  have coframeAtOrigin :=
    fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice
      (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero] at coframeAtOrigin
  rw [coframeAtOrigin]
  simpa only [coframeTemporalPrincipalScalar_one] using
    (one_ne_zero : (1 : ℝ) ≠ 0)

private theorem fixedP506FormNativeRepairedCurrent_nondegenerate :
    Matrix.det (FixedP506FormNativeJointActionSolvedSuccessor.coframe 0) ≠
      0 := by
  have coframeAtOrigin :=
    fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice
      (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero] at coframeAtOrigin
  rw [coframeAtOrigin]
  simp

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSuccessor_coframe_origin :
    FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.coframe 0 =
      1 := by
  rw [
    FixedP506FormNativeRepairedConstitutiveJointActionSuccessor,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_coframe]
  have coframeAtOrigin :=
    fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice
      (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero] at coframeAtOrigin
  exact coframeAtOrigin

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSuccessor_simplicity :
    FormNativeGravitySimplicityEquation
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor :=
  diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_simplicity
    _ _

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSuccessor_auxiliaryEquation :
    FormNativeGravityAuxiliaryEquation
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor :=
  diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_auxiliaryEquation
    _ _

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSuccessor_primalActionLaw :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor
      0
      (holonomicMatterCovariantDerivative
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor
        0 canonicalLorentzianTimeDirection) := by
  exact
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_primalActionLaw
      positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
      fixedP506FormNativeRepairedCurrent_noncharacteristic

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSuccessor_liveAdjointActionLaw :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor
      0
      (holonomicConjugateMatterDerivativeDual
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor
        0 canonicalLorentzianTimeDirection) := by
  exact
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_liveAdjointActionLaw
      positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
      fixedP506FormNativeRepairedCurrent_nondegenerate
      fixedP506FormNativeRepairedCurrent_noncharacteristic

/-- No branch remains in either repaired matter channel on the generated
common actual. -/
theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSuccessor_response_unique
    (primalCandidate : DiracExteriorMatterCarrier)
    (adjointCandidate : Module.Dual ℂ DiracExteriorMatterCarrier)
    (primalLaw :
      HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor
        0 primalCandidate)
    (adjointLaw :
      HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor
        0 adjointCandidate) :
    primalCandidate =
        holonomicMatterCovariantDerivative
          FixedP506FormNativeRepairedConstitutiveJointActionSuccessor
          0 canonicalLorentzianTimeDirection ∧
      adjointCandidate =
        holonomicConjugateMatterDerivativeDual
          FixedP506FormNativeRepairedConstitutiveJointActionSuccessor
          0 canonicalLorentzianTimeDirection := by
  have generatedNoncharacteristic :
      coframeTemporalPrincipalScalar
          (FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.coframe
            0) ≠
        0 := by
    rw [
      fixedP506FormNativeRepairedConstitutiveJointActionSuccessor_coframe_origin]
    simpa only [coframeTemporalPrincipalScalar_one] using
      (one_ne_zero : (1 : ℝ) ≠ 0)
  have generatedNondegenerate :
      Matrix.det
          (FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.coframe
            0) ≠
        0 := by
    rw [
      fixedP506FormNativeRepairedConstitutiveJointActionSuccessor_coframe_origin]
    simp
  exact
    ⟨holonomicDiracDualCurrentCoframeMatterTimeActionLaw_unique
        _ _ generatedNoncharacteristic _ _ primalLaw
        fixedP506FormNativeRepairedConstitutiveJointActionSuccessor_primalActionLaw,
      holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_unique
        _ _ generatedNondegenerate generatedNoncharacteristic _ _ adjointLaw
        fixedP506FormNativeRepairedConstitutiveJointActionSuccessor_liveAdjointActionLaw⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506RepairedConstitutiveJointActionSuccessor
