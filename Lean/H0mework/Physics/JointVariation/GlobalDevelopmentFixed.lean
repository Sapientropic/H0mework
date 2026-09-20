import H0mework.Physics.JointVariation.GlobalDevelopmentOperator
import H0mework.Physics.FinalJoint.FixedP286AffineIdentification
import H0mework.Physics.FinalJoint.FixedTimeAxisCoframe
import H0mework.Physics.FixedJoint.FixedP286CanonicalJointActionWrite
import H0mework.Physics.FixedJoint.FixedSectionResponseResidual

/-!
# Fixed P506/L0 global complete-joint development

The source/current-only global development preserves the already generated
KIN-16 coframe.  This module identifies that coframe with the established
quadratic contact normal form and transfers its canonical nondegenerate time
domain to the new common actual.

No determinant root, radius, branch, residual support, or regularity receipt
is supplied to the producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Preserved generated coframe -/

@[simp] theorem fixedP506L0CompleteJointGlobalDevelopmentActual_coframe :
    fixedP506L0CompleteJointGlobalDevelopmentActual.coframe =
      FixedP506FormNativeJointActionSolvedSuccessor.coframe := by
  simp [fixedP506L0CompleteJointGlobalDevelopmentActual]

/-- At each physical occurrence, the new global actual carries exactly the
quadratic contact coframe selected by that occurrence's spatial coordinate. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_timeLine_eq_finalCommon
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    fixedP506L0CompleteJointGlobalDevelopmentActual.coframe
        (canonicalCauchySlicePoint time space) =
      (fixedP506L0FinalCommonActionActual space).coframe
        (canonicalCauchySlicePoint time 0) := by
  rw [fixedP506L0CompleteJointGlobalDevelopmentActual_coframe,
    fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      _ _).coframe (canonicalCauchySlicePoint time space) = _
  rw [primitiveDiagonalActual_coframe_slice]
  exact
    (fixedP506L0FinalCommonActionActual_coframe_timeAxis_eq_contact
      space time).symm

/-- The complete generated zero slice retains the identity coframe. -/
theorem fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0CompleteJointGlobalDevelopmentActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      1 := by
  rw [fixedP506L0CompleteJointGlobalDevelopmentActual_coframe]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space

theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate_zeroSlice
    (space : StageNineSpatialPoint) :
    Matrix.det
        (fixedP506L0CompleteJointGlobalDevelopmentActual.coframe
          (canonicalCauchySlicePoint 0 space)) ≠
      0 := by
  rw [fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_zeroSlice]
  norm_num

/-- The fixed global actual therefore closes the algebraic P286 auxiliary
equation on its entire generated Cauchy slice. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_p286AuxiliaryEquation_zeroSlice
    (space : StageNineSpatialPoint) :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField
        fixedP506L0CompleteJointGlobalDevelopmentActual
        (canonicalCauchySlicePoint 0 space)) := by
  exact
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_p286AuxiliaryEquation_zeroSlice
      positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor space
      (fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate_zeroSlice
        space)

/-- The canonical connected determinant component transfers unchanged to
the new common actual. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate
    (space : StageNineSpatialPoint)
    {time : ℝ}
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    Matrix.det
        (fixedP506L0CompleteJointGlobalDevelopmentActual.coframe
          (canonicalCauchySlicePoint time space)) ≠
      0 := by
  rw [
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_timeLine_eq_finalCommon]
  exact
    fixedP506L0FinalCommonTimeAxisOriginDomain_nondegenerate space inDomain

/-- Coframe regularity is inherited from the fixed source/current normal
form; it is not an input certificate to the global writer. -/
theorem fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_contDiff
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ ∞ (fun point =>
      fixedP506L0CompleteJointGlobalDevelopmentActual.coframe
        point internal coordinate) := by
  rw [fixedP506L0CompleteJointGlobalDevelopmentActual_coframe]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
      internal coordinate

/-! ## Fixed zero-slice scalar first jet -/

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- At the fixed P506/L0 contact, the global temporal producer preserves the
complete scalar first jet without accepting a regularity receipt. -/
theorem fixedP506L0CompleteJointGlobalTemporalCurrent_scalar_firstJet_origin :
    ∀ direction : LorentzianIndex,
      fieldDirectionalDerivative
          (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor).scalar
          0 direction =
        fieldDirectionalDerivative
          FixedP506FormNativeJointActionSolvedSuccessor.scalar
          0 direction := by
  intro direction
  have currentDifferentiable :
      DifferentiableAt ℝ
        FixedP506FormNativeJointActionSolvedSuccessor.scalar 0 :=
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
      ).differentiable (by simp) |>.differentiableAt
  by_cases generatedDifferentiable :
      DifferentiableAt ℝ
        (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor).scalar 0
  · have generated :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_firstJet_zeroSlice
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor 0
        (by simpa [canonicalCauchySlicePoint_zero_zero] using
          currentDifferentiable)
        (by simpa [completeJointGlobalTemporalCurrent,
            canonicalCauchySlicePoint_zero_zero] using
          generatedDifferentiable) direction
    simpa [completeJointGlobalTemporalCurrent,
      canonicalCauchySlicePoint_zero_zero] using generated
  · have generatedDerivativeZero :
        fieldDirectionalDerivative
            (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
              FixedP506FormNativeJointActionSolvedSuccessor).scalar
            0 direction =
          0 := by
      unfold fieldDirectionalDerivative
      rw [fderiv_zero_of_not_differentiableAt generatedDifferentiable]
      rfl
    have currentDerivativeZero :
        fieldDirectionalDerivative
            FixedP506FormNativeJointActionSolvedSuccessor.scalar
            0 direction =
          0 := by
      rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
        fixedP506JointActionSuccessor_scalar,
        fixedP506JointActual_scalar_vacuum]
      simp [fieldDirectionalDerivative]
    rw [generatedDerivativeZero, currentDerivativeZero]

theorem
    fixedP506L0CompleteJointGlobalTemporalCurrent_scalarCovariantDerivative_origin_eq_solved :
    holonomicScalarCovariantDerivative
        (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor) 0 =
      holonomicScalarCovariantDerivative
        FixedP506FormNativeJointActionSolvedSuccessor 0 := by
  have gaugeConnectionEq :
      (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor).gaugeConnection =
        FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection := by
    rfl
  have scalarOriginEq :
      (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor).scalar 0 =
        FixedP506FormNativeJointActionSolvedSuccessor.scalar 0 := by
    rw [completeJointGlobalTemporalCurrent]
    simpa [canonicalCauchySlicePoint_zero_zero] using
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor 0
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [
    fixedP506L0CompleteJointGlobalTemporalCurrent_scalar_firstJet_origin
      direction,
    gaugeConnectionEq, scalarOriginEq]

/-- The source/current-only global temporal leg exposes exactly the same
fixed-contact action data as the established P506/L0 canonical input.
Therefore the unique P286 principal write generated by the mother action is
literally the already computed fixed write. -/
theorem
    fixedP506L0CompleteJointGlobalTemporalCurrent_p286CanonicalGeneratedWrite :
    diracDualFormNativeP286CanonicalGeneratedWrite
        positiveSmoothUnifiedSource
        (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor) =
      fixedP506L0P286CanonicalGeneratedWrite := by
  calc
    diracDualFormNativeP286CanonicalGeneratedWrite
          positiveSmoothUnifiedSource
          (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor) =
        diracDualFormNativeP286CanonicalGeneratedWrite
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonActionActual 0) := by
      apply
        diracDualFormNativeP286CanonicalGeneratedWrite_eq_of_actionData_eq
      · rw [completeJointGlobalTemporalCurrent,
          sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe]
        exact fixedP506L0FinalCommonActionActual_coframe_eq_solved.symm
      · change
          FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection =
            (fixedP506L0FinalCommonActionActual 0).gaugeConnection
        exact
          fixedP506L0FinalCommonActionActual_gaugeConnection_eq_solved.symm
      · calc
          (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
                FixedP506FormNativeJointActionSolvedSuccessor).scalar 0 =
              FixedP506FormNativeJointActionSolvedSuccessor.scalar 0 := by
            rw [completeJointGlobalTemporalCurrent]
            simpa [canonicalCauchySlicePoint_zero_zero] using
              sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
                positiveSmoothUnifiedSource
                FixedP506FormNativeJointActionSolvedSuccessor 0
          _ =
              FixedP506FormNativeConstitutiveJointActionSuccessor.scalar 0 :=
            (congrFun
              fixedP506FormNativeConstitutiveJointActionSuccessor_scalar
              0).symm
          _ = (fixedP506L0FinalCommonActionActual 0).scalar 0 :=
            fixedP506L0FinalCommonActionActual_scalar_origin_eq_constitutive.symm
      · exact
          fixedP506L0CompleteJointGlobalTemporalCurrent_scalarCovariantDerivative_origin_eq_solved.trans
            fixedP506L0FinalCommonActionActual_scalarCovariantDerivative_origin_eq_solved.symm
      · calc
          (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
                FixedP506FormNativeJointActionSolvedSuccessor).matter 0 =
              FixedP506FormNativeJointActionSolvedSuccessor.matter 0 := by
            rw [completeJointGlobalTemporalCurrent]
            simpa [canonicalCauchySlicePoint_zero_zero] using
              sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
                positiveSmoothUnifiedSource
                FixedP506FormNativeJointActionSolvedSuccessor 0
          _ =
              FixedP506FormNativeConstitutiveJointActionSuccessor.matter 0 :=
            fixedP506FormNativeConstitutiveJointActionSuccessor_matter_origin.symm
          _ = (fixedP506L0FinalCommonActionActual 0).matter 0 :=
            fixedP506L0FinalCommonActionActual_matter_origin_eq_constitutive.symm
      · calc
          (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
                FixedP506FormNativeJointActionSolvedSuccessor
              ).conjugateMatter 0 =
              FixedP506FormNativeJointActionSolvedSuccessor.conjugateMatter 0 := by
            rw [completeJointGlobalTemporalCurrent]
            simpa [canonicalCauchySlicePoint_zero_zero] using
              sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
                positiveSmoothUnifiedSource
                FixedP506FormNativeJointActionSolvedSuccessor 0
          _ =
              FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter
                0 :=
            fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter_origin.symm
          _ =
              (fixedP506L0FinalCommonActionActual 0).conjugateMatter 0 :=
            fixedP506L0FinalCommonActionActual_conjugateMatter_origin_eq_constitutive.symm
    _ = fixedP506L0P286CanonicalGeneratedWrite := by
      rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
