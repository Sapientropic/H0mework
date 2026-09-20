import H0mework.Physics.GlobalDevelopment.FixedTemporalElectricKernel

/-!
# Fixed P506/L0 complete-joint matter--adjoint temporal first jet

The fixed joint first cancels its source-generated primal and adjoint affine
coefficients at the fixed contact.  At every other canonical contact the
remaining drift is exactly the source-action velocity difference from that
contact.  The occurrence-native complete-joint producer then recomputes both
action profiles from the same fixed P506/L0 source/current.  At the common
origin both profiles are exactly zero, and the integrated global development
therefore has zero scalar, matter, and independent-dual temporal first jets.

These are concrete fixed-lineage action readouts.  They are reusable by both
the Dirac Euler readers and the charged-current read-after-write calculation;
no residual, support coordinate, target jet, or zero-fiber receipt is fed to
the producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointMatterAdjointTemporalFirstJet

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CartanRestartTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedMatterJointRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Actual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointGlobalDevelopmentActual

private abbrev InitialCauchy :=
  positiveP506MatterCurrentFullSynchronizedCauchyState

private abbrev FullCauchy :=
  positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual

private abbrev InitialMatterVelocity :=
  actionGeneratedMatterRawTimeVelocity InitialCauchy 0

private abbrev FreshMatterResponse :=
  currentCoframeMatterTimeResponseWrite FullCauchy

private abbrev InitialAdjointVelocity :=
  actionGeneratedConjugateMatterTimeDerivative InitialCauchy 0

private abbrev FreshAdjointResponse :=
  identityCoframeConjugateMatterTimeResponseWrite
    fixedGlobalPrimalMatterWrittenActual

private theorem fixedJoint_matter_timeAxis_normalForm
    (time : ℝ) (space : StageNineSpatialPoint) :
    matterCoordinateEquiv
        (FixedP506JointActual.matter
          (canonicalCauchySlicePoint time space)) =
      matterCoordinateEquiv diracSpinTwoMatterProbe +
        time •
          (matterCoordinateEquiv
              (actionGeneratedMatterRawTimeVelocity InitialCauchy space) +
            matterCoordinateEquiv FreshMatterResponse) := by
  change
    matterCoordinateEquiv
        (fixedGlobalPrimalMatterWrittenActual.matter
          (canonicalCauchySlicePoint time space)) = _
  unfold fixedGlobalPrimalMatterWrittenActual
    actionGeneratedCurrentCoframeMatterTimeResponseActual
  rw [installMatterLinearTimeResponse_matter_coordinate]
  unfold
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter]
  unfold
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
  rw [primitiveDiagonalActual_matter_slice]
  rw [(sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_retainsNonGravity
    positiveSmoothUnifiedSource InitialCauchy space).2.2.2.1]
  rw [fixedJointMatterCoordinates_normalForm]
  simp [matterLinearTimeCoordinateWrite, canonicalCauchySlicePoint,
    canonicalLorentzianTimeDirection, Fin.sum_univ_three]
  exact add_assoc _ _ _

private theorem fixedJoint_matterLinearCoefficient_zero :
    matterCoordinateEquiv InitialMatterVelocity +
        matterCoordinateEquiv FreshMatterResponse =
      0 := by
  let coefficient :=
    matterCoordinateEquiv InitialMatterVelocity +
      matterCoordinateEquiv FreshMatterResponse
  let line : ℝ → MatterCoordinateCarrier := fun time =>
    matterCoordinateEquiv
      (FixedP506JointActual.matter
        (canonicalCauchySlicePoint time 0))
  have lineDerivativeZero : HasDerivAt line 0 0 := by
    have actual := field_timeLine_hasDerivAt
      (fun point => matterCoordinateEquiv (FixedP506JointActual.matter point))
      (0 : StageNineSpatialPoint) 0
      ((fixedGlobalMatterDualP286Complete_smooth.2.2.2.2.2.2.2.1
        ).differentiable (by simp) |>.differentiableAt)
    have pointZero :
        canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
      ext direction
      fin_cases direction <;>
        simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
          Fin.sum_univ_three]
    rw [pointZero,
      fixedP506JointActual_matterCoordinate_temporalDerivative_zero] at actual
    simpa [line] using actual
  have lineDerivativeCoefficient : HasDerivAt line coefficient 0 := by
    rw [show line = fun time =>
        matterCoordinateEquiv diracSpinTwoMatterProbe +
          time • coefficient by
      funext time
      simpa [line, coefficient] using
        fixedJoint_matter_timeAxis_normalForm time 0]
    simpa using
      ((hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const coefficient)
  exact lineDerivativeCoefficient.unique lineDerivativeZero

private theorem fixedJoint_freshMatterResponse_eq_negInitial :
    matterCoordinateEquiv FreshMatterResponse =
      -matterCoordinateEquiv InitialMatterVelocity := by
  exact eq_neg_of_add_eq_zero_right
    fixedJoint_matterLinearCoefficient_zero

private theorem fixedJoint_conjugateMatter_timeAxis_normalForm
    (time : ℝ) (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier) :
    FixedP506JointActual.conjugateMatter
        (canonicalCauchySlicePoint time space) matter =
      diracSpinZeroMatterCoordinate matter +
        time •
          (actionGeneratedConjugateMatterTimeDerivative
              InitialCauchy space matter +
            FreshAdjointResponse matter) := by
  change
    fixedGlobalMatterDualWrittenActual.conjugateMatter
        (canonicalCauchySlicePoint time space) matter = _
  rw [show
      fixedGlobalMatterDualWrittenActual.conjugateMatter
          (canonicalCauchySlicePoint time space) matter =
        fixedGlobalPrimalMatterWrittenActual.conjugateMatter
            (canonicalCauchySlicePoint time space) matter +
          time • FreshAdjointResponse matter by
    simp [fixedGlobalMatterDualWrittenActual,
      actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual,
      installConjugateMatterLinearTimeResponse,
      varyConjugateMatterCoordinates,
      conjugateMatterLinearTimeCoordinateWrite,
      canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three, matterDualOfCoordinates_real_smul,
      matterDualOfCoordinates_surjective]]
  unfold fixedGlobalPrimalMatterWrittenActual
    actionGeneratedCurrentCoframeMatterTimeResponseActual
  rw [installMatterLinearTimeResponse_conjugateMatter]
  unfold
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter]
  unfold
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
  rw [primitiveDiagonalActual_conjugateMatter_slice]
  rw [(sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_retainsNonGravity
    positiveSmoothUnifiedSource InitialCauchy space).2.2.2.2]
  rw [fixedJointConjugateMatter_apply_normalForm]
  simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
    Fin.sum_univ_three]
  rw [add_assoc]

private theorem fixedJoint_conjugateMatterCoordinates_timeAxis_normalForm
    (time : ℝ) :
    matterDualCoordinates
        (FixedP506JointActual.conjugateMatter
          (canonicalCauchySlicePoint time 0)) =
      matterDualCoordinates diracSpinZeroMatterCoordinate +
        time •
          (matterDualCoordinates InitialAdjointVelocity +
            matterDualCoordinates FreshAdjointResponse) := by
  have fieldEq :
      FixedP506JointActual.conjugateMatter
          (canonicalCauchySlicePoint time 0) =
        diracSpinZeroMatterCoordinate +
          time • (InitialAdjointVelocity + FreshAdjointResponse) := by
    apply LinearMap.ext
    intro matter
    simpa only [LinearMap.add_apply, LinearMap.smul_apply] using
      fixedJoint_conjugateMatter_timeAxis_normalForm time 0 matter
  have coordinatesEq := congrArg matterDualCoordinates fieldEq
  have coordinatesRealSmul
      (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
      matterDualCoordinates (time • dual) =
        time • matterDualCoordinates dual := by
    apply PiLp.ext
    intro index
    rfl
  rw [matterDualCoordinates_add, coordinatesRealSmul,
    matterDualCoordinates_add] at coordinatesEq
  simpa using coordinatesEq

private theorem fixedJoint_conjugateMatterCoordinate_temporalDerivative_zero :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates FixedP506JointActual)
        0 canonicalLorentzianTimeDirection =
      0 := by
  have dualZero :
      holonomicConjugateMatterDerivativeDual FixedP506JointActual 0
          canonicalLorentzianTimeDirection =
        0 := by
    apply LinearMap.ext
    intro matter
    rw [holonomicConjugateMatterDerivativeDual_apply FixedP506JointActual
      fixedGlobalMatterDualP286Complete_smooth]
    exact fixedP506JointActual_conjugateMatter_temporalDerivative_zero matter
  change
    holonomicConjugateMatterDerivativeCoordinates FixedP506JointActual 0
        canonicalLorentzianTimeDirection =
      0
  apply PiLp.ext
  intro index
  change
    holonomicConjugateMatterDerivativeCoordinates FixedP506JointActual 0
        canonicalLorentzianTimeDirection index =
      (0 : ℂ)
  have evaluated := LinearMap.congr_fun dualZero
    (matterCoordinateEquiv.symm
      (EuclideanSpace.single index (1 : ℂ)))
  unfold holonomicConjugateMatterDerivativeDual at evaluated
  simpa only [matterDualOfCoordinates_basis_apply,
    LinearMap.zero_apply] using evaluated

private theorem fixedJoint_adjointCoordinateLinearCoefficient_zero :
    matterDualCoordinates InitialAdjointVelocity +
        matterDualCoordinates FreshAdjointResponse =
      0 := by
  let coefficient :=
    matterDualCoordinates InitialAdjointVelocity +
      matterDualCoordinates FreshAdjointResponse
  let line : ℝ → MatterCoordinateCarrier := fun time =>
    holonomicConjugateMatterCoordinates FixedP506JointActual
      (canonicalCauchySlicePoint time 0)
  have lineDerivativeZero : HasDerivAt line 0 0 := by
    have actual := field_timeLine_hasDerivAt
      (holonomicConjugateMatterCoordinates FixedP506JointActual)
      (0 : StageNineSpatialPoint) 0
      ((holonomicConjugateMatterCoordinates_contDiff FixedP506JointActual
        fixedGlobalMatterDualP286Complete_smooth
        ).differentiable (by simp) |>.differentiableAt)
    have pointZero :
        canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
      ext direction
      fin_cases direction <;>
        simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
          Fin.sum_univ_three]
    rw [pointZero,
      fixedJoint_conjugateMatterCoordinate_temporalDerivative_zero] at actual
    simpa [line] using actual
  have lineDerivativeCoefficient : HasDerivAt line coefficient 0 := by
    rw [show line = fun time =>
        matterDualCoordinates diracSpinZeroMatterCoordinate +
          time • coefficient by
      funext time
      simpa only [line, coefficient,
        holonomicConjugateMatterCoordinates] using
        fixedJoint_conjugateMatterCoordinates_timeAxis_normalForm time]
    simpa using
      ((hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const coefficient)
  exact lineDerivativeCoefficient.unique lineDerivativeZero

private theorem fixedJoint_adjointLinearCoefficient_zero :
    InitialAdjointVelocity + FreshAdjointResponse = 0 := by
  apply matterDualCoordinates_injective
  rw [matterDualCoordinates_add, matterDualCoordinates_zero]
  exact fixedJoint_adjointCoordinateLinearCoefficient_zero

private theorem fixedJoint_freshAdjointResponse_apply_eq_negInitial
    (matter : DiracExteriorMatterCarrier) :
    FreshAdjointResponse matter = -InitialAdjointVelocity matter := by
  have actual := LinearMap.congr_fun
    (eq_neg_of_add_eq_zero_right
      fixedJoint_adjointLinearCoefficient_zero) matter
  simpa only [LinearMap.neg_apply] using actual

/-- The ordered source-generated primal and adjoint writes cancel their
fixed-contact affine coefficients.  At an arbitrary canonical contact, the
entire remaining drift is therefore exactly the difference between that
contact's source-action velocity and the fixed origin velocity. -/
theorem fixedP506JointActual_matterAdjoint_canonicalVelocityDrift_normalForm
    (time : ℝ) (space : StageNineSpatialPoint) :
    matterCoordinateEquiv
        (FixedP506JointActual.matter
          (canonicalCauchySlicePoint time space)) =
      matterCoordinateEquiv diracSpinTwoMatterProbe +
        time •
          (matterCoordinateEquiv
              (actionGeneratedMatterRawTimeVelocity
                positiveP506MatterCurrentFullSynchronizedCauchyState space) -
            matterCoordinateEquiv
              (actionGeneratedMatterRawTimeVelocity
                positiveP506MatterCurrentFullSynchronizedCauchyState 0)) ∧
      ∀ matter : DiracExteriorMatterCarrier,
        FixedP506JointActual.conjugateMatter
            (canonicalCauchySlicePoint time space) matter =
          diracSpinZeroMatterCoordinate matter +
            time •
              (actionGeneratedConjugateMatterTimeDerivative
                  positiveP506MatterCurrentFullSynchronizedCauchyState
                  space matter -
                actionGeneratedConjugateMatterTimeDerivative
                  positiveP506MatterCurrentFullSynchronizedCauchyState
                  0 matter) := by
  constructor
  · rw [fixedJoint_matter_timeAxis_normalForm]
    rw [fixedJoint_freshMatterResponse_eq_negInitial]
    rfl
  · intro matter
    rw [fixedJoint_conjugateMatter_timeAxis_normalForm]
    rw [fixedJoint_freshAdjointResponse_apply_eq_negInitial]
    simp only [sub_eq_add_neg]

private theorem fixedInput_matterTemporalDerivative_origin_zero :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (FixedInput.matter point))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]
  exact fixedP506JointActual_matterCoordinate_temporalDerivative_zero

private theorem fixedInput_conjugateMatterDerivativeDual_origin_zero :
    holonomicConjugateMatterDerivativeDual FixedInput 0
        canonicalLorentzianTimeDirection =
      0 := by
  apply LinearMap.ext
  intro matter
  rw [holonomicConjugateMatterDerivativeDual_apply FixedInput
    fixedP506FormNativeJointActionSolvedSuccessor_smooth]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
    fixedP506JointActionSuccessor_conjugateMatter]
  exact fixedP506JointActual_conjugateMatter_temporalDerivative_zero matter

private theorem
    fixedInput_conjugateMatterCoordinateDerivative_origin_zero :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates FixedInput)
        0 canonicalLorentzianTimeDirection =
      0 := by
  have dualZero :=
    fixedInput_conjugateMatterDerivativeDual_origin_zero
  have coordinateZero := congrArg matterDualCoordinates dualZero
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates at coordinateZero
  simpa using coordinateZero

/-- The fixed primal profile correction itself has exact value zero at the
common occurrence. -/
theorem fixedP506L0CompleteJointMatterTemporalCorrection_origin_zero :
    completeJointMatterTemporalCoordinateCorrection
        positiveSmoothUnifiedSource FixedInput 0 =
      0 := by
  unfold completeJointMatterTemporalCoordinateCorrection
  rw [fixedProfile_matterVelocity_zero,
    fixedInput_matterTemporalDerivative_origin_zero]
  simp

/-- The independent-dual profile correction has the same exact value. -/
theorem fixedP506L0CompleteJointAdjointTemporalCorrection_origin_zero :
    completeJointAdjointTemporalCoordinateCorrection
        positiveSmoothUnifiedSource FixedInput 0 =
      0 := by
  unfold completeJointAdjointTemporalCoordinateCorrection
  rw [fixedProfile_adjointVelocity_zero,
    fixedInput_conjugateMatterCoordinateDerivative_origin_zero]
  simp

/-- Exact scalar temporal first jet of the same action-generated global
development.  The scalar acceleration enters only at second order. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopment_scalarTemporalFirstJet_origin_zero :
    fieldDirectionalDerivative Actual.scalar 0
        canonicalLorentzianTimeDirection =
      0 := by
  change
    fieldDirectionalDerivative
        (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
          FixedInput).scalar 0 canonicalLorentzianTimeDirection =
      0
  rw [fixedP506L0CompleteJointGlobalTemporalCurrent_scalar_firstJet_origin]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar,
    fixedP506JointActual_scalar_vacuum]
  simp [fieldDirectionalDerivative]

/-- One fixed, faithful temporal first-jet bundle shared by the primal Euler,
adjoint Euler, and charged-current consumers. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopment_matterAdjointScalarTemporalFirstJet_origin_zero :
    fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (Actual.matter point))
          0 canonicalLorentzianTimeDirection = 0 ∧
      holonomicConjugateMatterDerivativeDual Actual 0
          canonicalLorentzianTimeDirection = 0 ∧
      fieldDirectionalDerivative Actual.scalar 0
          canonicalLorentzianTimeDirection = 0 := by
  exact
    ⟨newActual_matterCoordinateTimeDerivative_origin_zero,
      newActual_conjugateMatterTimeDerivative_origin_zero,
      fixedP506L0CompleteJointGlobalDevelopment_scalarTemporalFirstJet_origin_zero⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointMatterAdjointTemporalFirstJet
