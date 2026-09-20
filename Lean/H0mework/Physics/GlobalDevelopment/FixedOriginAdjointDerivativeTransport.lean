import H0mework.Physics.GlobalDevelopment.FixedOriginPrimalAdjointClosure

/-!
# Fixed P506/L0 global adjoint derivative transport

This module continues the generated primal/adjoint origin chain through the
complete spatial and temporal first germs.  It identifies the adjoint
derivative of the source/current-only global actual with the accepted
same-occurrence derivative from the already generated action profiles.

The result transports actual action data only.  It neither constructs a
field from a residual nor assumes an Euler receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginAdjointDerivativeTransport

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeLocalDifferentiability
open StageNineCoframeFirstJet
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonZeroFiber
open StageNineDiracDualFormNativeFixedP506FullOccurrenceAdjointTemporalRegularity
open StageNineDiracDualFormNativeFixedP506FullOccurrenceMatterTemporalRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterPointwiseEquation
open StageNineMatterCovariantDerivativeAffine
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineScalarPointwiseEquation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

theorem newActual_coframe_eq_profilePrimal :
    NewActual.coframe = ProfilePrimalActual.coframe := by
  change NewActual.coframe = ProfileRestartActual.coframe
  exact newActual_coframe_eq_profileRestart

theorem newActual_scalar_origin_eq_profilePrimal :
    NewActual.scalar 0 = ProfilePrimalActual.scalar 0 := by
  change NewActual.scalar 0 = ProfileRestartActual.scalar 0
  rw [newActual_scalar_origin_eq_input,
    profileRestartActual_scalar_origin_eq_input]

theorem newActual_conjugateMatter_origin_eq_profilePrimal :
    NewActual.conjugateMatter 0 =
      ProfilePrimalActual.conjugateMatter 0 := by
  change NewActual.conjugateMatter 0 =
    ProfileRestartActual.conjugateMatter 0
  rw [newActual_conjugateMatter_origin_eq_input,
    profileRestartActual_conjugateMatter_origin_eq_input]

theorem newActual_gravityConnection_origin_eq_profilePrimal :
    NewActual.gravityConnection 0 =
      ProfilePrimalActual.gravityConnection 0 := by
  change NewActual.gravityConnection 0 =
    ProfileRestartActual.gravityConnection 0
  exact newActual_gravityConnection_origin_eq_profileRestart

theorem newActual_gaugeConnection_origin_eq_profilePrimal :
    NewActual.gaugeConnection 0 =
      ProfilePrimalActual.gaugeConnection 0 := by
  change NewActual.gaugeConnection 0 =
    ProfileRestartActual.gaugeConnection 0
  exact newActual_gaugeConnection_origin_eq_profileRestart

theorem newActual_conjugateMatterDerivative_spatial_origin
    (direction : Fin 3) :
    holonomicConjugateMatterDerivativeDual NewActual 0 direction.succ =
      holonomicConjugateMatterDerivativeDual ProfilePrimalActual 0
        direction.succ := by
  unfold holonomicConjugateMatterDerivativeDual
  change
    matterDualOfCoordinates (newAdjointDerivative direction.succ) =
      matterDualOfCoordinates
        (holonomicConjugateMatterDerivativeCoordinates
          ProfilePrimalActual 0 direction.succ)
  rw [newActual_conjugateMatterDerivativeCoordinates_origin]
  unfold newAdjointDerivativeNormalForm
  rw [canonicalTimeProjection_coordinateDirection]
  have spatialNe :
      direction.succ ≠ canonicalLorentzianTimeDirection := by
    fin_cases direction <;> decide
  simp only [if_neg spatialNe, zero_smul, add_zero]
  apply congrArg matterDualOfCoordinates
  unfold holonomicConjugateMatterDerivativeCoordinates
  change
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates InputActual) 0 direction.succ =
      fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates ProfilePrimalActual) 0
          direction.succ
  rw [show
    holonomicConjugateMatterCoordinates ProfilePrimalActual =
      holonomicConjugateMatterCoordinates InputActual by
    unfold holonomicConjugateMatterCoordinates
    rw [show
      ProfilePrimalActual.conjugateMatter =
        ProfileRestartActual.conjugateMatter by rfl,
      profileRestartActual_conjugateMatter_eq_input]]

theorem
    newActual_liveAdjointKnownDensitizedDual_origin_eq_profilePrimal :
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
        NewActual 0 =
      holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
        ProfilePrimalActual 0 := by
  have coframeJet :
      holonomicCoframeFirstJetAt NewActual.coframe 0 =
        holonomicCoframeFirstJetAt ProfilePrimalActual.coframe 0 := by
    rw [newActual_coframe_eq_profilePrimal]
  have coframe :
      NewActual.coframe 0 = ProfilePrimalActual.coframe 0 :=
    congrFun newActual_coframe_eq_profilePrimal 0
  have conjugateCoordinates :
      holonomicConjugateMatterCoordinates NewActual 0 =
        holonomicConjugateMatterCoordinates ProfilePrimalActual 0 := by
    unfold holonomicConjugateMatterCoordinates
    rw [newActual_conjugateMatter_origin_eq_profilePrimal]
  have volume :
      generatedVolumeDensity (toContinuumPointField NewActual 0) =
        generatedVolumeDensity
          (toContinuumPointField ProfilePrimalActual 0) := by
    unfold generatedVolumeDensity toContinuumPointField
    rw [coframe]
  unfold holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
    holonomicDiracDualLiveCoframeAlgebraicDual
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
    holonomicLiveCoframeAffineGerm
  rw [coframe, volume,
    newActual_gravityConnection_origin_eq_profilePrimal,
    newActual_gaugeConnection_origin_eq_profilePrimal,
    newActual_scalar_origin_eq_profilePrimal,
    newActual_conjugateMatter_origin_eq_profilePrimal,
    coframeJet, conjugateCoordinates]
  simp_rw [newActual_conjugateMatterDerivative_spatial_origin]

theorem
    newActual_conjugateMatterTimeDerivative_origin_eq_profilePrimalActionVelocity :
    holonomicConjugateMatterDerivativeDual NewActual 0
        canonicalLorentzianTimeDirection =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        ProfilePrimalActual 0 := by
  rw [newActual_conjugateMatterTimeDerivative_origin]
  unfold newAdjointActionVelocity ProfilePrimalActual
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity]

theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_liveAdjointActionLaw_origin :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw NewActual 0
      (holonomicConjugateMatterDerivativeDual NewActual 0
        canonicalLorentzianTimeDirection) := by
  have profileCoframeOne : ProfilePrimalActual.coframe 0 = 1 := by
    change ProfileRestartActual.coframe 0 = 1
    rw [← congrFun newActual_coframe_eq_profileRestart 0,
      newActual_coframe_origin_eq_accepted]
    exact fixedP506L0FinalCommonActionActual_coframe_origin 0
  have nondegenerate :
      Matrix.det (ProfilePrimalActual.coframe 0) ≠ 0 := by
    rw [profileCoframeOne]
    simp
  have noncharacteristic :
      coframeTemporalPrincipalScalar (ProfilePrimalActual.coframe 0) ≠ 0 := by
    rw [profileCoframeOne, coframeTemporalPrincipalScalar_one]
    exact one_ne_zero
  have generated :=
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_satisfies
      ProfilePrimalActual 0 nondegenerate noncharacteristic
  unfold HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw at generated ⊢
  unfold generatedVolumeDensity toContinuumPointField at generated ⊢
  rw [newActual_conjugateMatterTimeDerivative_origin_eq_profilePrimalActionVelocity,
    congrFun newActual_coframe_eq_profilePrimal 0,
    newActual_liveAdjointKnownDensitizedDual_origin_eq_profilePrimal]
  exact generated

theorem acceptedActual_matter_eq_profileAdjoint :
    AcceptedActual.matter = ProfileAdjointActual.matter := by
  rw [fixedP506L0FinalCommonActionActual_matter]
  unfold recenteredCartanRepairedScalarSecondJetActual
    installScalarQuadraticTimeCorrection
    recenteredCartanRepairedConstitutiveCurrent
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
    ProfileAdjointActual ProfilePrimalActual ProfileRestartActual
    completeJointGeneratedProfileRestartCurrent
  rw [spatiallyRecenterHolonomicConfiguration_zero,
    fullyRecenterHolonomicConfiguration_zero]

theorem acceptedActual_conjugateMatter_eq_profileAdjoint :
    AcceptedActual.conjugateMatter =
      ProfileAdjointActual.conjugateMatter := by
  rw [fixedP506L0FinalCommonActionActual_conjugateMatter]
  unfold recenteredCartanRepairedScalarSecondJetActual
    installScalarQuadraticTimeCorrection
    recenteredCartanRepairedConstitutiveCurrent
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
    ProfileAdjointActual ProfilePrimalActual ProfileRestartActual
    completeJointGeneratedProfileRestartCurrent
  rw [spatiallyRecenterHolonomicConfiguration_zero,
    fullyRecenterHolonomicConfiguration_zero]

theorem profilePrimal_matterCoordinateDerivative_origin
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv (ProfilePrimalActual.matter point))
        0 direction =
      fieldDirectionalDerivative
          (fun point =>
            matterCoordinateEquiv (ProfileRestartActual.matter point))
          0 direction +
        if direction = canonicalLorentzianTimeDirection then
          matterCoordinateEquiv
            (diracDualCurrentCoframeMatterTimeResponseWrite
              ProfileRestartActual)
        else
          0 := by
  have backgroundDifferentiable : DifferentiableAt ℝ
      (fun point =>
        matterCoordinateEquiv (ProfileRestartActual.matter point)) 0 := by
    rw [profileRestartActual_matter_eq_input]
    exact
      ((fixedP506FormNativeJointActionSolvedSuccessor_smooth
        ).2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt
  have responseDifferentiable : DifferentiableAt ℝ
      (matterLinearTimeCoordinateWrite
        (diracDualCurrentCoframeMatterTimeResponseWrite
          ProfileRestartActual)) 0 :=
    ((matterLinearTimeCoordinateWrite_contDiff
      (diracDualCurrentCoframeMatterTimeResponseWrite
        ProfileRestartActual)).differentiable (by simp)).differentiableAt
  unfold ProfilePrimalActual
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    fieldDirectionalDerivative
  rw [show
    (fun point =>
      matterCoordinateEquiv
        ((installMatterLinearTimeResponse ProfileRestartActual
          (diracDualCurrentCoframeMatterTimeResponseWrite
            ProfileRestartActual)).matter point)) =
      (fun point =>
        matterCoordinateEquiv (ProfileRestartActual.matter point)) +
        matterLinearTimeCoordinateWrite
          (diracDualCurrentCoframeMatterTimeResponseWrite
            ProfileRestartActual) by
    funext point
    exact installMatterLinearTimeResponse_matter_coordinate
      ProfileRestartActual
      (diracDualCurrentCoframeMatterTimeResponseWrite ProfileRestartActual)
      point]
  rw [fderiv_add backgroundDifferentiable responseDifferentiable, add_apply]
  change
    _ + fieldDirectionalDerivative
          (matterLinearTimeCoordinateWrite
            (diracDualCurrentCoframeMatterTimeResponseWrite
              ProfileRestartActual))
          0 direction = _
  rw [matterLinearTimeCoordinateWrite_directionalDerivative]

theorem
    newActual_matterCoordinateDerivative_origin_eq_profileAdjoint
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (NewActual.matter point))
        0 direction =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (ProfileAdjointActual.matter point))
        0 direction := by
  change
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (NewActual.matter point))
        0 direction =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (ProfilePrimalActual.matter point))
        0 direction
  rw [profilePrimal_matterCoordinateDerivative_origin]
  by_cases timeDirection :
      direction = canonicalLorentzianTimeDirection
  · subst direction
    rw [if_pos rfl, newActual_matterCoordinateTimeDerivative_origin]
    rw [sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity]
    unfold diracDualCurrentCoframeMatterTimeResponseWrite
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
      holonomicMatterConnectionAction holonomicMatterCovariantDerivative
    simp only [map_add, map_sub, matterCoordinateEquiv.apply_symm_apply]
    module
  · rw [if_neg timeDirection, add_zero]
    have directionNeZero : direction ≠ 0 := by
      simpa [canonicalLorentzianTimeDirection] using timeDirection
    obtain ⟨spatialDirection, rfl⟩ :=
      Fin.eq_succ_of_ne_zero directionNeZero
    exact
      newActual_matterCoordinateSpatialDerivative_origin spatialDirection

theorem newActual_matterCoordinateDerivative_origin_eq_accepted
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (NewActual.matter point))
        0 direction =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (AcceptedActual.matter point))
        0 direction := by
  rw [acceptedActual_matter_eq_profileAdjoint]
  exact
    newActual_matterCoordinateDerivative_origin_eq_profileAdjoint direction

theorem profileAdjoint_conjugateMatterDerivative_origin
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual ProfileAdjointActual 0 direction =
      holonomicConjugateMatterDerivativeDual ProfilePrimalActual 0 direction +
        if direction = canonicalLorentzianTimeDirection then
          liveCoframeConjugateMatterTimeResponseWrite ProfilePrimalActual
        else
          0 := by
  have backgroundDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates ProfilePrimalActual) 0 := by
    have profilePrimalConjugateMatter :
        ProfilePrimalActual.conjugateMatter =
          InputActual.conjugateMatter := by
      change ProfileRestartActual.conjugateMatter =
        InputActual.conjugateMatter
      exact profileRestartActual_conjugateMatter_eq_input
    rw [show
      holonomicConjugateMatterCoordinates ProfilePrimalActual =
        holonomicConjugateMatterCoordinates InputActual by
      unfold holonomicConjugateMatterCoordinates
      rw [profilePrimalConjugateMatter]]
    exact
      ((holonomicConjugateMatterCoordinates_contDiff
        InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth).differentiable
        (by simp)).differentiableAt
  have responseDifferentiable : DifferentiableAt ℝ
      (conjugateMatterLinearTimeCoordinateWrite
        (liveCoframeConjugateMatterTimeResponseWrite ProfilePrimalActual)) 0 :=
    ((conjugateMatterLinearTimeCoordinateWrite_contDiff
      (liveCoframeConjugateMatterTimeResponseWrite
        ProfilePrimalActual)).differentiable (by simp)).differentiableAt
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  rw [show
    holonomicConjugateMatterCoordinates ProfileAdjointActual =
      holonomicConjugateMatterCoordinates ProfilePrimalActual +
        conjugateMatterLinearTimeCoordinateWrite
          (liveCoframeConjugateMatterTimeResponseWrite ProfilePrimalActual) by
    funext point
    exact
      installConjugateMatterLinearTimeResponse_conjugateMatterCoordinates
        ProfilePrimalActual
        (liveCoframeConjugateMatterTimeResponseWrite ProfilePrimalActual)
        point]
  rw [fderiv_add backgroundDifferentiable responseDifferentiable, add_apply]
  change
    matterDualOfCoordinates
        (_ + fieldDirectionalDerivative
          (conjugateMatterLinearTimeCoordinateWrite
            (liveCoframeConjugateMatterTimeResponseWrite
              ProfilePrimalActual))
          0 direction) =
      _
  rw [conjugateMatterLinearTimeCoordinateWrite_directionalDerivative]
  by_cases timeDirection :
      direction = canonicalLorentzianTimeDirection
  · simp [timeDirection, matterDualOfCoordinates_add,
      matterDualOfCoordinates_surjective]
  · simp [timeDirection]

theorem
    newActual_conjugateMatterDerivative_origin_eq_profileAdjoint
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual NewActual 0 direction =
      holonomicConjugateMatterDerivativeDual ProfileAdjointActual 0
        direction := by
  rw [profileAdjoint_conjugateMatterDerivative_origin]
  by_cases timeDirection :
      direction = canonicalLorentzianTimeDirection
  · subst direction
    rw [if_pos rfl,
      newActual_conjugateMatterTimeDerivative_origin_eq_profilePrimalActionVelocity]
    unfold liveCoframeConjugateMatterTimeResponseWrite
    module
  · rw [if_neg timeDirection, add_zero]
    have directionNeZero : direction ≠ 0 := by
      simpa [canonicalLorentzianTimeDirection] using timeDirection
    obtain ⟨spatialDirection, rfl⟩ :=
      Fin.eq_succ_of_ne_zero directionNeZero
    exact
      newActual_conjugateMatterDerivative_spatial_origin spatialDirection

theorem
    profileAdjoint_conjugateMatterCoordinates_differentiableAt_origin :
    DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates ProfileAdjointActual) 0 := by
  have backgroundDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates ProfilePrimalActual) 0 := by
    have profilePrimalConjugateMatter :
        ProfilePrimalActual.conjugateMatter =
          InputActual.conjugateMatter := by
      change ProfileRestartActual.conjugateMatter =
        InputActual.conjugateMatter
      exact profileRestartActual_conjugateMatter_eq_input
    rw [show
      holonomicConjugateMatterCoordinates ProfilePrimalActual =
        holonomicConjugateMatterCoordinates InputActual by
      unfold holonomicConjugateMatterCoordinates
      rw [profilePrimalConjugateMatter]]
    exact
      ((holonomicConjugateMatterCoordinates_contDiff InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth).differentiable
        (by simp)).differentiableAt
  have responseDifferentiable : DifferentiableAt ℝ
      (conjugateMatterLinearTimeCoordinateWrite
        (liveCoframeConjugateMatterTimeResponseWrite ProfilePrimalActual)) 0 :=
    ((conjugateMatterLinearTimeCoordinateWrite_contDiff
      (liveCoframeConjugateMatterTimeResponseWrite
        ProfilePrimalActual)).differentiable (by simp)).differentiableAt
  rw [show
    holonomicConjugateMatterCoordinates ProfileAdjointActual =
      holonomicConjugateMatterCoordinates ProfilePrimalActual +
        conjugateMatterLinearTimeCoordinateWrite
          (liveCoframeConjugateMatterTimeResponseWrite ProfilePrimalActual) by
    funext point
    exact
      installConjugateMatterLinearTimeResponse_conjugateMatterCoordinates
        ProfilePrimalActual
        (liveCoframeConjugateMatterTimeResponseWrite ProfilePrimalActual)
        point]
  exact backgroundDifferentiable.add responseDifferentiable

theorem newActual_conjugateMatterDerivative_origin_eq_accepted
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual NewActual 0 direction =
      holonomicConjugateMatterDerivativeDual AcceptedActual 0 direction := by
  calc
    _ = holonomicConjugateMatterDerivativeDual ProfileAdjointActual 0
          direction :=
      newActual_conjugateMatterDerivative_origin_eq_profileAdjoint direction
    _ = _ := by
      unfold holonomicConjugateMatterDerivativeDual
        holonomicConjugateMatterDerivativeCoordinates
        holonomicConjugateMatterCoordinates
      rw [acceptedActual_conjugateMatter_eq_profileAdjoint]

theorem
    newActual_conjugateMatterCoordinateDerivative_origin_eq_accepted
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates NewActual) 0 direction =
      fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates AcceptedActual) 0 direction := by
  have dualEquality :=
    newActual_conjugateMatterDerivative_origin_eq_accepted direction
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates at dualEquality
  have coordinateEquality := congrArg matterDualCoordinates dualEquality
  simpa only [matterDualCoordinates_matterDualOfCoordinates] using
    coordinateEquality

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginAdjointDerivativeTransport
