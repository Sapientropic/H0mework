import H0mework.Physics.IdentityHessian.CartanECNormalFixedGlobalMatterDualP286CompleteActual
import H0mework.Physics.DualVariation.JointResidualCarrier
import H0mework.Physics.MatterCurrent.P286CompleteActionPrincipalFullNonlinearLocalActualLift

/-!
# Complete repaired-root residual on the fixed P506/L0 successor

This module computes the authoritative Dirac-dual form-native joint residual
on the current fixed P506/L0 action-generated actual.  It does not advance
one residual projection at a time: every theorem below is a projection of
the single complete carrier, and the frontier is the carrier's full support
or its zero fiber.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointResidual

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCoframeTwoFormPairing
open StageNineCoframeFirstJet
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanReactionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeIdentityECCartanRestartOriginCurvature
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedCartanJointRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalJointLocalActualLift
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeP286GaugeDerivativeIntegrationByParts
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineIIPlusRestriction
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineP286SourceAffineCurvatureJetNormalForm
open StageNineResidualLimitCoframeBalanceDecision
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedP286ResponseReplay
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineTopologicalFourFormPairing
open StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRestriction
open SU7ExteriorYukawaMassSpectrum
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance fixedP506JointP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance fixedP506JointP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity.fixedP286CoordinateIndexFintype

local instance fixedP506JointP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity.fixedP286CoordinateIsTopologicalAddGroup

abbrev FixedP506JointActual : StageNineHolonomicConfiguration :=
  positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual

private abbrev FixedP506JointCurrent : StageNineHolonomicConfiguration :=
  positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual

/-- One complete residual section, generated from the fixed proof-free source
and the current common actual. -/
def fixedP506JointResidualSection :
    BasePoint → DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualSection positiveSmoothUnifiedSource
    FixedP506JointActual

private theorem fixedCanonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem fixedPrimitiveDiagonal_matter_origin :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.matter
        0 =
      diracSpinTwoMatterProbe := by
  have zeroSlice := congrArg
    (fun state : StageNineCauchyState => state.matter 0)
    fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.matter
        (canonicalCauchySlicePoint 0 0) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.matter
        0 at zeroSlice
  rw [fixedCanonicalCauchySlicePoint_zero_zero] at zeroSlice
  rw [zeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState 0
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState).matter 0 =
        diracSpinTwoMatterProbe
  rw [reads.2.2.2.2.2.2.2.2.1]
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
  change (fixedCartanReactionContact 0).matter 0 = diracSpinTwoMatterProbe
  exact fixedCartanReactionContact_matter_origin 0

private theorem fixedPrimitiveDiagonal_conjugateMatter_origin :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.conjugateMatter
        0 =
      diracSpinZeroMatterCoordinate := by
  have zeroSlice := congrArg
    (fun state : StageNineCauchyState => state.conjugateMatter 0)
    fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.conjugateMatter
        (canonicalCauchySlicePoint 0 0) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.conjugateMatter
        0 at zeroSlice
  rw [fixedCanonicalCauchySlicePoint_zero_zero] at zeroSlice
  rw [zeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState 0
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState).conjugateMatter
        0 =
      diracSpinZeroMatterCoordinate
  rw [reads.2.2.2.2.2.2.2.2.2]
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
  change
    (fixedCartanReactionContact 0).conjugateMatter 0 =
      diracSpinZeroMatterCoordinate
  exact fixedCartanReactionContact_conjugateMatter_origin 0

private theorem fixedPrimitiveDiagonal_scalar_origin :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.scalar
        0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  have zeroSlice := congrArg
    (fun state : StageNineCauchyState => state.scalar 0)
    fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.scalar
        (canonicalCauchySlicePoint 0 0) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.scalar
        0 at zeroSlice
  rw [fixedCanonicalCauchySlicePoint_zero_zero] at zeroSlice
  rw [zeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState 0
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState).scalar 0 =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  rw [reads.2.2.2.2.2.2.1]
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
  change
    (fixedCartanReactionContact 0).scalar 0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  exact fixedCartanReactionContact_scalar 0 0

theorem fixedP506JointActual_matter_origin :
    FixedP506JointActual.matter 0 = diracSpinTwoMatterProbe := by
  change
    (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
      FixedP506JointCurrent).matter 0 =
        diracSpinTwoMatterProbe
  rw [currentP286CompleteActionResponseOperator_matter,
    fixedGlobalMatterDualFullCauchy_matter]
  unfold fixedGlobalPrimalMatterWrittenActual
  rw [actionGeneratedCurrentCoframeMatterTimeResponseActual_matter_origin]
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.matter
        0 =
      diracSpinTwoMatterProbe
  exact fixedPrimitiveDiagonal_matter_origin

theorem fixedP506JointActual_conjugateMatter_origin :
    FixedP506JointActual.conjugateMatter 0 =
      diracSpinZeroMatterCoordinate := by
  change
    (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
      FixedP506JointCurrent).conjugateMatter 0 =
        diracSpinZeroMatterCoordinate
  rw [currentP286CompleteActionResponseOperator_conjugateMatter,
    fixedGlobalMatterDualFullCauchy_conjugateMatter]
  unfold fixedGlobalMatterDualWrittenActual
  rw [
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin]
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.conjugateMatter
        0 =
      diracSpinZeroMatterCoordinate
  exact fixedPrimitiveDiagonal_conjugateMatter_origin

theorem fixedP506JointActual_scalar_origin :
    FixedP506JointActual.scalar 0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
      FixedP506JointCurrent).scalar 0 =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  rw [currentP286CompleteActionResponseOperator_scalar,
    fixedGlobalMatterDualFullCauchy_scalar]
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.scalar
        0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  exact fixedPrimitiveDiagonal_scalar_origin

/-! ## Fixed Dirac-dual matter zero fiber -/

private theorem fixedP506VacuumMassMap_hyperchargeProbe_zero :
    exteriorYukawaMassMap
        (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
        (su7ExteriorBasis 2 hyperchargeDegreeTwoIndex) =
      0 := by
  rw [positive_sourceGeneratedVacuumBase]
  have overlaps :
      ∀ output input : Fin 2,
        ¬ Disjoint hyperchargeDegreeTwoIndex.1
          (finiteGenerationScalarIndex output input).1 := by
    intro output input
    fin_cases output <;> fin_cases input <;> decide
  simp [finiteGenerationJointBreakingScalar, Fin.sum_univ_two,
    exteriorYukawaMassMap_add_breaking, finiteGenerationBreakingTensor,
    exteriorYukawaMassMap_basisPair_of_not_disjoint, overlaps]

/-- The source-generated fixed vacuum annihilates the selected spin-two
matter probe under the repaired Dirac-dual Yukawa operator. -/
theorem fixedP506VacuumDiracDualYukawa_spinTwo_zero :
    diracDualRightChiralYukawaAction
        (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
        diracSpinTwoMatterProbe =
      0 := by
  have projector :
      diracMatrixMatterAction rightChiralityProjector
          diracSpinTwoMatterProbe =
        diracSpinTwoMatterProbe := by
    funext spin
    fin_cases spin <;>
      simp [diracMatrixMatterAction, rightChiralityProjector,
        diracGammaFive, Fin.sum_univ_four, diracSpinTwoMatterProbe]
    all_goals norm_num
  rw [diracDualRightChiralYukawaAction, LinearMap.comp_apply, projector]
  funext spin
  fin_cases spin
  · simp [diracExteriorYukawaInternalAction, internalMatterLinearAction,
      exteriorYukawaInternalAction, diracSpinTwoMatterProbe]
  · simp [diracExteriorYukawaInternalAction, internalMatterLinearAction,
      exteriorYukawaInternalAction, diracSpinTwoMatterProbe]
  · change
      exteriorYukawaInternalAction
          (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
          p286HyperchargeMatterProbe =
        0
    apply Prod.ext
    · exact fixedP506VacuumMassMap_hyperchargeProbe_zero
    · rfl
  · simp [diracExteriorYukawaInternalAction, internalMatterLinearAction,
      exteriorYukawaInternalAction, diracSpinTwoMatterProbe]

private theorem fixedP506VacuumChiralYukawa_spinTwo_zero :
    chiralExteriorYukawaAction
        (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
        diracSpinTwoMatterProbe =
      0 := by
  unfold chiralExteriorYukawaAction
  simp only [LinearMap.comp_apply]
  have internalZero :
      diracExteriorYukawaInternalAction
          (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
          (diracMatrixMatterAction rightChiralityProjector
            diracSpinTwoMatterProbe) =
        0 := by
    have repaired := fixedP506VacuumDiracDualYukawa_spinTwo_zero
    simpa [diracDualRightChiralYukawaAction] using repaired
  rw [internalZero]
  simp

private theorem fixedP506JointActual_coframe_eq_current :
    FixedP506JointActual.coframe = FixedP506JointCurrent.coframe :=
  currentP286CompleteActionResponseOperator_coframe
    positiveSmoothUnifiedSource FixedP506JointCurrent

private theorem fixedP506JointActual_gravityConnection_eq_current :
    FixedP506JointActual.gravityConnection =
      FixedP506JointCurrent.gravityConnection :=
  currentP286CompleteActionResponseOperator_gravityConnection
    positiveSmoothUnifiedSource FixedP506JointCurrent

private theorem fixedP506JointActual_gaugeConnection_eq_current :
    FixedP506JointActual.gaugeConnection =
      FixedP506JointCurrent.gaugeConnection :=
  currentP286CompleteActionResponseOperator_gaugeConnection
    positiveSmoothUnifiedSource FixedP506JointCurrent

private theorem fixedP506JointActual_conjugateMatter_eq_current :
    FixedP506JointActual.conjugateMatter =
      FixedP506JointCurrent.conjugateMatter :=
  currentP286CompleteActionResponseOperator_conjugateMatter
    positiveSmoothUnifiedSource FixedP506JointCurrent

private theorem fixedP506JointActual_pointField_origin_eq_current :
    toContinuumPointField FixedP506JointActual 0 =
      toContinuumPointField FixedP506JointCurrent 0 :=
  currentP286CompleteActionResponseOperator_pointField_origin
    positiveSmoothUnifiedSource FixedP506JointCurrent

private theorem fixedP506JointActual_oldYukawa_origin_zero :
    chiralExteriorYukawaAction
        (scalarCoordinateEquiv.symm
          (scalarFrameRelativeCoordinates positiveSmoothUnifiedSource 0 0
            (toContinuumPointField FixedP506JointActual 0).scalar))
        (matterFrameRelative positiveSmoothUnifiedSource 0 0
          (toContinuumPointField FixedP506JointActual 0).matter) =
      0 := by
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, toContinuumPointField]
  rw [fixedP506JointActual_scalar_origin,
    fixedP506JointActual_matter_origin]
  rw [sourceGeneratedVacuumCoordinates,
    scalarCoordinateEquiv.symm_apply_apply]
  exact fixedP506VacuumChiralYukawa_spinTwo_zero

theorem fixedP506JointActual_generatedContinuumMatterVector_origin_zero :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedP506JointActual 0) =
      0 := by
  rw [fixedP506JointActual_pointField_origin_eq_current]
  exact fixedGlobalMatterDualFullCauchy_diracYukawa

private theorem fixedP506JointActual_kineticVector_origin_zero :
    generatedContinuumMatterKineticVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedP506JointActual 0) =
      0 := by
  have oldEquation :=
    fixedP506JointActual_generatedContinuumMatterVector_origin_zero
  unfold generatedContinuumMatterVector at oldEquation
  rw [fixedP506JointActual_oldYukawa_origin_zero, add_zero] at oldEquation
  simpa [generatedContinuumMatterKineticVector,
    matterCovariantDerivativeVariationVector,
    matterCovariantDerivativeKineticSum] using oldEquation

private theorem fixedP506JointActual_repairedYukawa_origin_zero :
    generatedContinuumDiracDualYukawaVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedP506JointActual 0) =
      0 := by
  unfold generatedContinuumDiracDualYukawaVector
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, toContinuumPointField]
  rw [fixedP506JointActual_scalar_origin,
    fixedP506JointActual_matter_origin]
  rw [sourceGeneratedVacuumCoordinates,
    scalarCoordinateEquiv.symm_apply_apply]
  exact fixedP506VacuumDiracDualYukawa_spinTwo_zero

/-- The fixed joint contact also closes the repaired Dirac-dual matter
vector.  This public readout lets later same-lineage action writes reuse the
already generated repaired matter law without replaying the vacuum Yukawa
calculation. -/
theorem fixedP506JointActual_repairedMatterVector_origin_zero :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedP506JointActual 0) =
      0 := by
  rw [generatedContinuumDiracDualMatterVector,
    fixedP506JointActual_kineticVector_origin_zero,
    fixedP506JointActual_repairedYukawa_origin_zero, zero_add]

theorem fixedP506JointResidual_conjugateMatter_origin_zero :
    (fixedP506JointResidualSection 0).conjugateMatter = 0 := by
  change
    (fun direction =>
      diracDualConjugateMatterDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual direction 0) =
      0
  funext direction
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [fixedP506JointActual_repairedMatterVector_origin_zero]
  simp

theorem
    fixedDiracSpinZeroMatterCoordinate_diracDualRightChiralYukawa_zero
    (scalar : ExteriorBreakingScalarCarrier)
    (field : DiracExteriorMatterCarrier) :
    diracSpinZeroMatterCoordinate
        (diracDualRightChiralYukawaAction scalar field) =
      0 := by
  change
    ((su7ExteriorBasis 2).repr
      ((diracDualRightChiralYukawaAction scalar field 0).2.1))
        hyperchargeDegreeTwoIndex =
      0
  unfold diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply]
  unfold diracExteriorYukawaInternalAction internalMatterLinearAction
    exteriorYukawaInternalAction
  simp

private theorem fixedP506JointActual_diracDualMatterAlgebraic_eq_old
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual direction 0 =
      matterAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual direction 0 := by
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterAlgebraicDirectionalCoefficient
    matterAlgebraicVariationVector matterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum matterGaugeKineticSum
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin]
  simp only [map_add, Complex.add_re]
  rw [
    fixedDiracSpinZeroMatterCoordinate_diracDualRightChiralYukawa_zero,
    diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]

private theorem fixedP506JointActual_oldMatterAlgebraic_eq_current
    (direction : MatterCoordinateCarrier) :
    matterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        FixedP506JointActual direction 0 =
      matterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        FixedP506JointCurrent direction 0 := by
  have variationEquality :
      holonomicMatterVariationAlgebraicDirection
          FixedP506JointActual direction 0 =
        holonomicMatterVariationAlgebraicDirection
          FixedP506JointCurrent direction 0 := by
    funext formDirection
    unfold holonomicMatterVariationAlgebraicDirection
    rw [fixedP506JointActual_gravityConnection_eq_current,
      fixedP506JointActual_gaugeConnection_eq_current]
  have vectorEquality :
      matterAlgebraicVariationVector positiveSmoothUnifiedSource
          FixedP506JointActual direction 0 =
        matterAlgebraicVariationVector positiveSmoothUnifiedSource
          FixedP506JointCurrent direction 0 := by
    unfold matterAlgebraicVariationVector matterFieldVariationVector
    rw [fixedP506JointActual_pointField_origin_eq_current,
      variationEquality]
  unfold matterAlgebraicDirectionalCoefficient
  rw [fixedP506JointActual_pointField_origin_eq_current,
    fixedP506JointActual_conjugateMatter_eq_current, vectorEquality]

private theorem fixedP506JointActual_matterDifferentialMomentum_eq_current
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource
        FixedP506JointActual direction derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource
        FixedP506JointCurrent direction derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_coframe_eq_current,
    fixedP506JointActual_conjugateMatter_eq_current]

private theorem fixedP506JointActual_matterMomentumDivergence_eq_current
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506JointActual direction 0 =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506JointCurrent direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [fixedP506JointActual_matterDifferentialMomentum_eq_current]

private theorem fixedP506JointActual_oldMatterEuler_origin_zero
    (direction : MatterCoordinateCarrier) :
    matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        FixedP506JointActual direction 0 =
      0 := by
  unfold matterEulerLagrangeDirectionalCoefficient
  rw [fixedP506JointActual_oldMatterAlgebraic_eq_current,
    fixedP506JointActual_matterMomentumDivergence_eq_current]
  exact fixedGlobalMatterDualFullCauchy_matterEuler_origin direction

theorem fixedP506JointResidual_matter_origin_zero :
    (fixedP506JointResidualSection 0).matter = 0 := by
  change
    (fun direction =>
      diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual direction 0) =
      0
  funext direction
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [fixedP506JointActual_diracDualMatterAlgebraic_eq_old]
  exact fixedP506JointActual_oldMatterEuler_origin_zero direction

/-! ## Fixed P286 mixed-jet seam -/

private theorem fixedSourceCauchy_gaugeConnection_zero :
    positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeConnection =
      0 := by
  funext space direction
  change
    (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
      |>.gaugeConnection) (canonicalCauchySlicePoint 0 space) direction =
      0
  apply p286CoordinateEquiv.injective
  simp only [map_zero]
  change
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        (canonicalCauchySlicePoint 0 space) direction =
      0
  rw [show
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        (canonicalCauchySlicePoint 0 space) =
      c3h181U7ConnectionNormalForm
        (canonicalCauchySlicePoint 0 space) by
      unfold holonomicP286GaugeConnectionCoordinate
      rw [currentUStar_gaugeConnection_eq_currentU7]
      exact
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_connection_normalForm
          (canonicalCauchySlicePoint 0 space)]
  simp [c3h181U7ConnectionNormalForm, canonicalCauchySlicePoint,
    canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem fixedPrimitiveDiagonal_gaugeConnection_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeConnection
        (canonicalCauchySlicePoint 0 space) =
      0 := by
  have zeroSlice := congrArg
    (fun state : StageNineCauchyState => state.gaugeConnection space)
    fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeConnection
        (canonicalCauchySlicePoint 0 space) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.gaugeConnection
        space at zeroSlice
  rw [zeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState space
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState).gaugeConnection
        space =
      0
  rw [reads.2.2.2.2.1]
  have retained :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_retainsNonGravity
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState space
  rw [retained.1]
  funext direction
  change
    sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState space 0 direction =
      0
  rw [sourceGeneratedP286ActionLocalConnection_origin,
    fixedSourceCauchy_gaugeConnection_zero]
  rfl

private theorem fixedP506_deriv_along_canonicalSlice
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → V)
    (space : StageNineSpatialPoint)
    (differentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint 0 space)) :
    deriv (fun time : ℝ => field (canonicalCauchySlicePoint time space)) 0 =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection := by
  let line := fun time : ℝ =>
    time • coordinateDirection canonicalLorentzianTimeDirection +
      canonicalCauchySlicePoint 0 space
  have lineDerivative :
      HasDerivAt line
        (coordinateDirection canonicalLorentzianTimeDirection) 0 := by
    simpa [line] using
      ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const
        (coordinateDirection canonicalLorentzianTimeDirection)).add_const
          (canonicalCauchySlicePoint 0 space)
  have outerDerivative :
      HasFDerivAt field
        (fderiv ℝ field (canonicalCauchySlicePoint 0 space))
        (line 0) := by
    simpa [line] using differentiable.hasFDerivAt
  have composed := outerDerivative.comp_hasDerivAt 0 lineDerivative
  unfold fieldDirectionalDerivative
  rw [show
    (fun time : ℝ => field (canonicalCauchySlicePoint time space)) =
      field ∘ line by
        funext time
        congr 1
        ext direction
        fin_cases direction <;>
          simp [line, canonicalCauchySlicePoint,
            canonicalLorentzianTimeDirection, coordinateDirection,
            Fin.sum_univ_three]]
  exact composed.deriv

private theorem fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero
    (axis : Fin 3) (formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        0 axis.succ formDirection =
      0 := by
  let coordinate := fun point : BasePoint =>
    holonomicP286GaugeConnectionCoordinate
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      point formDirection
  have coordinateDifferentiable :
      DifferentiableAt ℝ coordinate 0 :=
    ((positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_smooth
      |>.2.2.2.2.1 formDirection).differentiable (by simp)).differentiableAt
  have coordinateDifferentiableAtSlice :
      DifferentiableAt ℝ coordinate
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
    simpa only [fixedCanonicalCauchySlicePoint_zero_zero] using
      coordinateDifferentiable
  have composed :=
    coordinateDifferentiableAtSlice.hasFDerivAt.comp
      (0 : StageNineSpatialPoint)
      (canonicalCauchySlicePoint_hasFDerivAt 0 0)
  have composedEquality :
      coordinate ∘ canonicalCauchySlicePoint 0 =
        Function.const StageNineSpatialPoint 0 := by
    funext space
    change
      p286CoordinateEquiv
          (positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeConnection
            (canonicalCauchySlicePoint 0 space) formDirection) =
        0
    rw [fixedPrimitiveDiagonal_gaugeConnection_zeroSlice]
    exact map_zero p286CoordinateEquiv
  have derivativeEquality := composed.fderiv
  rw [composedEquality, fderiv_const] at derivativeEquality
  have atAxis :=
    congrArg
      (fun derivative =>
        derivative (canonicalSpatialCoordinateDirection axis))
      derivativeEquality
  unfold p286GaugeConnectionCoordinateDerivative fieldDirectionalDerivative
  simpa [coordinate, ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection,
    fixedCanonicalCauchySlicePoint_zero_zero] using atAxis.symm

private theorem
    fixedPrimitiveDiagonal_gaugeConnection_temporalDerivative_eq_contact
    (formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        0 canonicalLorentzianTimeDirection formDirection =
      p286GaugeConnectionCoordinateDerivative
        (fixedIdentityECHessianCartanECNormalContactActual 0)
        0 canonicalLorentzianTimeDirection formDirection := by
  let globalCoordinate := fun point : BasePoint =>
    holonomicP286GaugeConnectionCoordinate
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      point formDirection
  let contactCoordinate := fun point : BasePoint =>
    holonomicP286GaugeConnectionCoordinate
      (fixedIdentityECHessianCartanECNormalContactActual 0)
      point formDirection
  have globalDifferentiable :
      DifferentiableAt ℝ globalCoordinate 0 :=
    ((positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_smooth
      |>.2.2.2.2.1 formDirection).differentiable (by simp)).differentiableAt
  have contactContDiff : ContDiff ℝ ∞ contactCoordinate := by
    simpa [contactCoordinate, holonomicP286GaugeConnectionCoordinate,
      Function.comp_def] using
      (fixedIdentityECHessianCartanECNormalContactActual_gaugeConnection_contDiff
        formDirection).comp
          ((contDiff_const : ContDiff ℝ ∞
            (fun _ : BasePoint => (0 : StageNineSpatialPoint))).prodMk
              contDiff_id)
  have contactDifferentiable : DifferentiableAt ℝ contactCoordinate 0 :=
    (contactContDiff.differentiable (by simp)).differentiableAt
  have curveEquality :
      (fun time : ℝ =>
        globalCoordinate
          (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))) =
      (fun time =>
        contactCoordinate
          (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))) := by
    funext time
    change
      p286CoordinateEquiv
          (positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeConnection
            (canonicalCauchySlicePoint time 0) formDirection) =
        p286CoordinateEquiv
          ((fixedIdentityECHessianCartanECNormalContactActual 0).gaugeConnection
            (canonicalCauchySlicePoint time 0) formDirection)
    unfold
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
    rw [primitiveDiagonalActual_gaugeConnection_slice]
    rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
  unfold p286GaugeConnectionCoordinateDerivative
  change
    fieldDirectionalDerivative globalCoordinate 0
        canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative contactCoordinate 0
        canonicalLorentzianTimeDirection
  calc
    _ =
        deriv
          (fun time : ℝ =>
            globalCoordinate
              (canonicalCauchySlicePoint time
                (0 : StageNineSpatialPoint))) 0 := by
      simpa only [fixedCanonicalCauchySlicePoint_zero_zero] using
        (fixedP506_deriv_along_canonicalSlice globalCoordinate 0
          (by simpa only [fixedCanonicalCauchySlicePoint_zero_zero] using
            globalDifferentiable)).symm
    _ =
        deriv
          (fun time : ℝ =>
            contactCoordinate
              (canonicalCauchySlicePoint time
                (0 : StageNineSpatialPoint))) 0 := by
      rw [curveEquality]
    _ = _ := by
      simpa only [fixedCanonicalCauchySlicePoint_zero_zero] using
        fixedP506_deriv_along_canonicalSlice contactCoordinate 0
          (by simpa only [fixedCanonicalCauchySlicePoint_zero_zero] using
            contactDifferentiable)

private theorem fixedSourceCauchy_spatialGaugeConnectionDerivative_zero
    (space : StageNineSpatialPoint) (axis : Fin 3)
    (formDirection : LorentzianIndex) :
    cauchyP286SpatialConnectionDerivativeCoordinate
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space axis formDirection =
      0 := by
  unfold cauchyP286SpatialConnectionDerivativeCoordinate
  have functionZero :
      (fun candidate =>
        p286CoordinateEquiv
          (positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeConnection
            candidate formDirection)) =
        fun _ => 0 := by
    funext candidate
    rw [fixedSourceCauchy_gaugeConnection_zero]
    simp
  rw [functionZero]
  simp

private theorem fixedSourceCauchy_gaugeAuxiliary_origin_eq_U7 :
    positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeAuxiliary 0 =
      (positiveP506MatterCurrentP286GaussCauchyState |>.gaugeAuxiliary)
        positiveP506MatterCurrentP286AxisContact := by
  funext pair
  apply p286CoordinateEquiv.injective
  change
    p286CoordinateEquiv
        (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeAuxiliary
          (canonicalCauchySlicePoint 0 0) pair) =
      p286CoordinateEquiv
        ((positiveP506MatterCurrentP286GaussCauchyState |>.gaugeAuxiliary)
          positiveP506MatterCurrentP286AxisContact pair)
  rw [fixedCanonicalCauchySlicePoint_zero_zero]
  calc
    _ =
        p286CoordinateEquiv
          (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeAuxiliary
            0 pair) := by
      exact congrArg p286CoordinateEquiv
        (congrFun
          positiveP506MatterCurrentUStar_gaugeAuxiliary_origin_eq_U7 pair)
    _ = _ := by
      exact congrFun currentOriginAuxiliaryCoordinate_eq_gaussCauchy pair

private theorem fixedSourceCauchy_actionGeneratedP286Curvature_eq_U7 :
    actionGeneratedP286Curvature positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState 0 =
      actionGeneratedP286Curvature positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact := by
  unfold actionGeneratedP286Curvature
  rw [fixedCurrent_coframe_one 0,
    positiveP506MatterCurrentP286GaussCauchyState_coframe_axis,
    fixedSourceCauchy_gaugeAuxiliary_origin_eq_U7]

private theorem fixedSourceCauchy_actionGeneratedP286CurvatureCoordinate_normalForm :
    (fun pair =>
      p286CoordinateEquiv
        (actionGeneratedP286Curvature positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState 0 pair)) =
      ![(c3h181StrongCouplingSquared / 3) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0, 0, 0, 0] := by
  funext pair
  rw [fixedSourceCauchy_actionGeneratedP286Curvature_eq_U7]
  exact congrFun currentActionGeneratedP286CurvatureCoordinate_normalForm pair

private theorem fixedContact_gaugeConnection_temporalDerivative_eq_jet
    (formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        (fixedIdentityECHessianCartanECNormalContactActual 0)
        0 canonicalLorentzianTimeDirection formDirection =
      sourceGeneratedP286ActionLocalConnectionJet positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState 0
        canonicalLorentzianTimeDirection formDirection := by
  have retained :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_retainsNonGravity
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState 0
  have connectionEq :
      (fixedIdentityECHessianCartanECNormalContactActual 0).gaugeConnection =
        (sourceGeneratedP286ActionLocalActualLift positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState 0
          ).gaugeConnection := by
    rw [fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
    exact retained.1
  unfold p286GaugeConnectionCoordinateDerivative
    holonomicP286GaugeConnectionCoordinate
  rw [connectionEq]
  exact
    sourceGeneratedP286ActionLocalActualLift_connectionDerivative
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState 0
      canonicalLorentzianTimeDirection formDirection

private theorem
    fixedPrimitiveDiagonal_temporalGaugeDerivative_eq_actionCurvature
    (axis : Fin 3) :
    p286GaugeConnectionCoordinateDerivative
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        0 canonicalLorentzianTimeDirection axis.succ =
      p286CoordinateEquiv
        (actionGeneratedP286Curvature positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState 0
          (temporalSpatialPair axis)) := by
  rw [
    fixedPrimitiveDiagonal_gaugeConnection_temporalDerivative_eq_contact,
    fixedContact_gaugeConnection_temporalDerivative_eq_jet]
  fin_cases axis <;>
    simp [sourceGeneratedP286ActionLocalConnectionJet,
      sourceGeneratedP286SpatialConnectionVelocity_coordinate,
      fixedSourceCauchy_spatialGaugeConnectionDerivative_zero,
      fixedSourceCauchy_gaugeConnection_zero,
      temporalSpatialPair, canonicalLorentzianTimeDirection]

private theorem fixedPrimitiveDiagonal_gaugeConnectionCoordinate_origin_zero :
    holonomicP286GaugeConnectionCoordinate
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        0 =
      0 := by
  funext direction
  unfold holonomicP286GaugeConnectionCoordinate
  rw [← fixedCanonicalCauchySlicePoint_zero_zero,
    fixedPrimitiveDiagonal_gaugeConnection_zeroSlice]
  simp

private theorem fixedPrimitiveDiagonal_gaugeCurvatureCoordinate_origin :
    holonomicP286GaugeCurvatureCoordinate
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        0 =
      fun pair =>
        p286CoordinateEquiv
          (actionGeneratedP286Curvature positiveSmoothUnifiedSource
            positiveP506MatterCurrentFullSynchronizedCauchyState 0 pair) := by
  funext pair
  rw [holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket,
    fixedPrimitiveDiagonal_gaugeConnectionCoordinate_origin_zero]
  simp only [Pi.zero_apply, p286CoordinateLieBracket_zero_left, add_zero]
  fin_cases pair
  · simp [pairFirst, pairSecond]
    have temporal :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 0 1 =
          p286CoordinateEquiv
            (actionGeneratedP286Curvature positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedCauchyState 0 0) := by
      simpa [canonicalLorentzianTimeDirection, temporalSpatialPair] using
        fixedPrimitiveDiagonal_temporalGaugeDerivative_eq_actionCurvature 0
    have spatial :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 1 0 =
          0 := by
      simpa using
        fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 0 0
    rw [temporal, spatial]
    simp
  · simp [pairFirst, pairSecond]
    have temporal :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 0 2 =
          p286CoordinateEquiv
            (actionGeneratedP286Curvature positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedCauchyState 0 1) := by
      simpa [canonicalLorentzianTimeDirection, temporalSpatialPair] using
        fixedPrimitiveDiagonal_temporalGaugeDerivative_eq_actionCurvature 1
    have spatial :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 2 0 =
          0 := by
      simpa using
        fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 1 0
    rw [temporal, spatial]
    simp
  · simp [pairFirst, pairSecond]
    have temporal :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 0 3 =
          p286CoordinateEquiv
            (actionGeneratedP286Curvature positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedCauchyState 0 2) := by
      simpa [canonicalLorentzianTimeDirection, temporalSpatialPair] using
        fixedPrimitiveDiagonal_temporalGaugeDerivative_eq_actionCurvature 2
    have spatial :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 3 0 =
          0 := by
      simpa using
        fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 2 0
    rw [temporal, spatial]
    simp
  · simp [pairFirst, pairSecond]
    have firstDerivative :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 2 3 =
          0 := by
      simpa using
        fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 1 3
    have secondDerivative :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 3 2 =
          0 := by
      simpa using
        fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 2 2
    rw [firstDerivative, secondDerivative]
    have target :=
      congrFun
        fixedSourceCauchy_actionGeneratedP286CurvatureCoordinate_normalForm 3
    simpa using target.symm
  · simp [pairFirst, pairSecond]
    have firstDerivative :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 3 1 =
          0 := by
      simpa using
        fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 2 1
    have secondDerivative :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 1 3 =
          0 := by
      simpa using
        fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 0 3
    rw [firstDerivative, secondDerivative]
    have target :=
      congrFun
        fixedSourceCauchy_actionGeneratedP286CurvatureCoordinate_normalForm 4
    simpa using target.symm
  · simp [pairFirst, pairSecond]
    have firstDerivative :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 1 2 =
          0 := by
      simpa using
        fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 0 2
    have secondDerivative :
        p286GaugeConnectionCoordinateDerivative
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            0 2 1 =
          0 := by
      simpa using
        fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 1 1
    rw [firstDerivative, secondDerivative]
    have target :=
      congrFun
        fixedSourceCauchy_actionGeneratedP286CurvatureCoordinate_normalForm 5
    simpa using target.symm

private theorem fixedPrimitiveDiagonal_gaugeCurvature_origin :
    holonomicGaugeCurvature
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        0 =
      actionGeneratedP286Curvature positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  change
    holonomicP286GaugeCurvatureCoordinate
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        0 pair =
      p286CoordinateEquiv
        (actionGeneratedP286Curvature positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState 0 pair)
  exact congrFun fixedPrimitiveDiagonal_gaugeCurvatureCoordinate_origin pair

private theorem fixedP506JointActual_gaugeConnection_eq_primitive :
    FixedP506JointActual.gaugeConnection =
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeConnection := by
  rfl

private theorem fixedP506JointActual_gaugeCurvature_origin :
    holonomicGaugeCurvature FixedP506JointActual 0 =
      actionGeneratedP286Curvature positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState 0 := by
  calc
    _ =
        holonomicGaugeCurvature
          positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
          0 := by
      exact holonomicGaugeCurvature_eq_of_connection_eq_current _ _
        fixedP506JointActual_gaugeConnection_eq_primitive 0
    _ = _ := fixedPrimitiveDiagonal_gaugeCurvature_origin

/-- The complete fixed actual retains the nonzero P286 curvature generated
by the same P506/L0 source.  This is a same-actual sector readout, not a
separate equation or repair gate. -/
theorem fixedP506JointActual_gaugeCurvature_origin_ne_zero :
    holonomicGaugeCurvature FixedP506JointActual 0 ≠ 0 := by
  rw [fixedP506JointActual_gaugeCurvature_origin,
    fixedSourceCauchy_actionGeneratedP286Curvature_eq_U7,
    ←
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_gaugeCurvature]
  exact
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_gaugeCurvature_ne_zero

private theorem fixedPrimitiveDiagonal_gaugeAuxiliary_origin_eq_sourceCauchy :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeAuxiliary
        0 =
      positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeAuxiliary 0 := by
  have zeroSlice := congrArg
    (fun state : StageNineCauchyState => state.gaugeAuxiliary 0)
    fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 0) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.gaugeAuxiliary
        0 at zeroSlice
  rw [fixedCanonicalCauchySlicePoint_zero_zero] at zeroSlice
  rw [zeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState 0
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState).gaugeAuxiliary 0 =
      positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeAuxiliary 0
  rw [reads.2.2.2.2.2.1]
  have retained :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_retainsNonGravity
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState 0
  rw [retained.2.1]
  rfl

theorem fixedP506JointActual_gaugeAuxiliary_origin_eq_sourceCauchy :
    FixedP506JointActual.gaugeAuxiliary 0 =
      positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeAuxiliary 0 := by
  have outputContact :=
    currentP286CompleteActionResponseOperator_pointField_origin
      positiveSmoothUnifiedSource FixedP506JointCurrent
  have auxiliaryContact :=
    congrArg StageNineContinuumPointField.gaugeAuxiliary outputContact
  change
    FixedP506JointActual.gaugeAuxiliary 0 =
      FixedP506JointCurrent.gaugeAuxiliary 0 at auxiliaryContact
  rw [auxiliaryContact]
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeAuxiliary
        0 =
      positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeAuxiliary 0
  exact fixedPrimitiveDiagonal_gaugeAuxiliary_origin_eq_sourceCauchy

private theorem fixedSource_formNativeP286BlockwiseConstitutive_eq_unified
    (coframe : LorentzianCoframe)
    (form : FormNativeP286GaugeTwoForm) :
    formNativeP286BlockwiseConstitutive coframe
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        form =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        form := by
  have weakEq :
      ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) := by
    rfl
  have hyperchargeEq :
      ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) := by
    rfl
  rw [weakEq, hyperchargeEq]
  funext output
  unfold formNativeP286BlockwiseConstitutive
  apply Prod.ext
  · exact
      (liftGaugeTwoFormOperator_p286_strong
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        form output).symm
  · apply Prod.ext
    · exact
        (liftGaugeTwoFormOperator_p286_weak
          (((sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear coframe)
          form output).symm
    · exact
        (liftGaugeTwoFormOperator_p286_hypercharge
          (((sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear coframe)
          form output).symm

theorem fixedP506JointResidual_p286GaugeAuxiliary_zero :
    (fixedP506JointResidualSection 0).p286GaugeAuxiliary = 0 := by
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (toContinuumPointField FixedP506JointActual 0) =
      0
  apply
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField FixedP506JointActual 0)).2
  unfold FormNativeP286GaugeAuxiliaryEquationAtBoundary
  change
    holonomicGaugeCurvature FixedP506JointActual 0 =
      formNativeP286BlockwiseConstitutive
        (FixedP506JointActual.coframe 0)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        (FixedP506JointActual.gaugeAuxiliary 0)
  rw [fixedP506JointActual_gaugeCurvature_origin,
    fixedSource_formNativeP286BlockwiseConstitutive_eq_unified,
    fixedGlobalMatterDualP286Complete_coframe_origin,
    fixedP506JointActual_gaugeAuxiliary_origin_eq_sourceCauchy]
  unfold actionGeneratedP286Curvature
  rw [fixedCurrent_coframe_one 0]

/-! This is only the fixed identity-coframe convention readout used when
comparing the historical metric coefficient with the repaired root.  It does
not decide the connection residual or select a new write by itself. -/
theorem fixedIdentityP286HodgePairing_eq_neg_topologicalWedge
    (first second : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1 first second =
      -generatedTwoFormWedgeCoefficient p286CoordinateLiePairing first
        second := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
    generatedTwoFormWedgeCoefficient
  rw [coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_id_p286]
  rw [Fin.sum_univ_six]
  simp [liftGaugeTwoFormOperator_fixedHodge_apply_local,
    lorentzianTwoFormSign, minkowskiInternalSign, twoFormComplement,
    pairFirst, pairSecond, Fin.sum_univ_six]
  ring

private theorem fixedCartanReactionContact_lorentzAdmissible
    (space : StageNineSpatialPoint) :
    GravityConnectionLorentzAdmissible
      (fixedCartanReactionContact space) := by
  apply
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_lorentzAdmissible
  rw [fixedCurrent_coframe_one]
  norm_num

private theorem
    fixedIdentityECHessianCartanECNormalContactActual_lorentzAdmissible
    (space : StageNineSpatialPoint) :
    GravityConnectionLorentzAdmissible
      (fixedIdentityECHessianCartanECNormalContactActual space) := by
  let base := fixedCartanReactionContact space
  let increment :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
      positiveSmoothUnifiedSource base
  let hessian :=
    identityECHolonomicCoframeHessianIncrementLocalActualLift base increment
  let cartan :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      positiveSmoothUnifiedSource hessian
  have baseCoframe : base.coframe = fun _ => 1 := by
    funext point
    exact fixedCartanReactionContact_coframe_one space point
  have baseConnection :
      base.gravityConnection =
        fun point =>
          diracDualFormNativeActionCartanConnectionAt
            positiveSmoothUnifiedSource base point := by
    funext point
    exact
      sourceActionGeneratedDiracDualCartanReactionLocalActualLift_connection_selfGenerated
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState space point
  have cartanOrigin :
      cartan.gravityConnection 0 = hessian.gravityConnection 0 := by
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_connection_origin
        positiveSmoothUnifiedSource base increment baseCoframe baseConnection
  have hessianOrigin :
      hessian.gravityConnection 0 = base.gravityConnection 0 := by
    exact
      identityECHolonomicCoframeHessianIncrementLocalActualLift_connection_origin
        base increment
  have originSkew : LorentzSkew (cartan.gravityConnection 0) := by
    rw [cartanOrigin, hessianOrigin]
    exact fixedCartanReactionContact_lorentzAdmissible space 0
  intro point
  change
    LorentzSkew
      (normalizedAffineLorentzConnectionField
        (cartan.gravityConnection 0)
        (diracDualFormNativeECNormalCurvatureTarget
          positiveSmoothUnifiedSource cartan) point)
  exact
    normalizedAffineLorentzConnectionField_lorentzSkew
      (cartan.gravityConnection 0)
      (diracDualFormNativeECNormalCurvatureTarget
        positiveSmoothUnifiedSource cartan)
      originSkew point

theorem fixedPrimitiveDiagonal_lorentzAdmissible :
    GravityConnectionLorentzAdmissible
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual := by
  intro point
  rw [← canonicalCauchySlicePoint_projections point]
  unfold
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
  rw [primitiveDiagonalActual_gravityConnection_slice]
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
  exact
    fixedIdentityECHessianCartanECNormalContactActual_lorentzAdmissible
      (canonicalSpatialProjection point)
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)

private theorem fixedGlobalFullCauchy_lorentzAdmissible :
    GravityConnectionLorentzAdmissible
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual := by
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_lorentzAdmissible
      positiveSmoothUnifiedSource
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      fixedPrimitiveDiagonal_lorentzAdmissible

private theorem fixedGlobalMatterDualFullCauchy_lorentzAdmissible :
    GravityConnectionLorentzAdmissible FixedP506JointCurrent := by
  apply
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_lorentzAdmissible
  intro point
  change
    LorentzSkew
      ((actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
        (actionGeneratedCurrentCoframeMatterTimeResponseActual
          positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual)
        ).gravityConnection point)
  rw [
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gravityConnection,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gravityConnection]
  exact fixedGlobalFullCauchy_lorentzAdmissible point

theorem fixedP506JointActual_lorentzAdmissible :
    GravityConnectionLorentzAdmissible FixedP506JointActual := by
  intro point
  change
    LorentzSkew
      ((currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
        FixedP506JointCurrent).gravityConnection point)
  rw [currentP286CompleteActionResponseOperator_gravityConnection]
  exact fixedGlobalMatterDualFullCauchy_lorentzAdmissible point

theorem fixedP506JointResidual_gravityMultiplier_zero
    (point : BasePoint) :
    (fixedP506JointResidualSection point).gravityMultiplier = 0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField FixedP506JointActual point) =
      0
  rw [formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity]
  change
    (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
        FixedP506JointCurrent).gravityAuxiliary point =
      physicalIIPlusBivector
        ((currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
          FixedP506JointCurrent).coframe point)
  rw [currentP286CompleteActionResponseOperator_gravityAuxiliary,
    currentP286CompleteActionResponseOperator_coframe]
  exact fixedGlobalMatterDualFullCauchy_simplicity point

private theorem fixedP506JointActual_gravityCurvature
    (point : BasePoint) :
    holonomicGravityCurvature FixedP506JointActual point =
      holonomicGravityCurvature FixedP506JointCurrent point := by
  have connectionEq :
      FixedP506JointActual.gravityConnection =
        FixedP506JointCurrent.gravityConnection := by
    exact currentP286CompleteActionResponseOperator_gravityConnection
      positiveSmoothUnifiedSource FixedP506JointCurrent
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [connectionEq]

theorem fixedP506JointResidual_gravityAuxiliary_zero
    (point : BasePoint) :
    (fixedP506JointResidualSection point).gravityAuxiliary = 0 := by
  have baseZero :=
    congrFun fixedGlobalMatterDualFullCauchy_auxiliaryEquation point
  change
    formNativeGravityAuxiliaryEulerResidual
        (toContinuumPointField
          positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
          point) =
      0 at baseZero
  change
    formNativeGravityAuxiliaryEulerResidual
        (toContinuumPointField FixedP506JointActual point) =
      0
  unfold formNativeGravityAuxiliaryEulerResidual
  change
    gravityInternalPairVarianceNormalization
          (holonomicGravityCurvature FixedP506JointActual point) -
        gravityInternalDualEquiv
          (FixedP506JointActual.gravityAuxiliary point) +
      FixedP506JointActual.gravitySimplicityMultiplier point =
    0
  rw [fixedP506JointActual_gravityCurvature]
  change
    gravityInternalPairVarianceNormalization
          (holonomicGravityCurvature FixedP506JointCurrent point) -
        gravityInternalDualEquiv
          ((currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
            FixedP506JointCurrent).gravityAuxiliary point) +
      (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
        FixedP506JointCurrent).gravitySimplicityMultiplier point =
    0
  rw [currentP286CompleteActionResponseOperator_gravityAuxiliary,
    currentP286CompleteActionResponseOperator_multiplier]
  exact baseZero

private theorem fixedP506JointCurrent_restrictToIIPlus :
    restrictHolonomicConfigurationToIIPlus FixedP506JointCurrent =
      FixedP506JointCurrent := by
  exact
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      FixedP506JointCurrent).2 fixedGlobalMatterDualFullCauchy_simplicity

private theorem fixedP506JointCurrent_lorentzResidual_origin_zero :
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506JointCurrent 0 =
      0 := by
  apply
    (holonomicFormNativeLorentzEulerThreeForm_eq_zero_iff_current
      positiveSmoothUnifiedSource 0 FixedP506JointCurrent 0).2
  calc
    holonomicGravityAuxiliaryExteriorCovariantDerivative FixedP506JointCurrent
          0 =
        holonomicGravityAuxiliaryExteriorCovariantDerivative
          (restrictHolonomicConfigurationToIIPlus FixedP506JointCurrent) 0 := by
      rw [fixedP506JointCurrent_restrictToIIPlus]
    _ =
        internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (FixedP506JointCurrent.coframe 0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt FixedP506JointCurrent.coframe 0)
              (FixedP506JointCurrent.gravityConnection 0))) :=
      holonomicGravityAuxiliaryExteriorCovariantDerivative_restrictToIIPlus_eq_torsionCoframe
        FixedP506JointCurrent fixedGlobalMatterDualFullCauchy_smooth
        fixedGlobalMatterDualFullCauchy_lorentzAdmissible 0
    _ =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus FixedP506JointCurrent)
            0) :=
      fixedGlobalMatterDualFullCauchy_torsionSpin_origin
    _ =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField FixedP506JointCurrent 0) := by
      rw [fixedP506JointCurrent_restrictToIIPlus]

private theorem fixedP506JointActual_lorentzEuler_origin_eq_current :
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506JointActual 0 =
      holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506JointCurrent 0 := by
  have geometric :
      holonomicGravityAuxiliaryExteriorCovariantDerivative
          FixedP506JointActual 0 =
        holonomicGravityAuxiliaryExteriorCovariantDerivative
          FixedP506JointCurrent 0 := by
    unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
      holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
    change
      pointwisePhysicalBivectorExteriorCovariantDerivative
          ((currentP286CompleteActionResponseOperator
            positiveSmoothUnifiedSource FixedP506JointCurrent
            ).gravityConnection 0)
          { value :=
              (currentP286CompleteActionResponseOperator
                positiveSmoothUnifiedSource FixedP506JointCurrent
                ).gravityAuxiliary 0
            derivative := fun direction =>
              fieldDirectionalDerivative
                (currentP286CompleteActionResponseOperator
                  positiveSmoothUnifiedSource FixedP506JointCurrent
                  ).gravityAuxiliary 0 direction } =
        pointwisePhysicalBivectorExteriorCovariantDerivative
          (FixedP506JointCurrent.gravityConnection 0)
          { value := FixedP506JointCurrent.gravityAuxiliary 0
            derivative := fun direction =>
              fieldDirectionalDerivative FixedP506JointCurrent.gravityAuxiliary
                0 direction }
    rw [currentP286CompleteActionResponseOperator_gravityConnection,
      currentP286CompleteActionResponseOperator_gravityAuxiliary]
  have pointField :
      toContinuumPointField FixedP506JointActual 0 =
        toContinuumPointField FixedP506JointCurrent 0 := by
    change
      toContinuumPointField
          (currentP286CompleteActionResponseOperator
            positiveSmoothUnifiedSource FixedP506JointCurrent) 0 =
        toContinuumPointField FixedP506JointCurrent 0
    exact
      currentP286CompleteActionResponseOperator_pointField_origin
        positiveSmoothUnifiedSource FixedP506JointCurrent
  unfold holonomicFormNativeLorentzEulerThreeForm
  rw [geometric, pointField]

theorem fixedP506JointResidual_lorentzConnection_origin_zero :
    (fixedP506JointResidualSection 0).lorentzConnection = 0 := by
  change
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506JointActual 0 =
      0
  rw [fixedP506JointActual_lorentzEuler_origin_eq_current]
  exact fixedP506JointCurrent_lorentzResidual_origin_zero

/-! ## Scalar coordinate of the same complete carrier

The comparison below freezes only the coframe in a proof-only readout.  The
fixed current and the comparison have the same coframe value and first jet at
the common contact, so their scalar momenta have the same divergence there.
This is one coordinate computation of `fixedP506JointResidualSection`; it is
not a scalar-only repair epoch or a new completion gate. -/

open scoped Matrix.Norms.Elementwise

open StageNineDiracDualFormNativeScalarVariation
open StageNineScalarPointwiseEquation
open StageNineScalarVariation

private theorem fixedP506JointCurrent_scalar_eq_primitive :
    FixedP506JointCurrent.scalar =
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.scalar := by
  rfl

private theorem fixedPrimitiveDiagonal_scalar_vacuum_global :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  funext point
  calc
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.scalar
          (canonicalCauchySlicePoint
            (canonicalTimeProjection point)
            (canonicalSpatialProjection point)) := by
      rw [canonicalCauchySlicePoint_projections]
    _ =
        (fixedIdentityECHessianCartanECNormalContactActual
          (canonicalSpatialProjection point)).scalar
            (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) := by
      change
        (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState).scalar
            (canonicalCauchySlicePoint
              (canonicalTimeProjection point)
              (canonicalSpatialProjection point)) =
          _
      rw [primitiveDiagonalActual_scalar_slice]
      rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
    _ = sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource :=
      congrFun
        (fixedIdentityECHessianCartanECNormalContactActual_scalar_vacuum
          (canonicalSpatialProjection point))
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)

private theorem fixedP506JointCurrent_scalar_vacuum :
    FixedP506JointCurrent.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  rw [fixedP506JointCurrent_scalar_eq_primitive,
    fixedPrimitiveDiagonal_scalar_vacuum_global]

private theorem fixedP506JointCurrent_gaugeConnection_eq_primitive :
    FixedP506JointCurrent.gaugeConnection =
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gaugeConnection := by
  rfl

private theorem
    fixedP506JointCurrent_gaugeConnectionCoordinate_origin_zero :
    holonomicP286GaugeConnectionCoordinate FixedP506JointCurrent 0 = 0 := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [fixedP506JointCurrent_gaugeConnection_eq_primitive]
  exact fixedPrimitiveDiagonal_gaugeConnectionCoordinate_origin_zero

private theorem
    fixedP506JointCurrent_gaugeConnectionCoordinate_diagonalDerivative_zero
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeConnectionCoordinate
            FixedP506JointCurrent point direction)
        0 direction =
      0 := by
  have coordinateEquality :
      (fun point =>
        holonomicP286GaugeConnectionCoordinate
          FixedP506JointCurrent point direction) =
        fun point =>
          holonomicP286GaugeConnectionCoordinate
            positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
            point direction := by
    funext point
    unfold holonomicP286GaugeConnectionCoordinate
    rw [fixedP506JointCurrent_gaugeConnection_eq_primitive]
  rw [coordinateEquality]
  change
    p286GaugeConnectionCoordinateDerivative
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        0 direction direction =
      0
  fin_cases direction
  · have temporal :=
      fixedPrimitiveDiagonal_gaugeConnection_temporalDerivative_eq_contact 0
    rw [fixedContact_gaugeConnection_temporalDerivative_eq_jet] at temporal
    simpa [sourceGeneratedP286ActionLocalConnectionJet,
      canonicalLorentzianTimeDirection] using temporal
  · simpa using
      fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 0 1
  · simpa using
      fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 1 2
  · simpa using
      fixedPrimitiveDiagonal_gaugeConnection_spatialDerivative_zero 2 3

private theorem
    fixedP506JointCurrent_scalarCovariantDerivative_eq_fixedVacuumAction
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative FixedP506JointCurrent point direction =
      scalarP286ActionBilinear
        (holonomicP286GaugeConnectionCoordinate
          FixedP506JointCurrent point direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  unfold holonomicScalarCovariantDerivative
  rw [fixedP506JointCurrent_scalar_vacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add]
  unfold holonomicP286GaugeConnectionCoordinate
  change
    scalarMotherLieAction
        (p286LieBlockEmbed
          (FixedP506JointCurrent.gaugeConnection point direction))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (p286CoordinateEquiv
              (FixedP506JointCurrent.gaugeConnection point direction))))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
  rw [p286CoordinateEquiv.symm_apply_apply]

private theorem fixedP506JointCurrent_scalarCovariantDerivative_origin_zero
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative FixedP506JointCurrent 0 direction =
      0 := by
  rw [
    fixedP506JointCurrent_scalarCovariantDerivative_eq_fixedVacuumAction,
    congrFun fixedP506JointCurrent_gaugeConnectionCoordinate_origin_zero
      direction]
  simp

private theorem
    fixedP506JointCurrent_scalarCovariantDerivative_directionalDerivative
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicScalarCovariantDerivative FixedP506JointCurrent point
            formDirection)
        0 derivativeDirection =
      scalarP286ActionBilinear
        (fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeConnectionCoordinate
              FixedP506JointCurrent point formDirection)
          0 derivativeDirection)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  let connection := fun point =>
    holonomicP286GaugeConnectionCoordinate
      FixedP506JointCurrent point formDirection
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 := by
    have smooth :=
      fixedGlobalMatterDualFullCauchy_smooth |>.2.2.2.2.1 formDirection
    simpa [connection, holonomicP286GaugeConnectionCoordinate] using
      (smooth.differentiable (by simp)).differentiableAt
  have actionDerivative :
      fderiv ℝ
          (fun point =>
            action (connection point)
              (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
          0 =
        (action.flip
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).comp
            (fderiv ℝ connection 0) :=
    ((action.flip
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
        ).hasFDerivAt.comp 0 connectionDifferentiable.hasFDerivAt).fderiv
  rw [show
      (fun point =>
        holonomicScalarCovariantDerivative FixedP506JointCurrent point
          formDirection) =
        fun point =>
          action (connection point)
            (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) by
      funext point
      exact
        fixedP506JointCurrent_scalarCovariantDerivative_eq_fixedVacuumAction
          point formDirection]
  unfold fieldDirectionalDerivative
  rw [actionDerivative]
  rfl

private theorem
    fixedP506JointCurrent_scalarCovariantDerivative_diagonalDerivative_zero
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicScalarCovariantDerivative FixedP506JointCurrent point
            direction)
        0 direction =
      0 := by
  rw [
    fixedP506JointCurrent_scalarCovariantDerivative_directionalDerivative,
    fixedP506JointCurrent_gaugeConnectionCoordinate_diagonalDerivative_zero]
  simp

private theorem fixedP506JointActual_scalar_eq_current :
    FixedP506JointActual.scalar = FixedP506JointCurrent.scalar :=
  currentP286CompleteActionResponseOperator_scalar
    positiveSmoothUnifiedSource FixedP506JointCurrent

theorem fixedP506JointActual_adjointActionLaw :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
      FixedP506JointActual 0
      (holonomicConjugateMatterDerivativeDual FixedP506JointActual 0
        canonicalLorentzianTimeDirection) := by
  have derivativeEq (direction : LorentzianIndex) :
      holonomicConjugateMatterDerivativeDual
          FixedP506JointActual 0 direction =
        holonomicConjugateMatterDerivativeDual
          FixedP506JointCurrent 0 direction := by
    unfold holonomicConjugateMatterDerivativeDual
      holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates
    rw [fixedP506JointActual_conjugateMatter_eq_current]
  have spatialTransportEq :
      holonomicIdentityCoframeConjugateMatterSpatialTransport
          FixedP506JointActual 0 =
        holonomicIdentityCoframeConjugateMatterSpatialTransport
          FixedP506JointCurrent 0 := by
    unfold holonomicIdentityCoframeConjugateMatterSpatialTransport
    simp_rw [derivativeEq]
  have connectionOperatorEq :
      holonomicIdentityCoframeMatterConnectionOperator
          FixedP506JointActual 0 =
        holonomicIdentityCoframeMatterConnectionOperator
          FixedP506JointCurrent 0 := by
    funext direction
    unfold holonomicIdentityCoframeMatterConnectionOperator
    rw [fixedP506JointActual_gravityConnection_eq_current,
      fixedP506JointActual_gaugeConnection_eq_current]
  have algebraicOperatorEq :
      holonomicIdentityCoframeMatterAlgebraicOperator
          FixedP506JointActual 0 =
        holonomicIdentityCoframeMatterAlgebraicOperator
          FixedP506JointCurrent 0 := by
    unfold holonomicIdentityCoframeMatterAlgebraicOperator
    rw [connectionOperatorEq, fixedP506JointActual_scalar_eq_current]
  have law := fixedGlobalMatterDualFullCauchy_adjointActionLaw
  unfold HolonomicIdentityCoframeConjugateMatterTimeActionLaw at law ⊢
  rw [derivativeEq, spatialTransportEq,
    congrFun fixedP506JointActual_conjugateMatter_eq_current 0,
    algebraicOperatorEq]
  exact law

/-- The fixed joint actual keeps the globally generated scalar vacuum of the
same source lineage. -/
theorem fixedP506JointActual_scalar_vacuum :
    FixedP506JointActual.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  rw [fixedP506JointActual_scalar_eq_current,
    fixedP506JointCurrent_scalar_vacuum]

private theorem fixedP506JointActual_diracDualScalarAlgebraic_eq_old
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual direction 0 =
      scalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual direction 0 := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarAlgebraicDirectionalCoefficient
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
    scalarYukawaFirstVariationDensity scalarYukawaVariationVector
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin]
  rw [
    fixedDiracSpinZeroMatterCoordinate_diracDualRightChiralYukawa_zero,
    diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]

private theorem fixedP506JointActual_scalarDifferentialMomentum_eq_current
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        FixedP506JointActual direction derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource
        FixedP506JointCurrent direction derivativeDirection := by
  have scalarCovariant :
      holonomicScalarCovariantDerivative FixedP506JointActual =
        holonomicScalarCovariantDerivative FixedP506JointCurrent := by
    funext point formDirection
    unfold holonomicScalarCovariantDerivative
    rw [fixedP506JointActual_scalar_eq_current,
      fixedP506JointActual_gaugeConnection_eq_current]
  funext point
  unfold scalarDifferentialMomentum generatedVolumeDensity
    scalarGaugeConnectionKineticFirstVariationDensity
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_coframe_eq_current, scalarCovariant]

private theorem fixedP506JointActual_scalarMomentumDivergence_eq_current
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506JointActual direction 0 =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506JointCurrent direction 0 := by
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [fixedP506JointActual_scalarDifferentialMomentum_eq_current]

private theorem fixedP506JointActual_oldScalarAlgebraic_eq_current
    (direction : ScalarCoordinateCarrier) :
    scalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        FixedP506JointActual direction 0 =
      scalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        FixedP506JointCurrent direction 0 := by
  have variationEquality :
      holonomicScalarVariationAlgebraicDirection FixedP506JointActual
          direction 0 =
        holonomicScalarVariationAlgebraicDirection FixedP506JointCurrent
          direction 0 := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rw [fixedP506JointActual_gaugeConnection_eq_current]
  unfold scalarAlgebraicDirectionalCoefficient
  rw [fixedP506JointActual_pointField_origin_eq_current, variationEquality]

private def fixedP506JointCurrentScalarMomentumPointCoframe
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (joint : BasePoint × LorentzianCoframe) : ℝ :=
  abs (Matrix.det joint.2) *
    scalarGaugeConnectionKineticFirstVariationDensity
      positiveSmoothUnifiedSource 0 joint.1
      (StageNineCoframeVariation.withCoframe
        (toContinuumPointField FixedP506JointCurrent joint.1) joint.2)
      (scalarVariationDifferentialDirection direction derivativeDirection)

private theorem fixedP506JointCurrentScalarMomentumPointCoframe_contDiffAt
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fixedP506JointCurrentScalarMomentumPointCoframe direction
        derivativeDirection)
      (0, 1) := by
  have volumeSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        abs (Matrix.det joint.2)) (0, 1) :=
    (StageNineCoframeVariation.coframe_volume_contDiffAt
      (1 : LorentzianCoframe)
      (by norm_num)).comp (0, 1) contDiffAt_snd
  have metricOuter : ContDiffAt ℝ ∞
      (fun coframe : LorentzianCoframe =>
        (lorentzianMetricOfCoframe coframe)⁻¹) 1 :=
    StageNineCoframeLocalDifferentiability.lorentzianMetric_inv_contDiffAt
      (1 : LorentzianCoframe) (by norm_num)
  have metricSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        (lorentzianMetricOfCoframe joint.2)⁻¹) (0, 1) := by
    rw [show
      (fun joint : BasePoint × LorentzianCoframe =>
        (lorentzianMetricOfCoframe joint.2)⁻¹) =
        (fun coframe : LorentzianCoframe =>
          (lorentzianMetricOfCoframe coframe)⁻¹) ∘
          (fun joint : BasePoint × LorentzianCoframe => joint.2) by
      rfl]
    exact metricOuter.comp (0, 1)
      (show ContDiffAt ℝ ∞
        (fun joint : BasePoint × LorentzianCoframe => joint.2) (0, 1) from
        contDiffAt_snd)
  have covariantSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun joint : BasePoint × LorentzianCoframe =>
        holonomicScalarCovariantDerivative FixedP506JointCurrent joint.1
          formDirection :=
    (StageNineCoframeScalarMatterRegularity.holonomicScalarCovariantDerivative_contDiff_local
      FixedP506JointCurrent fixedGlobalMatterDualFullCauchy_smooth
      formDirection).comp contDiff_fst
  have variationSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun _ : BasePoint × LorentzianCoframe =>
        scalarVariationDifferentialDirection direction derivativeDirection
          formDirection :=
    contDiff_const
  unfold fixedP506JointCurrentScalarMomentumPointCoframe
    scalarGaugeConnectionKineticFirstVariationDensity
  simp only [StageNineCoframeVariation.withCoframe,
    scalarFrameRelativeCovariantDerivative,
    scalarFrameRelativeCoordinates_zeroChart]
  apply volumeSmooth.mul
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro first _
  apply ContDiffAt.sum
  intro second _
  apply
    (contDiffAt_pi.mp (contDiffAt_pi.mp metricSmooth first) second).mul
  exact
    ((StageNineCoframeScalarMatterRegularity.scalarCoordinatePairingRe_joint_contDiff_local
      _ _
      (variationSmooth first) (covariantSmooth second)).add
      (StageNineCoframeScalarMatterRegularity.scalarCoordinatePairingRe_joint_contDiff_local
        _ _
        (covariantSmooth first) (variationSmooth second))).contDiffAt

private theorem
    fixedP506JointCurrent_scalarDifferentialMomentum_eq_pointCoframe
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        FixedP506JointCurrent direction derivativeDirection =
      fixedP506JointCurrentScalarMomentumPointCoframe direction
          derivativeDirection ∘
        fun point => (point, FixedP506JointCurrent.coframe point) := by
  funext point
  unfold scalarDifferentialMomentum
    fixedP506JointCurrentScalarMomentumPointCoframe generatedVolumeDensity
  simp only [Function.comp_apply, StageNineCoframeVariation.withCoframe,
    toContinuumPointField]

private abbrev FixedP506JointCurrentIdentityCoframeComparison :
    StageNineHolonomicConfiguration :=
  identityCoframeComparison FixedP506JointCurrent

private theorem
    fixedP506JointComparison_scalarDifferentialMomentum_eq_pointCoframe
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        FixedP506JointCurrentIdentityCoframeComparison direction
          derivativeDirection =
      fixedP506JointCurrentScalarMomentumPointCoframe direction
          derivativeDirection ∘
        fun point => (point, (1 : LorentzianCoframe)) := by
  funext point
  unfold scalarDifferentialMomentum
    fixedP506JointCurrentScalarMomentumPointCoframe generatedVolumeDensity
    FixedP506JointCurrentIdentityCoframeComparison
    identityCoframeComparison
  simp only [Function.comp_apply, StageNineCoframeVariation.withCoframe,
    toContinuumPointField]
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarCovariantDerivative
  rfl

private def fixedP506JointCurrentCoordinateAxis
    (direction : LorentzianIndex) : ℝ → BasePoint :=
  fun parameter => parameter • coordinateDirection direction

private theorem fixedP506JointCurrentCoordinateAxis_hasDerivAt
    (direction : LorentzianIndex) :
    HasDerivAt (fixedP506JointCurrentCoordinateAxis direction)
      (coordinateDirection direction) 0 := by
  let line :=
    fun parameter : ℝ =>
      parameter • coordinateDirection direction
  change HasDerivAt line (coordinateDirection direction) 0
  simpa [line] using
    (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
      (coordinateDirection direction)

private theorem fixedP506JointCurrent_coframe_fderiv_coordinate_zero
    (direction : LorentzianIndex) :
    (fderiv ℝ FixedP506JointCurrent.coframe 0)
        (coordinateDirection direction) =
      0 := by
  have coframeDifferentiable :
      DifferentiableAt ℝ FixedP506JointCurrent.coframe 0 :=
    ((StageNineCoframeHolonomicRegularity.holonomicCoframe_contDiff
      FixedP506JointCurrent fixedGlobalMatterDualFullCauchy_smooth
      ).differentiable (by simp)).differentiableAt
  ext internal coordinate
  let evaluation : LorentzianCoframe →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate :
        (LorentzianIndex → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj internal :
        LorentzianCoframe →L[ℝ] (LorentzianIndex → ℝ))
  have evaluatedDerivative :
      HasFDerivAt
        (fun point : BasePoint =>
          evaluation (FixedP506JointCurrent.coframe point))
        (evaluation.comp
          (fderiv ℝ FixedP506JointCurrent.coframe 0)) 0 :=
    evaluation.hasFDerivAt.comp 0 coframeDifferentiable.hasFDerivAt
  have componentDerivativeZero :=
    congrArg
      (fun jet => jet.derivative direction internal coordinate)
      fixedGlobalMatterDualFullCauchy_coframeFirstJet_origin
  have evaluatedFunctionEquality :
      (fun point : BasePoint =>
        evaluation (FixedP506JointCurrent.coframe point)) =
      (fun point : BasePoint =>
        FixedP506JointCurrent.coframe point internal coordinate) := by
    funext point
    rfl
  have evaluatedZero :
      (fderiv ℝ
        (fun point : BasePoint =>
          evaluation (FixedP506JointCurrent.coframe point)) 0)
          (coordinateDirection direction) =
        0 := by
    rw [evaluatedFunctionEquality]
    simpa [holonomicCoframeFirstJetAt, fieldDirectionalDerivative] using
      componentDerivativeZero
  rw [evaluatedDerivative.fderiv] at evaluatedZero
  change
    evaluation
        ((fderiv ℝ FixedP506JointCurrent.coframe 0)
          (coordinateDirection direction)) =
      0 at evaluatedZero
  exact evaluatedZero

theorem fixedP506JointActual_coframe_origin_one :
    FixedP506JointActual.coframe 0 = 1 := by
  rw [fixedP506JointActual_coframe_eq_current]
  exact fixedGlobalMatterDualFullCauchy_coframe_origin

theorem fixedP506JointActual_coframe_fderiv_coordinate_zero
    (direction : LorentzianIndex) :
    (fderiv ℝ FixedP506JointActual.coframe 0)
        (coordinateDirection direction) =
      0 := by
  rw [fixedP506JointActual_coframe_eq_current]
  exact fixedP506JointCurrent_coframe_fderiv_coordinate_zero direction

theorem fixedP506JointActual_coframe_differentiableAt :
    DifferentiableAt ℝ FixedP506JointActual.coframe 0 := by
  rw [fixedP506JointActual_coframe_eq_current]
  exact
    ((StageNineCoframeHolonomicRegularity.holonomicCoframe_contDiff
      FixedP506JointCurrent fixedGlobalMatterDualFullCauchy_smooth
      ).differentiable (by simp)).differentiableAt

private theorem fixedP506JointCurrent_coframeAxis_hasDerivAt_zero
    (direction : LorentzianIndex) :
    HasDerivAt
      (fun parameter =>
        FixedP506JointCurrent.coframe
          (fixedP506JointCurrentCoordinateAxis direction parameter))
      0 0 := by
  have coframeDifferentiable :
      DifferentiableAt ℝ FixedP506JointCurrent.coframe 0 :=
    ((StageNineCoframeHolonomicRegularity.holonomicCoframe_contDiff
      FixedP506JointCurrent fixedGlobalMatterDualFullCauchy_smooth
      ).differentiable (by simp)).differentiableAt
  have coframeOuter :
      HasFDerivAt FixedP506JointCurrent.coframe
        (fderiv ℝ FixedP506JointCurrent.coframe 0)
        (fixedP506JointCurrentCoordinateAxis direction 0) := by
    simpa [fixedP506JointCurrentCoordinateAxis] using
      coframeDifferentiable.hasFDerivAt
  have composed :=
    coframeOuter.comp_hasDerivAt 0
      (fixedP506JointCurrentCoordinateAxis_hasDerivAt direction)
  have derivativeZero :
      (fderiv ℝ FixedP506JointCurrent.coframe 0)
          (coordinateDirection direction) =
        0 :=
    fixedP506JointCurrent_coframe_fderiv_coordinate_zero direction
  apply composed.congr_deriv
  exact derivativeZero

private def fixedP506JointCurrentActualPointCoframeAxis
    (direction : LorentzianIndex) :
    ℝ → BasePoint × LorentzianCoframe :=
  fun parameter =>
    let point := fixedP506JointCurrentCoordinateAxis direction parameter
    (point, FixedP506JointCurrent.coframe point)

private def fixedP506JointCurrentFrozenPointCoframeAxis
    (direction : LorentzianIndex) :
    ℝ → BasePoint × LorentzianCoframe :=
  fun parameter =>
    (fixedP506JointCurrentCoordinateAxis direction parameter,
      (1 : LorentzianCoframe))

private theorem fixedP506JointCurrentActualPointCoframeAxis_hasDerivAt
    (direction : LorentzianIndex) :
    HasDerivAt (fixedP506JointCurrentActualPointCoframeAxis direction)
      (coordinateDirection direction, 0) 0 := by
  exact
    (fixedP506JointCurrentCoordinateAxis_hasDerivAt direction).prodMk
      (fixedP506JointCurrent_coframeAxis_hasDerivAt_zero direction)

private theorem fixedP506JointCurrentFrozenPointCoframeAxis_hasDerivAt
    (direction : LorentzianIndex) :
    HasDerivAt (fixedP506JointCurrentFrozenPointCoframeAxis direction)
      (coordinateDirection direction, 0) 0 := by
  exact
    (fixedP506JointCurrentCoordinateAxis_hasDerivAt direction).prodMk
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : LorentzianCoframe)))

private theorem
    fixedP506JointCurrent_scalarMomentumDerivative_eq_comparison
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          FixedP506JointCurrent direction derivativeDirection)
        0 derivativeDirection =
      fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          FixedP506JointCurrentIdentityCoframeComparison direction
            derivativeDirection)
        0 derivativeDirection := by
  let outer :=
    fixedP506JointCurrentScalarMomentumPointCoframe direction
      derivativeDirection
  have outerDerivative :
      HasFDerivAt outer (fderiv ℝ outer (0, 1)) (0, 1) :=
    ((fixedP506JointCurrentScalarMomentumPointCoframe_contDiffAt
      direction derivativeDirection).differentiableAt
        (by simp)).hasFDerivAt
  have actualAxisOrigin :
      fixedP506JointCurrentActualPointCoframeAxis derivativeDirection 0 =
        (0, 1) := by
    simp [fixedP506JointCurrentActualPointCoframeAxis,
      fixedP506JointCurrentCoordinateAxis,
      fixedGlobalMatterDualFullCauchy_coframe_origin]
  have outerAtActual :
      HasFDerivAt outer (fderiv ℝ outer (0, 1))
        (fixedP506JointCurrentActualPointCoframeAxis derivativeDirection
          0) := by
    simpa only [actualAxisOrigin] using outerDerivative
  have generatedActualAxis :=
    outerAtActual.comp_hasDerivAt 0
      (fixedP506JointCurrentActualPointCoframeAxis_hasDerivAt
        derivativeDirection)
  have frozenAxisOrigin :
      fixedP506JointCurrentFrozenPointCoframeAxis derivativeDirection 0 =
        (0, 1) := by
    simp [fixedP506JointCurrentFrozenPointCoframeAxis,
      fixedP506JointCurrentCoordinateAxis]
  have outerAtFrozen :
      HasFDerivAt outer (fderiv ℝ outer (0, 1))
        (fixedP506JointCurrentFrozenPointCoframeAxis derivativeDirection
          0) := by
    simpa only [frozenAxisOrigin] using outerDerivative
  have generatedFrozenAxis :=
    outerAtFrozen.comp_hasDerivAt 0
      (fixedP506JointCurrentFrozenPointCoframeAxis_hasDerivAt
        derivativeDirection)
  have actualAxisFunctionEquality :
      (scalarDifferentialMomentum positiveSmoothUnifiedSource
          FixedP506JointCurrent direction derivativeDirection) ∘
          fixedP506JointCurrentCoordinateAxis derivativeDirection =
        outer ∘
          fixedP506JointCurrentActualPointCoframeAxis
            derivativeDirection := by
    funext parameter
    have read :=
      congrFun
        (fixedP506JointCurrent_scalarDifferentialMomentum_eq_pointCoframe
          direction derivativeDirection)
        (fixedP506JointCurrentCoordinateAxis derivativeDirection parameter)
    simpa only [Function.comp_apply, outer,
      fixedP506JointCurrentActualPointCoframeAxis] using read
  have comparisonAxisFunctionEquality :
      (scalarDifferentialMomentum positiveSmoothUnifiedSource
          FixedP506JointCurrentIdentityCoframeComparison direction
            derivativeDirection) ∘
          fixedP506JointCurrentCoordinateAxis derivativeDirection =
        outer ∘
          fixedP506JointCurrentFrozenPointCoframeAxis
            derivativeDirection := by
    funext parameter
    have read :=
      congrFun
        (fixedP506JointComparison_scalarDifferentialMomentum_eq_pointCoframe
          direction derivativeDirection)
        (fixedP506JointCurrentCoordinateAxis derivativeDirection parameter)
    simpa only [Function.comp_apply, outer,
      fixedP506JointCurrentFrozenPointCoframeAxis] using read
  have actualDifferentiable :
      DifferentiableAt ℝ
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          FixedP506JointCurrent direction derivativeDirection) 0 := by
    rw [fixedP506JointCurrent_scalarDifferentialMomentum_eq_pointCoframe]
    have outerAtCurrent :
        DifferentiableAt ℝ outer (0, FixedP506JointCurrent.coframe 0) := by
      simpa only [fixedGlobalMatterDualFullCauchy_coframe_origin] using
        outerDerivative.differentiableAt
    exact
      outerAtCurrent.comp 0
        (differentiableAt_id.prodMk
          ((StageNineCoframeHolonomicRegularity.holonomicCoframe_contDiff
            FixedP506JointCurrent fixedGlobalMatterDualFullCauchy_smooth
            ).differentiable (by simp)).differentiableAt)
  have comparisonDifferentiable :
      DifferentiableAt ℝ
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          FixedP506JointCurrentIdentityCoframeComparison direction
            derivativeDirection)
        0 := by
    rw [
      fixedP506JointComparison_scalarDifferentialMomentum_eq_pointCoframe]
    exact outerDerivative.differentiableAt.comp 0
      (differentiableAt_id.prodMk
        (differentiableAt_const (c := (1 : LorentzianCoframe))))
  have actualMomentumOuter :
      HasFDerivAt
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          FixedP506JointCurrent direction derivativeDirection)
        (fderiv ℝ
          (scalarDifferentialMomentum positiveSmoothUnifiedSource
            FixedP506JointCurrent direction derivativeDirection) 0)
        (fixedP506JointCurrentCoordinateAxis derivativeDirection 0) := by
    simpa [fixedP506JointCurrentCoordinateAxis] using
      actualDifferentiable.hasFDerivAt
  have actualCoordinateDerivative :=
    actualMomentumOuter.comp_hasDerivAt 0
      (fixedP506JointCurrentCoordinateAxis_hasDerivAt derivativeDirection)
  have comparisonMomentumOuter :
      HasFDerivAt
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          FixedP506JointCurrentIdentityCoframeComparison direction
            derivativeDirection)
        (fderiv ℝ
          (scalarDifferentialMomentum positiveSmoothUnifiedSource
            FixedP506JointCurrentIdentityCoframeComparison direction
              derivativeDirection) 0)
        (fixedP506JointCurrentCoordinateAxis derivativeDirection 0) := by
    simpa [fixedP506JointCurrentCoordinateAxis] using
      comparisonDifferentiable.hasFDerivAt
  have comparisonCoordinateDerivative :=
    comparisonMomentumOuter.comp_hasDerivAt 0
      (fixedP506JointCurrentCoordinateAxis_hasDerivAt derivativeDirection)
  have actualCoordinateDerivative' :
      HasDerivAt
        (outer ∘
          fixedP506JointCurrentActualPointCoframeAxis derivativeDirection)
        (fieldDirectionalDerivative
          (scalarDifferentialMomentum positiveSmoothUnifiedSource
            FixedP506JointCurrent direction derivativeDirection)
          0 derivativeDirection)
        0 := by
    rw [← actualAxisFunctionEquality]
    exact actualCoordinateDerivative
  have comparisonCoordinateDerivative' :
      HasDerivAt
        (outer ∘
          fixedP506JointCurrentFrozenPointCoframeAxis derivativeDirection)
        (fieldDirectionalDerivative
          (scalarDifferentialMomentum positiveSmoothUnifiedSource
            FixedP506JointCurrentIdentityCoframeComparison direction
              derivativeDirection)
          0 derivativeDirection)
        0 := by
    rw [← comparisonAxisFunctionEquality]
    exact comparisonCoordinateDerivative
  exact
    (actualCoordinateDerivative'.unique generatedActualAxis).trans
      (comparisonCoordinateDerivative'.unique generatedFrozenAxis).symm

private theorem
    fixedP506JointCurrent_scalarMomentumDivergence_eq_comparison
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506JointCurrent direction 0 =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506JointCurrentIdentityCoframeComparison direction 0 := by
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact
    fixedP506JointCurrent_scalarMomentumDerivative_eq_comparison
      direction derivativeDirection

private theorem fixedP506JointComparison_smooth :
    FixedP506JointCurrentIdentityCoframeComparison.Smooth :=
  identityCoframeComparison_smooth FixedP506JointCurrent
    fixedGlobalMatterDualFullCauchy_smooth

private theorem fixedP506JointComparison_scalarCovariantDerivative_eq_current
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        FixedP506JointCurrentIdentityCoframeComparison point direction =
      holonomicScalarCovariantDerivative FixedP506JointCurrent point
        direction := by
  rfl

private theorem fixedP506JointComparison_scalarMomentumDivergence_zero
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506JointCurrentIdentityCoframeComparison direction 0 =
      0 := by
  apply
    StageNineBiradialScalarOriginResponse.scalarDifferentialMomentumDivergence_origin_eq_zero_of_biradial
      positiveSmoothUnifiedSource
      FixedP506JointCurrentIdentityCoframeComparison
      (a := 1) (b := 1)
  · norm_num
  · norm_num
  · rw [identityCoframeComparison_coframe,
      StageNineBiradialCoframeResponse.biradialCoframe_one_one]
  · intro formDirection
    exact
      ((holonomicScalarCovariantDerivative_contDiff
        FixedP506JointCurrentIdentityCoframeComparison
        fixedP506JointComparison_smooth formDirection).differentiable
          (by simp)).differentiableAt
  · intro formDirection
    have functionEquality :
        (fun point =>
          holonomicScalarCovariantDerivative
            FixedP506JointCurrentIdentityCoframeComparison point
              formDirection) =
          fun point =>
            holonomicScalarCovariantDerivative FixedP506JointCurrent point
              formDirection := by
      funext point
      exact
        fixedP506JointComparison_scalarCovariantDerivative_eq_current
          point formDirection
    rw [functionEquality]
    exact
      fixedP506JointCurrent_scalarCovariantDerivative_diagonalDerivative_zero
        formDirection

private theorem fixedP506JointCurrent_scalarMomentumDivergence_zero
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506JointCurrent direction 0 =
      0 := by
  rw [fixedP506JointCurrent_scalarMomentumDivergence_eq_comparison]
  exact fixedP506JointComparison_scalarMomentumDivergence_zero direction

private theorem fixedP506JointCurrent_scalarKineticAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedP506JointCurrent 0)
        (holonomicScalarVariationAlgebraicDirection
          FixedP506JointCurrent direction 0) =
      0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  have covariantDerivativeOrigin :
      (toContinuumPointField
        FixedP506JointCurrent 0).scalarCovariantDerivative =
        0 := by
    funext formDirection
    exact
      fixedP506JointCurrent_scalarCovariantDerivative_origin_zero
        formDirection
  rw [covariantDerivativeOrigin]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

private theorem fixedP506JointCurrent_scalarPotential_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField FixedP506JointCurrent 0) direction =
      0 := by
  unfold scalarPotentialFirstVariation
  rw [show
    (toContinuumPointField FixedP506JointCurrent 0).scalar =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource by
    exact congrFun fixedP506JointCurrent_scalar_vacuum 0]
  simp

private theorem fixedP506JointCurrent_scalarYukawa_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarYukawaFirstVariationDensity
        (toContinuumPointField FixedP506JointCurrent 0) direction =
      0 := by
  unfold scalarYukawaFirstVariationDensity scalarYukawaVariationVector
  rw [show
    (toContinuumPointField FixedP506JointCurrent 0).conjugateMatter =
        diracSpinZeroMatterCoordinate by
    change
      FixedP506JointCurrent.conjugateMatter 0 =
        diracSpinZeroMatterCoordinate
    rw [← congrFun fixedP506JointActual_conjugateMatter_eq_current 0]
    exact fixedP506JointActual_conjugateMatter_origin]
  rw [diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]
  norm_num

private theorem fixedP506JointCurrent_scalarAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        FixedP506JointCurrent direction 0 =
      0 := by
  unfold scalarAlgebraicDirectionalCoefficient
  rw [fixedP506JointCurrent_scalarKineticAlgebraic_origin_zero,
    fixedP506JointCurrent_scalarPotential_origin_zero,
    fixedP506JointCurrent_scalarYukawa_origin_zero]
  ring

theorem fixedP506JointResidual_scalar_origin_zero :
    (fixedP506JointResidualSection 0).scalar = 0 := by
  change
    (fun direction =>
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual direction 0) =
      0
  funext direction
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [fixedP506JointActual_diracDualScalarAlgebraic_eq_old,
    fixedP506JointActual_oldScalarAlgebraic_eq_current,
    fixedP506JointCurrent_scalarAlgebraic_origin_zero,
    fixedP506JointActual_scalarMomentumDivergence_eq_current,
    fixedP506JointCurrent_scalarMomentumDivergence_zero]
  simp

/-! ## Coframe coordinate of the same complete carrier -/

open StageNineCartanTangentSimplicityResponse
open StageNineDiracDualFormNativeCoframeIntegratedVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation

private theorem fixedP506Joint_identityECCurvatureObservation_intrinsic_apply
    (variation : LorentzianCoframe) :
    identityDiracDualECCurvatureObservation
        (gravityInternalPairVarianceNormalization
          (coframeWedge (1 : LorentzianCoframe))) variation =
      gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
        (coframeWedge (1 : LorentzianCoframe)) := by
  change
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
        (gravityInternalPairVarianceNormalization
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe)))) =
      _
  rw [gravityInternalPairVarianceNormalization_involutive]

private theorem fixedP506JointCurrent_ECNormalContactField_eq_restrict :
    diracDualFormNativeECNormalContactField FixedP506JointCurrent =
      restrictContinuumPointFieldToIIPlus
        (toContinuumPointField FixedP506JointCurrent 0) := by
  unfold diracDualFormNativeECNormalContactField
    diracDualFormNativeECNormalPreparedActual
  rw [fixedP506JointCurrent_restrictToIIPlus]

private theorem fixedP506JointCurrent_ECBalance_zero
    (variation : LorentzianCoframe) :
    gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent
            (FixedP506JointCurrent.coframe 0) variation)
          (gravityInternalPairVarianceNormalization
              (toContinuumPointField
                FixedP506JointCurrent 0).gravityCurvature +
            coframeWedge (FixedP506JointCurrent.coframe 0)) +
        diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource
          (restrictContinuumPointFieldToIIPlus
            (toContinuumPointField FixedP506JointCurrent 0)) variation +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0
          (restrictContinuumPointFieldToIIPlus
            (toContinuumPointField FixedP506JointCurrent 0)) variation =
      0 := by
  have balance := congrArg
    (fun covector : LorentzianCoframe →L[ℝ] ℝ => covector variation)
    fixedGlobalMatterDualFullCauchy_EC_covector_zero
  change
    (identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature FixedP506JointCurrent 0) +
        diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
          FixedP506JointCurrent) variation =
      0 at balance
  rw [fixedGlobalMatterDualFullCauchy_coframe_origin]
  rw [gravityTopologicalWedgeCoefficient_add_right]
  rw [show
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent
            (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization
            (toContinuumPointField
              FixedP506JointCurrent 0).gravityCurvature) =
        identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature FixedP506JointCurrent 0) variation by
      rfl]
  rw [←
    fixedP506Joint_identityECCurvatureObservation_intrinsic_apply variation]
  unfold diracDualFormNativeIdentityECLoad at balance
  rw [fixedP506JointCurrent_ECNormalContactField_eq_restrict] at balance
  simpa only [add_apply, zero_apply, add_assoc] using balance

private theorem fixedP506JointCurrent_reducedCoframeFirstVariation_zero
    (variation : LorentzianCoframe) :
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
        positiveSmoothUnifiedSource 0
        (toContinuumPointField FixedP506JointCurrent 0) variation =
      0 := by
  rw [
    StageNineDiracDualFormNativeIIPlusCoframeECBalance.diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_EC_balance
      positiveSmoothUnifiedSource 0
      (toContinuumPointField FixedP506JointCurrent 0)
      (by
        change Matrix.det (FixedP506JointCurrent.coframe 0) ≠ 0
        rw [fixedGlobalMatterDualFullCauchy_coframe_origin]
        norm_num)
      variation]
  exact fixedP506JointCurrent_ECBalance_zero variation

private theorem fixedP506JointCurrent_fullCoframeEuler_origin_zero :
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource 0
        (toContinuumPointField FixedP506JointCurrent 0) =
      0 := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    holonomicDiracDualFormNativeCoframeFirstVariationDensity
        positiveSmoothUnifiedSource FixedP506JointCurrent
        (fun _ => variation) 0 =
      0
  rw [←
    holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_of_equations
      positiveSmoothUnifiedSource FixedP506JointCurrent
      fixedGlobalMatterDualFullCauchy_simplicity
      fixedGlobalMatterDualFullCauchy_auxiliaryEquation
      (fun _ => variation) 0]
  exact fixedP506JointCurrent_reducedCoframeFirstVariation_zero variation

theorem fixedP506JointResidual_coframe_origin_zero :
    (fixedP506JointResidualSection 0).coframe = 0 := by
  change
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource 0
        (toContinuumPointField FixedP506JointActual 0) =
      0
  rw [fixedP506JointActual_pointField_origin_eq_current]
  exact fixedP506JointCurrent_fullCoframeEuler_origin_zero

/-! ## Complete origin support of the same joint residual

The historical identity-coframe Hodge/wedge sign is used below only inside
the actual directional-derivative calculation.  It does not decide the
P286 coordinate by itself.  The result combines that calculation with the
same-actual old response equation and the authoritative form-native charged
coefficient, then returns to the complete joint carrier. -/

private def fixedP506TopologicalWedgeLeftContinuousLinear
    (right : P286GaugeTwoForm) : P286GaugeTwoForm →L[ℝ] ℝ :=
  ({ toFun := fun left =>
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing left right
     map_add' := fun first second =>
      p286TopologicalGaugeBFCoefficient_add_left first second right
     map_smul' := by
      intro parameter left
      simpa only [RingHom.id_apply, smul_eq_mul] using
        p286TopologicalGaugeBFCoefficient_smul_left parameter left right } :
      P286GaugeTwoForm →ₗ[ℝ] ℝ).toContinuousLinearMap

private theorem
    fixedP506JointResponseAuxiliary_topologicalWedge_directionalDerivative
    (right : P286GaugeTwoForm)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
            (currentP286CompleteResponseAuxiliaryCoordinate
              positiveSmoothUnifiedSource FixedP506JointCurrent point)
            right)
        0 direction =
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        (fieldDirectionalDerivative
          (currentP286CompleteResponseAuxiliaryCoordinate
            positiveSmoothUnifiedSource FixedP506JointCurrent)
          0 direction)
        right := by
  have auxiliarySmooth :
      ContDiff ℝ ∞
        (currentP286CompleteResponseAuxiliaryCoordinate
          positiveSmoothUnifiedSource FixedP506JointCurrent) := by
    apply contDiff_pi'
    intro pair
    exact currentP286CompleteResponseAuxiliaryCoordinate_contDiff
      positiveSmoothUnifiedSource FixedP506JointCurrent pair
  have derivative :=
    (fixedP506TopologicalWedgeLeftContinuousLinear right).hasFDerivAt.comp 0
      ((auxiliarySmooth.differentiable (by simp)).differentiableAt
        |>.hasFDerivAt)
  unfold fieldDirectionalDerivative
  change
    (fderiv ℝ
      ((fixedP506TopologicalWedgeLeftContinuousLinear right) ∘
        currentP286CompleteResponseAuxiliaryCoordinate
          positiveSmoothUnifiedSource FixedP506JointCurrent) 0)
        (coordinateDirection direction) =
      _
  rw [derivative.fderiv]
  rfl

private theorem fixedP506JointActual_auxiliaryCoordinate_eq_response :
    holonomicP286GaugeAuxiliaryCoordinate FixedP506JointActual =
      currentP286CompleteResponseAuxiliaryCoordinate
        positiveSmoothUnifiedSource FixedP506JointCurrent := by
  funext point
  exact currentP286CompleteActionResponseOperator_auxiliaryCoordinate
    positiveSmoothUnifiedSource FixedP506JointCurrent point

private theorem
    fixedP506JointActual_topologicalWedge_directionalDerivative
    (right : P286GaugeTwoForm)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
            (holonomicP286GaugeAuxiliaryCoordinate
              FixedP506JointActual point)
            right)
        0 direction =
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        (p286GaugeAuxiliaryDirectionalDerivative
          FixedP506JointActual 0 direction)
        right := by
  unfold p286GaugeAuxiliaryDirectionalDerivative
  rw [fixedP506JointActual_auxiliaryCoordinate_eq_response]
  simpa using
    fixedP506JointResponseAuxiliary_topologicalWedge_directionalDerivative
      right direction

private theorem fixedP506JointFrozenMomentum_eq_neg_topologicalWedge
    (right : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        (identityCoframeComparison FixedP506JointActual) right =
      fun point =>
        -generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          (holonomicP286GaugeAuxiliaryCoordinate
            FixedP506JointActual point)
          right := by
  funext point
  unfold p286GaugeConnectionBFDifferentialMomentum
    generatedVolumeDensity
  simp only [identityCoframeComparison_coframe]
  change
    abs (Matrix.det (1 : LorentzianCoframe)) *
        p286GaugeAuxiliaryHodgePairingPolynomial 1
          (holonomicP286GaugeAuxiliaryCoordinate
            FixedP506JointActual point)
          right =
      _
  rw [fixedIdentityP286HodgePairing_eq_neg_topologicalWedge]
  norm_num

private theorem fixedP506JointActual_BFMomentumDerivative_eq_principal
    (right : P286GaugeTwoForm)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          FixedP506JointActual right)
        0 direction =
      -generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        (p286GaugeAuxiliaryDirectionalDerivative
          FixedP506JointActual 0 direction)
        right := by
  rw [
    fixedGlobalMatterDualP286Complete_bfMomentumDerivative_eq_identityComparison
      right direction]
  have functionEquality :=
    fixedP506JointFrozenMomentum_eq_neg_topologicalWedge right
  rw [functionEquality]
  have derivativeEquality :=
    fixedP506JointActual_topologicalWedge_directionalDerivative
      right direction
  have actualAuxiliarySmooth :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate FixedP506JointActual) := by
    rw [fixedP506JointActual_auxiliaryCoordinate_eq_response]
    apply contDiff_pi'
    intro pair
    exact currentP286CompleteResponseAuxiliaryCoordinate_contDiff
      positiveSmoothUnifiedSource FixedP506JointCurrent pair
  have wedgeSmooth :
      ContDiff ℝ ∞ fun point =>
        generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          (holonomicP286GaugeAuxiliaryCoordinate
            FixedP506JointActual point)
          right :=
    (fixedP506TopologicalWedgeLeftContinuousLinear right).contDiff.comp
      actualAuxiliarySmooth
  have wedgeDerivative :
      HasFDerivAt
        (fun point =>
          generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
            (holonomicP286GaugeAuxiliaryCoordinate
              FixedP506JointActual point)
            right)
        (fderiv ℝ
          (fun point =>
            generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (holonomicP286GaugeAuxiliaryCoordinate
                FixedP506JointActual point)
              right)
          0)
        0 :=
    (wedgeSmooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have negDerivative := wedgeDerivative.neg
  unfold fieldDirectionalDerivative
  change
    (fderiv ℝ
      (-(fun point =>
        generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          (holonomicP286GaugeAuxiliaryCoordinate
            FixedP506JointActual point)
          right))
      0) (coordinateDirection direction) =
      _
  rw [negDerivative.fderiv]
  exact congrArg Neg.neg derivativeEquality

private theorem fixedP506JointActual_exteriorDerivative_wedge_eq_BFDivergence
    (direction : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (holonomicP286GaugeAuxiliaryExteriorDerivative
          FixedP506JointActual 0) =
      p286GaugeConnectionBFDifferentialMomentumDivergence
        FixedP506JointActual direction 0 := by
  calc
    _ =
        -(∑ derivativeDirection : LorentzianIndex,
          p286GaugeExteriorPrincipalBilinear derivativeDirection
            (p286GaugeAuxiliaryDirectionalDerivative
              FixedP506JointActual 0 derivativeDirection)
            direction) := by
      exact
        (p286GaugeExteriorPrincipalSum_eq_w13
          (p286GaugeAuxiliaryDirectionalDerivative
            FixedP506JointActual 0)
          direction).symm
    _ =
        ∑ derivativeDirection : LorentzianIndex,
          -p286GaugeExteriorPrincipalBilinear derivativeDirection
            (p286GaugeAuxiliaryDirectionalDerivative
              FixedP506JointActual 0 derivativeDirection)
            direction := by
      rw [Finset.sum_neg_distrib]
    _ = _ := by
      unfold p286GaugeConnectionBFDifferentialMomentumDivergence
      apply Finset.sum_congr rfl
      intro derivativeDirection _
      rw [fixedP506JointActual_BFMomentumDerivative_eq_principal
        (StageNineP286GaugeConnectionPointwiseEquation.p286GaugeExteriorDerivativeDirection
          derivativeDirection direction)
        derivativeDirection]
      rfl

theorem
    fixedP506JointActual_gaugeConnectionCoordinate_origin_zero :
    holonomicP286GaugeConnectionCoordinate FixedP506JointActual 0 = 0 := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [fixedP506JointActual_gaugeConnection_eq_current]
  exact fixedP506JointCurrent_gaugeConnectionCoordinate_origin_zero

private theorem fixedP506_connectionExteriorAction_zero
    (value : P286GaugeTwoForm) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction 0 value = 0 := by
  have adjointZero : p286GaugeTwoFormAdjoint 0 value = 0 := by
    funext pair
    simp [p286GaugeTwoFormAdjoint]
  funext triple
  unfold pointwiseP286GaugeTwoFormConnectionExteriorAction
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormCovariantDerivative
  simp only [Pi.zero_apply, zero_add]
  rw [adjointZero]
  simp

private theorem
    fixedP506JointActual_covariantDerivative_wedge_eq_BFDivergence
    (direction : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          FixedP506JointActual 0) =
      p286GaugeConnectionBFDifferentialMomentumDivergence
        FixedP506JointActual direction 0 := by
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
    fixedP506JointActual_exteriorDerivative_wedge_eq_BFDivergence,
    fixedP506JointActual_gaugeConnectionCoordinate_origin_zero,
    fixedP506_connectionExteriorAction_zero]
  simp [p286GaugeOneFormThreeFormWedgeCoefficient]

theorem fixedP506JointActual_actionCurrent_eq_formNativeCharged
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual direction 0 =
      formNativeChargedGaugeFirstCoefficient
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedP506JointActual 0) direction := by
  have curvatureVariationZero :
      StageNineP286GaugeConnectionPointwiseEquation.p286GaugeConnectionAlgebraicCurvatureDirection
          FixedP506JointActual direction 0 =
        0 := by
    funext pair
    unfold
      StageNineP286GaugeConnectionPointwiseEquation.p286GaugeConnectionAlgebraicCurvatureDirection
      StageNineP286GaugeConnectionPointwiseEquation.p286GaugeConnectionAlgebraicCurvatureVariation
    rw [fixedP506JointActual_gaugeConnectionCoordinate_origin_zero]
    simp
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
    p286GaugeConnectionFirstVariationDensity
    formNativeChargedGaugeFirstCoefficient
  rw [curvatureVariationZero]
  have bfZero :
      p286GaugeBFCurvatureIncrementDensity
          (toContinuumPointField FixedP506JointActual 0).coframe
          (coframeGaugeSpacetimeHodgeLinear
            (toContinuumPointField FixedP506JointActual 0).coframe)
          (p286AuxiliaryCoordinate
            (toContinuumPointField FixedP506JointActual 0))
          0 =
        0 := by
    simp [p286GaugeBFCurvatureIncrementDensity,
      generatedGaugeTwoFormMetricPairing]
  rw [bfZero, zero_add]
  have scalarVariationEq :
      holonomicScalarGaugeConnectionVariation
          FixedP506JointActual (fun _ => direction) 0 =
        pointwiseScalarP286GaugeConnectionVariation
          (toContinuumPointField FixedP506JointActual 0) direction := by
    symm
    simpa using
      pointwiseScalarP286GaugeConnectionVariation_actual
        FixedP506JointActual (fun _ => direction) 0
  have matterVariationEq :
      holonomicMatterGaugeConnectionVariation
          FixedP506JointActual (fun _ => direction) 0 =
        pointwiseMatterP286GaugeConnectionVariation
          (toContinuumPointField FixedP506JointActual 0) direction := by
    symm
    simpa using
      pointwiseMatterP286GaugeConnectionVariation_actual
        FixedP506JointActual (fun _ => direction) 0
  rw [scalarVariationEq, matterVariationEq]

private theorem fixedP506JointActual_formNativeEuler_wedge_normalForm
    (direction : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (holonomicFormNativeP286GaugeEulerThreeForm
          positiveSmoothUnifiedSource 0 FixedP506JointActual 0) =
      2 *
        formNativeChargedGaugeFirstCoefficient
          positiveSmoothUnifiedSource 0 0
          (toContinuumPointField FixedP506JointActual 0) direction := by
  have oldEquation :=
    fixedGlobalMatterDualP286Complete_connectionEquation_origin direction
  unfold p286GaugeConnectionEulerLagrangeCoefficient at oldEquation
  have actionEqDivergence :
      p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource FixedP506JointActual direction 0 =
        p286GaugeConnectionBFDifferentialMomentumDivergence
          FixedP506JointActual direction 0 :=
    sub_eq_zero.mp oldEquation
  have actionEqCharged :=
    fixedP506JointActual_actionCurrent_eq_formNativeCharged direction
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
    fixedP506JointActual_covariantDerivative_wedge_eq_BFDivergence,
    formNativeChargedGaugeThreeForm_evaluation]
  rw [← actionEqCharged, actionEqDivergence]
  ring

private theorem fixedP506JointActual_formNativeEuler_threeForm_normalForm :
    holonomicFormNativeP286GaugeEulerThreeForm
        positiveSmoothUnifiedSource 0 FixedP506JointActual 0 =
      (2 : ℝ) •
        formNativeChargedGaugeThreeForm
          positiveSmoothUnifiedSource 0 0
          (toContinuumPointField FixedP506JointActual 0) := by
  let chargedDual :=
    formNativeChargedGaugeFirstLinearMap
      positiveSmoothUnifiedSource 0 0
      (toContinuumPointField FixedP506JointActual 0)
  calc
    _ = p286GaugeThreeFormOfDual ((2 : ℝ) • chargedDual) := by
      apply p286GaugeThreeFormOfDual_unique
      intro direction
      exact fixedP506JointActual_formNativeEuler_wedge_normalForm direction
    _ = (2 : ℝ) • p286GaugeThreeFormOfDual chargedDual := by
      unfold p286GaugeThreeFormOfDual
      rw [map_smul]
    _ = _ := by
      rfl

/-- The final missing origin coordinate of the complete carrier.  The result
is a readout of the actual form-native root, not a P286-only repair epoch. -/
theorem fixedP506JointResidual_p286GaugeConnection_origin_normalForm :
    (fixedP506JointResidualSection 0).p286GaugeConnection =
      (2 : ℝ) •
        formNativeChargedGaugeThreeForm
          positiveSmoothUnifiedSource 0 0
          (toContinuumPointField FixedP506JointActual 0) := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm
        positiveSmoothUnifiedSource 0 FixedP506JointActual 0 =
      _
  exact fixedP506JointActual_formNativeEuler_threeForm_normalForm

/-- Canonical whole-carrier normal form at the fixed contact.  All nine
coordinates were computed on one actual; only the P286 connection coordinate
can carry support there. -/
def fixedP506JointOriginResidualNormalForm :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { gravityMultiplier := 0
    gravityAuxiliary := 0
    p286GaugeAuxiliary := 0
    lorentzConnection := 0
    p286GaugeConnection :=
      (2 : ℝ) •
        formNativeChargedGaugeThreeForm
          positiveSmoothUnifiedSource 0 0
          (toContinuumPointField FixedP506JointActual 0)
    scalar := 0
    matter := 0
    conjugateMatter := 0
    coframe := 0 }

/-- Complete origin residual calculation for the fixed P506/L0 successor. -/
theorem fixedP506JointResidual_origin_normalForm :
    fixedP506JointResidualSection 0 =
      fixedP506JointOriginResidualNormalForm := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact fixedP506JointResidual_gravityMultiplier_zero 0
  · exact fixedP506JointResidual_gravityAuxiliary_zero 0
  · exact fixedP506JointResidual_p286GaugeAuxiliary_zero
  · exact fixedP506JointResidual_lorentzConnection_origin_zero
  · exact fixedP506JointResidual_p286GaugeConnection_origin_normalForm
  · exact fixedP506JointResidual_scalar_origin_zero
  · exact fixedP506JointResidual_matter_origin_zero
  · exact fixedP506JointResidual_conjugateMatter_origin_zero
  · exact fixedP506JointResidual_coframe_origin_zero

/-! ## Normalization-invariant support decision

The `-1` below is a convention-locked coordinate readout.  The exported
support result consumes only its invariant consequence that the charged
covector, hence the complete joint residual, is nonzero. -/

private theorem
    fixedP506Joint_pointwiseTemporalHyperchargeMatterVariation :
    pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField FixedP506JointActual 0)
        (p286TemporalGaugeOneForm hyperchargeCoordinate) =
      temporalHyperchargeMatterDerivative := by
  funext formDirection
  unfold pointwiseMatterP286GaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_matter_origin]
  have mother :=
    congrFun temporalHyperchargeMotherVariation formDirection
  have motherPointwise :
      pointwiseP286GaugeConnectionMotherVariation
          (p286TemporalGaugeOneForm hyperchargeCoordinate) formDirection =
        if formDirection = canonicalLorentzianTimeDirection then
          p506P286HyperchargeMotherDirection
        else 0 := by
    simpa [pointwiseP286GaugeConnectionMotherVariation,
      p286GaugeConnectionMotherVariation] using mother
  rw [motherPointwise]
  by_cases isTime :
      formDirection = canonicalLorentzianTimeDirection
  · simpa [temporalHyperchargeMatterDerivative, isTime] using
      diracExteriorMotherLieAction_p286Hypercharge_spinTwoProbe
  · simp [temporalHyperchargeMatterDerivative, isTime,
      StageNineP286GaugeConnectionVariationDensity.diracExteriorMotherLieAction_zero_matrix]

private theorem fixedP506Joint_temporalHyperchargeMatterKineticSum :
    matterGaugeKineticSum positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedP506JointActual 0)
        (pointwiseMatterP286GaugeConnectionVariation
          (toContinuumPointField FixedP506JointActual 0)
          (p286TemporalGaugeOneForm hyperchargeCoordinate)) =
      Complex.I • diracSpinZeroMatterProbe := by
  rw [fixedP506Joint_pointwiseTemporalHyperchargeMatterVariation]
  unfold matterGaugeKineticSum
  rw [temporalHyperchargeMatterDerivative_frameRelative]
  simp only [toContinuumPointField,
    fixedGlobalMatterDualP286Complete_coframe_origin,
    Fin.sum_univ_four, temporalHyperchargeMatterDerivative,
    canonicalLorentzianTimeDirection,
    show (1 : LorentzianIndex) ≠ 0 by decide,
    show (2 : LorentzianIndex) ≠ 0 by decide,
    show (3 : LorentzianIndex) ≠ 0 by decide,
    if_pos, if_false, map_zero, add_zero]
  rw [map_smul, identityInverseCoframeGammaZero_spinTwo]

private theorem fixedP506Joint_temporalHyperchargeMatterVariationVector :
    matterGaugeConnectionVariationVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedP506JointActual 0)
        (pointwiseMatterP286GaugeConnectionVariation
          (toContinuumPointField FixedP506JointActual 0)
          (p286TemporalGaugeOneForm hyperchargeCoordinate)) =
      -diracSpinZeroMatterProbe := by
  unfold matterGaugeConnectionVariationVector
  rw [fixedP506Joint_temporalHyperchargeMatterKineticSum]
  rw [smul_smul]
  norm_num
  exact neg_one_smul ℂ diracSpinZeroMatterProbe

private theorem
    fixedP506Joint_temporalHyperchargeMatterFirstVariationDensity :
    matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource
        0 0 (toContinuumPointField FixedP506JointActual 0)
        (pointwiseMatterP286GaugeConnectionVariation
          (toContinuumPointField FixedP506JointActual 0)
          (p286TemporalGaugeOneForm hyperchargeCoordinate)) =
      -1 := by
  unfold matterGaugeConnectionFirstVariationDensity
  rw [fixedP506Joint_temporalHyperchargeMatterVariationVector]
  simp only [toContinuumPointField,
    fixedP506JointActual_conjugateMatter_origin]
  rw [matterDualFrameRelative_chartZero]
  simp [diracSpinZeroMatterCoordinate_probe]

theorem fixedP506JointActual_scalarCovariantDerivative_origin_zero
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        FixedP506JointActual 0 direction =
      0 := by
  have equality :
      holonomicScalarCovariantDerivative
          FixedP506JointActual 0 direction =
        holonomicScalarCovariantDerivative
          FixedP506JointCurrent 0 direction := by
    unfold holonomicScalarCovariantDerivative
    rw [fixedP506JointActual_scalar_eq_current,
      fixedP506JointActual_gaugeConnection_eq_current]
  rw [equality]
  exact fixedP506JointCurrent_scalarCovariantDerivative_origin_zero direction

private theorem
    fixedP506Joint_temporalHyperchargeScalarFirstVariationDensity_zero :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedP506JointActual 0)
        (pointwiseScalarP286GaugeConnectionVariation
          (toContinuumPointField FixedP506JointActual 0)
          (p286TemporalGaugeOneForm hyperchargeCoordinate)) =
      0 := by
  have scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative FixedP506JointActual 0 = 0 := by
    funext direction
    exact fixedP506JointActual_scalarCovariantDerivative_origin_zero direction
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  simp only [toContinuumPointField, scalarCovariantDerivativeEq]
  simp [scalarFrameRelativeCovariantDerivative,
    scalarCoordinatePairingRe]

private theorem
    fixedP506Joint_chargedGaugeFirstCoefficient_temporalHypercharge :
    formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource
        0 0 (toContinuumPointField FixedP506JointActual 0)
        (p286TemporalGaugeOneForm hyperchargeCoordinate) =
      -1 := by
  unfold formNativeChargedGaugeFirstCoefficient
  rw [
    fixedP506Joint_temporalHyperchargeScalarFirstVariationDensity_zero,
    fixedP506Joint_temporalHyperchargeMatterFirstVariationDensity]
  simp [generatedVolumeDensity, toContinuumPointField,
    fixedGlobalMatterDualP286Complete_coframe_origin]

/-- The actual action-generated charged three-form is nonzero.  This is the
normalization-invariant content of the preceding coordinate readout. -/
theorem fixedP506Joint_chargedGaugeThreeForm_ne_zero :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource
        0 0 (toContinuumPointField FixedP506JointActual 0) ≠
      0 := by
  intro formZero
  have evaluated :=
    formNativeChargedGaugeThreeForm_evaluation positiveSmoothUnifiedSource
      0 0 (toContinuumPointField FixedP506JointActual 0)
      (p286TemporalGaugeOneForm hyperchargeCoordinate)
  rw [formZero,
    fixedP506Joint_chargedGaugeFirstCoefficient_temporalHypercharge]
    at evaluated
  simp [p286GaugeOneFormThreeFormWedgeCoefficient] at evaluated

/-- The complete origin carrier has genuine support.  This does not promote
that support to a separate gate; it is the obstruction consumed by the next
same-source joint action write. -/
theorem fixedP506JointResidual_origin_ne_zero :
    fixedP506JointResidualSection 0 ≠ 0 := by
  intro jointZero
  have connectionZero := congrArg
    DiracDualFormNativePointwiseJointResidualCarrier.p286GaugeConnection
    jointZero
  have chargedNonzero := fixedP506Joint_chargedGaugeThreeForm_ne_zero
  rw [fixedP506JointResidual_p286GaugeConnection_origin_normalForm]
    at connectionZero
  simp only [zero_p286GaugeConnection] at connectionZero
  have twoNonzero : (2 : ℝ) ≠ 0 := by norm_num
  exact chargedNonzero
    ((smul_eq_zero.mp connectionZero).resolve_left twoNonzero)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointResidual
