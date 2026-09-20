import H0mework.Physics.FixedJoint.FixedCartanRestartCurvatureSpatialRegularity
import H0mework.Physics.DualVariation.ECCauchyConstraintObstructionRegression
import H0mework.Physics.ConstrainedCauchy.FixedECFullCauchyLiveStressSpatialRegularity
import H0mework.Physics.MatterCurrent.FullSynchronizedLorentzMatterSpinTangency
import H0mework.Physics.Dirac.DiracMatterCoordinateCalculus
import H0mework.Physics.DiracCovariance.CurvatureCovariance

/-!
# Fixed P506/L0 Cartan-restart temporal electric kernel

For the fixed exact-lineage P506/L0 action input, the live primal and adjoint
matter equations make the repaired W13 spin response stationary along the
canonical time direction.  The action-native Cartan actualizer therefore has
zero temporal derivative in the two connection coordinates entering the
`E03` electric-curvature readout.  The Levi--Civita contribution is computed
from the explicit polynomial coframe jet, while the KIN contribution is
transported from the same live spin response.

No curvature target, residual coordinate, shell certificate, or branch choice
is accepted as input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanRestartTemporalElectricKernel

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTorsionThreeFormEquiv
open StageNineConjugateMatterActionTimeVelocity
open StageNineCoframeVariation
open StageNineCoframeFirstJet
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanAlgebraicSmoothness
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracKineticLocalSpinCurvatureCovariance
open StageNineDiracMatterCoordinateCalculus
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeECCauchyConstraintObstructionRegression
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineMatterActionTimeVelocity
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzContactReadout
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMatterSpinTangency
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzResponse
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineTopologicalLorentzThreeFormDuality
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRestriction
open SU7ExteriorYukawaMassSpectrum
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

local instance currentMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private theorem fixed_current_repairedPrimalLaw :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      FixedP506JointActual 0
      (holonomicMatterCovariantDerivative FixedP506JointActual 0
        canonicalLorentzianTimeDirection) := by
  have h := fixedP506JointActual_repairedMatterVector_origin_zero
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum at h
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart,
    matterFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart] at h
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
    CurrentCoframeMatterTemporalActionLaw
    currentCoframeMatterTemporalPrincipal
    holonomicDiracDualCurrentCoframeMatterKnownVector
  simpa [canonicalLorentzianTimeDirection, Fin.sum_univ_four,
    Fin.sum_univ_three, add_assoc] using h

private theorem fixed_current_primalTemporal_eq_native :
    holonomicMatterCovariantDerivative FixedP506JointActual 0
        canonicalLorentzianTimeDirection =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        FixedP506JointActual 0 := by
  have noncharacteristic :
      coframeTemporalPrincipalScalar (FixedP506JointActual.coframe 0) ≠ 0 := by
    rw [fixedP506JointActual_coframe_origin_one]
    simp
  exact holonomicDiracDualCurrentCoframeMatterTimeActionLaw_unique
    FixedP506JointActual 0 noncharacteristic _ _
    fixed_current_repairedPrimalLaw
    (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      FixedP506JointActual 0 noncharacteristic)

private theorem fixed_current_matterTemporalDerivative_eq_native :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          (FixedP506JointActual.matter point))
        0 canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
          FixedP506JointActual 0) := by
  have covariant := fixed_current_primalTemporal_eq_native
  apply matterCoordinateEquiv.symm.injective
  simp only [matterCoordinateEquiv.symm_apply_apply]
  unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    holonomicMatterConnectionAction
  unfold holonomicMatterCovariantDerivative at covariant
  rw [← covariant]
  abel

private theorem fixed_current_adjointTemporal_eq_native :
    holonomicConjugateMatterDerivativeDual FixedP506JointActual 0
        canonicalLorentzianTimeDirection =
      holonomicIdentityCoframeConjugateMatterActionVelocity
        FixedP506JointActual 0 := by
  exact holonomicIdentityCoframeConjugateMatterTimeActionLaw_unique
    FixedP506JointActual 0 _ _
    fixedP506JointActual_adjointActionLaw
    (holonomicIdentityCoframeConjugateMatterActionVelocity_satisfies
      FixedP506JointActual 0)

private theorem fixed_current_conjugateMatterTemporalDerivative_eq_native
    (matter : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (fun point => FixedP506JointActual.conjugateMatter point matter)
        0 canonicalLorentzianTimeDirection =
      holonomicIdentityCoframeConjugateMatterActionVelocity
        FixedP506JointActual 0 matter := by
  rw [← fixed_current_adjointTemporal_eq_native]
  exact (holonomicConjugateMatterDerivativeDual_apply
    FixedP506JointActual fixedGlobalMatterDualP286Complete_smooth 0
    canonicalLorentzianTimeDirection matter).symm

private theorem fixed_current_gaugeConnection_origin_zero :
    FixedP506JointActual.gaugeConnection 0 = 0 := by
  funext direction
  apply p286CoordinateEquiv.injective
  simpa [holonomicP286GaugeConnectionCoordinate] using
    congrFun fixedP506JointActual_gaugeConnectionCoordinate_origin_zero
      direction

private theorem fixed_vacuum_massMap_hyperchargeProbe_zero :
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

private theorem fixed_vacuum_diracDualYukawa_spinTwo_zero :
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
    · exact fixed_vacuum_massMap_hyperchargeProbe_zero
    · rfl
  · simp [diracExteriorYukawaInternalAction, internalMatterLinearAction,
      exteriorYukawaInternalAction, diracSpinTwoMatterProbe]

private theorem fixed_current_primalRawVelocity_zero :
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        FixedP506JointActual 0 =
      0 := by
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    actionGeneratedCurrentCoframeMatterTemporalDerivative
    currentCoframeMatterTemporalPrincipalInverse
    currentCoframeMatterTemporalPrincipal
    holonomicDiracDualCurrentCoframeMatterKnownVector
    holonomicMatterConnectionAction
  rw [fixedP506JointActual_coframe_origin_one,
    fixedP506JointActual_matter_origin,
    fixedP506JointActual_scalar_origin,
    fixedP506JointActual_connection_origin_eq_fixedAction,
    fixedActionCartanConnection_eq_positiveNormalForm,
    fixed_current_gaugeConnection_origin_zero]
  simp_rw [fixedP506JointActual_spatialCovariantDerivative_normalForm]
  rw [show
    scalarCoordinateEquiv.symm
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      sourceGeneratedVacuumBase positiveSmoothUnifiedSource by
      simp [sourceGeneratedVacuumCoordinates],
    fixed_vacuum_diracDualYukawa_spinTwo_zero]
  have imaginarySandwich (z : ℂ) :
      Complex.I * (-1 : ℂ) * (Complex.I * z) = z := by
    calc
      _ = -(Complex.I * Complex.I) * z := by ring
      _ = z := by rw [Complex.I_mul_I]; ring
  funext row
  fin_cases row <;>
    simp [coframeTemporalPrincipalScalar, inverseCoframeDiracGamma,
    positiveDiracDualCartanContorsionNormalForm,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction, diracSpinTwoMatterProbe,
    p286HyperchargeMatterProbe,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    Matrix.mul_apply, Matrix.one_apply,
    Fin.sum_univ_six, Fin.sum_univ_four, Fin.sum_univ_three,
    lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond, minkowskiInternalSign,
      canonicalLorentzianTimeDirection]
  all_goals
    simp only [smul_smul]
    rw [← mul_assoc, imaginarySandwich]
    module

/-- The fixed current's action-native raw primal velocity vanishes.  This is
the reusable action read needed by later global-development first-germ
comparisons; it is not a stored velocity certificate. -/
theorem fixedP506JointActual_primalRawVelocity_zero :
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        FixedP506JointActual 0 =
      0 :=
  fixed_current_primalRawVelocity_zero

/-- Re-running the repaired primal action leg on the fixed current produces
no first-jet correction. -/
theorem fixedP506JointActual_primalTimeResponseWrite_zero :
    diracDualCurrentCoframeMatterTimeResponseWrite FixedP506JointActual = 0 := by
  unfold diracDualCurrentCoframeMatterTimeResponseWrite
  rw [← fixed_current_primalTemporal_eq_native]
  simp

private theorem fixed_current_adjointAlgebraic_row_zero
    (matter : DiracExteriorMatterCarrier) :
    diracSpinZeroMatterCoordinate
        (holonomicIdentityCoframeMatterAlgebraicOperator
          FixedP506JointActual 0 matter) =
      0 := by
  unfold holonomicIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  rw [fixedP506JointActual_connection_origin_eq_fixedAction,
    fixedActionCartanConnection_eq_positiveNormalForm,
    fixed_current_gaugeConnection_origin_zero,
    fixedP506JointActual_scalar_origin]
  rw [show
    scalarCoordinateEquiv.symm
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      sourceGeneratedVacuumBase positiveSmoothUnifiedSource by
      simp [sourceGeneratedVacuumCoordinates]]
  simp [positiveDiracDualCartanContorsionNormalForm,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction, diracSpinZeroMatterCoordinate,
    hyperchargeDegreeTwoMatterCoordinate,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
    lorentzBivectorFirst, lorentzBivectorSecond,
    pairFirst, pairSecond, minkowskiInternalSign,
    chiralExteriorYukawaAction_degreeTwo_eq_zero]

private theorem fixed_current_adjointActionVelocity_zero :
    holonomicIdentityCoframeConjugateMatterActionVelocity
        FixedP506JointActual 0 =
      0 := by
  apply LinearMap.ext
  intro matter
  unfold holonomicIdentityCoframeConjugateMatterActionVelocity
    holonomicIdentityCoframeConjugateMatterKnownDual
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  simp_rw [fixedP506JointActual_conjugateMatterDerivativeDual_spatial_zero]
  rw [fixedP506JointActual_conjugateMatter_origin]
  simp [fixed_current_adjointAlgebraic_row_zero]

/-- The same fixed current has zero action-native adjoint velocity. -/
theorem fixedP506JointActual_adjointActionVelocity_zero :
    holonomicIdentityCoframeConjugateMatterActionVelocity
        FixedP506JointActual 0 =
      0 :=
  fixed_current_adjointActionVelocity_zero

private theorem fixed_current_diracDualAdjointAlgebraic_row_zero
    (matter : DiracExteriorMatterCarrier) :
    diracSpinZeroMatterCoordinate
        (holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
          FixedP506JointActual 0 matter) =
      0 := by
  unfold holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  rw [fixedP506JointActual_connection_origin_eq_fixedAction,
    fixedActionCartanConnection_eq_positiveNormalForm,
    fixed_current_gaugeConnection_origin_zero,
    fixedP506JointActual_scalar_origin]
  rw [show
    scalarCoordinateEquiv.symm
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      sourceGeneratedVacuumBase positiveSmoothUnifiedSource by
      simp [sourceGeneratedVacuumCoordinates]]
  rw [LinearMap.add_apply, map_add,
    diracSpinZeroMatterCoordinate_diracDualRightChiralYukawaAction_eq_zero,
    add_zero]
  simp [positiveDiracDualCartanContorsionNormalForm,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracMatrixMatterAction, diracSpinZeroMatterCoordinate,
    hyperchargeDegreeTwoMatterCoordinate,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
    lorentzBivectorFirst, lorentzBivectorSecond,
    pairFirst, pairSecond, minkowskiInternalSign]

/-- The authoritative Dirac-dual adjoint law also selects zero velocity on
the fixed action current. -/
theorem fixedP506JointActual_diracDualAdjointActionVelocity_zero :
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        FixedP506JointActual 0 =
      0 := by
  apply LinearMap.ext
  intro matter
  unfold holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  simp_rw [fixedP506JointActual_conjugateMatterDerivativeDual_spatial_zero]
  rw [fixedP506JointActual_conjugateMatter_origin]
  simp [fixed_current_diracDualAdjointAlgebraic_row_zero]

private theorem fixed_current_matterCoordinate_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          (FixedP506JointActual.matter point))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [fixed_current_matterTemporalDerivative_eq_native,
    fixed_current_primalRawVelocity_zero]
  simp

/-- The fixed current's primitive matter field has zero canonical-time
derivative at the judged occurrence. -/
theorem fixedP506JointActual_matterCoordinate_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          (FixedP506JointActual.matter point))
        0 canonicalLorentzianTimeDirection =
      0 :=
  fixed_current_matterCoordinate_temporalDerivative_zero

private theorem fixed_current_conjugateMatter_temporalDerivative_zero
    (matter : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (fun point => FixedP506JointActual.conjugateMatter point matter)
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [fixed_current_conjugateMatterTemporalDerivative_eq_native,
    fixed_current_adjointActionVelocity_zero]
  rfl

/-- The same action closure fixes every dual-matter component's
canonical-time derivative to zero. -/
theorem fixedP506JointActual_conjugateMatter_temporalDerivative_zero
    (matter : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (fun point => FixedP506JointActual.conjugateMatter point matter)
        0 canonicalLorentzianTimeDirection =
      0 :=
  fixed_current_conjugateMatter_temporalDerivative_zero matter

private def fixedLorentzSpinActionVector
    (variationDirection : LorentzianIndex) (internalPair : Fin 6)
    (matter : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ direction : LorentzianIndex,
      diracMatrixMatterAction (diracGamma direction)
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm
              (loweredLorentzBivectorOneFormCoordinate
                variationDirection internalPair)) direction)
          matter)

private def fixedLorentzSpinAction
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ direction : LorentzianIndex,
      (diracMatrixMatterAction (diracGamma direction)).comp
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm
              (loweredLorentzBivectorOneFormCoordinate
                variationDirection internalPair)) direction))

@[simp] private theorem fixedLorentzSpinAction_apply
    (variationDirection : LorentzianIndex) (internalPair : Fin 6)
    (matter : DiracExteriorMatterCarrier) :
    fixedLorentzSpinAction variationDirection internalPair matter =
      fixedLorentzSpinActionVector variationDirection internalPair matter := by
  simp [fixedLorentzSpinAction, fixedLorentzSpinActionVector]

private def fixedLorentzSpinCoordinateLinear
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
  ((matterCoordinateEquiv.toLinearMap.comp
      ((fixedLorentzSpinAction variationDirection internalPair).comp
        matterCoordinateEquiv.symm.toLinearMap)).toContinuousLinearMap
    ).restrictScalars ℝ

@[simp] private theorem fixedLorentzSpinCoordinateLinear_apply
    (variationDirection : LorentzianIndex) (internalPair : Fin 6)
    (coordinates : MatterCoordinateCarrier) :
    fixedLorentzSpinCoordinateLinear variationDirection internalPair
        coordinates =
      matterCoordinateEquiv
        (fixedLorentzSpinActionVector variationDirection internalPair
          (matterCoordinateEquiv.symm coordinates)) := by
  rfl

private def fixed_current_lorentzSpinCoordinateVector
    (variationDirection : LorentzianIndex) (internalPair : Fin 6)
    (point : BasePoint) : MatterCoordinateCarrier :=
  fixedLorentzSpinCoordinateLinear variationDirection internalPair
    (matterCoordinateEquiv (FixedP506JointActual.matter point))

private theorem fixed_current_lorentzSpinCoordinateVector_contDiff
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiff ℝ ∞
      (fixed_current_lorentzSpinCoordinateVector
        variationDirection internalPair) := by
  exact
    (fixedLorentzSpinCoordinateLinear variationDirection internalPair
      ).contDiff.comp fixedGlobalMatterDualP286Complete_smooth.2.2.2.2.2.2.2.1

private theorem
    fixed_current_lorentzSpinCoordinateVector_temporalDerivative_zero
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fixed_current_lorentzSpinCoordinateVector
          variationDirection internalPair)
        0 canonicalLorentzianTimeDirection =
      0 := by
  let coordinates : BasePoint → MatterCoordinateCarrier := fun point =>
    matterCoordinateEquiv (FixedP506JointActual.matter point)
  let action :=
    fixedLorentzSpinCoordinateLinear variationDirection internalPair
  have coordinatesDifferentiable : DifferentiableAt ℝ coordinates 0 :=
    (fixedGlobalMatterDualP286Complete_smooth.2.2.2.2.2.2.2.1.differentiable
      (by simp)).differentiableAt
  have composed :=
    action.hasFDerivAt.comp 0 coordinatesDifferentiable.hasFDerivAt
  rw [show
    fixed_current_lorentzSpinCoordinateVector
        variationDirection internalPair =
      action ∘ coordinates by rfl]
  unfold fieldDirectionalDerivative
  rw [composed.fderiv]
  change
    action
        (fieldDirectionalDerivative coordinates 0
          canonicalLorentzianTimeDirection) =
      0
  rw [show
    fieldDirectionalDerivative coordinates 0
        canonicalLorentzianTimeDirection = 0 by
      exact fixed_current_matterCoordinate_temporalDerivative_zero]
  exact map_zero action

private theorem fixed_frozenLorentzMatterCoefficient_normalForm
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    (fun point =>
      formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
        point
        (withCoframe (toContinuumPointField FixedP506JointActual point) 1)
        (loweredLorentzBivectorOneFormCoordinate
          variationDirection internalPair)) =
      fun point =>
        (FixedP506JointActual.conjugateMatter point
          (fixedLorentzSpinActionVector variationDirection internalPair
            (FixedP506JointActual.matter point))).re := by
  funext point
  unfold formNativeLorentzMatterFirstCoefficient
    matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation generatedVolumeDensity
  simp only [withCoframe, toContinuumPointField, Matrix.det_one,
    abs_one, one_mul, matterDualFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart]
  rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
        identityCoframeMatterGeometry by rfl]
  simp only [inverseCoframeDiracGamma_identity]
  simp [fixedLorentzSpinActionVector, Fin.sum_univ_four]

private theorem fixed_frozenLorentzMatterCoefficient_coordinateExpansion
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    (fun point =>
      formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
        point
        (withCoframe (toContinuumPointField FixedP506JointActual point) 1)
        (loweredLorentzBivectorOneFormCoordinate
          variationDirection internalPair)) =
      fun point =>
        ∑ index : MatterCoordinateIndex,
          (fixed_current_lorentzSpinCoordinateVector
                variationDirection internalPair point index *
            FixedP506JointActual.conjugateMatter point
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ)))).re := by
  rw [fixed_frozenLorentzMatterCoefficient_normalForm]
  funext point
  have vectorFidelity :
      matterCoordinateEquiv.symm
          (fixed_current_lorentzSpinCoordinateVector
            variationDirection internalPair point) =
        fixedLorentzSpinActionVector variationDirection internalPair
          (FixedP506JointActual.matter point) := by
    simp [fixed_current_lorentzSpinCoordinateVector]
  rw [← vectorFidelity, matterDual_coordinate_expansion]
  simp only [Complex.re_sum]

private def matterCoordinatePairingRe
    (first second : MatterCoordinateCarrier) : ℝ :=
  ∑ index : MatterCoordinateIndex, (first index * second index).re

private theorem matterCoordinatePairingRe_add_right
    (first second third : MatterCoordinateCarrier) :
    matterCoordinatePairingRe first (second + third) =
      matterCoordinatePairingRe first second +
        matterCoordinatePairingRe first third := by
  simp [matterCoordinatePairingRe, mul_add, Finset.sum_add_distrib]

private theorem matterCoordinatePairingRe_add_left
    (first second third : MatterCoordinateCarrier) :
    matterCoordinatePairingRe (first + second) third =
      matterCoordinatePairingRe first third +
        matterCoordinatePairingRe second third := by
  simp [matterCoordinatePairingRe, add_mul, Finset.sum_add_distrib]

private theorem matterCoordinatePairingRe_smul_right
    (parameter : ℝ) (first second : MatterCoordinateCarrier) :
    matterCoordinatePairingRe first (parameter • second) =
      parameter • matterCoordinatePairingRe first second := by
  unfold matterCoordinatePairingRe
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [PiLp.smul_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change
    (first index * ((parameter : ℂ) * second index)).re =
      parameter * (first index * second index).re
  rw [show
    first index * ((parameter : ℂ) * second index) =
      (parameter : ℂ) * (first index * second index) by ring]
  simp

private theorem matterCoordinatePairingRe_smul_left
    (parameter : ℝ) (first second : MatterCoordinateCarrier) :
    matterCoordinatePairingRe (parameter • first) second =
      parameter • matterCoordinatePairingRe first second := by
  unfold matterCoordinatePairingRe
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [PiLp.smul_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change
    (((parameter : ℂ) * first index) * second index).re =
      parameter * (first index * second index).re
  rw [show
    ((parameter : ℂ) * first index) * second index =
      (parameter : ℂ) * (first index * second index) by ring]
  simp

private def matterCoordinatePairingReBilinear :
    MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier →ₗ[ℝ] ℝ where
  toFun first :=
    { toFun := matterCoordinatePairingRe first
      map_add' := matterCoordinatePairingRe_add_right first
      map_smul' := by
        intro parameter second
        simpa only [RingHom.id_apply] using
          matterCoordinatePairingRe_smul_right parameter first second }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro third
    exact matterCoordinatePairingRe_add_left first second third
  map_smul' := by
    intro parameter first
    apply LinearMap.ext
    intro second
    exact matterCoordinatePairingRe_smul_left parameter first second

@[simp] private theorem matterCoordinatePairingReBilinear_apply
    (first second : MatterCoordinateCarrier) :
    matterCoordinatePairingReBilinear first second =
      matterCoordinatePairingRe first second :=
  rfl

private theorem matterCoordinatePairingRe_matterDualCoordinates
    (first : MatterCoordinateCarrier)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterCoordinatePairingReBilinear first
        (StageNineConjugateMatterVariation.matterDualCoordinates dual) =
      ∑ index : MatterCoordinateIndex,
        (first index * dual
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))).re := by
  rw [matterCoordinatePairingReBilinear_apply]
  unfold matterCoordinatePairingRe
  apply Finset.sum_congr rfl
  intro index _
  rfl

/-! ## Reusable primitive first-germ calculus

These two finite-dimensional maps expose the action-owned W13 bilinear
calculus without exposing any fixed residual or target coordinate.  The
global complete-joint development reuses them to transport its independently
generated primal/adjoint first germ into the Cartan response. -/

def lorentzSpinActionVector
    (variationDirection : LorentzianIndex) (internalPair : Fin 6)
    (matter : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ direction : LorentzianIndex,
      diracMatrixMatterAction (diracGamma direction)
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm
              (loweredLorentzBivectorOneFormCoordinate
                variationDirection internalPair)) direction)
          matter)

def lorentzSpinAction
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ direction : LorentzianIndex,
      (diracMatrixMatterAction (diracGamma direction)).comp
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm
              (loweredLorentzBivectorOneFormCoordinate
                variationDirection internalPair)) direction))

@[simp] theorem lorentzSpinAction_apply
    (variationDirection : LorentzianIndex) (internalPair : Fin 6)
    (matter : DiracExteriorMatterCarrier) :
    lorentzSpinAction variationDirection internalPair matter =
      lorentzSpinActionVector variationDirection internalPair matter := by
  simp [lorentzSpinAction, lorentzSpinActionVector]

def lorentzSpinCoordinateLinear
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
  ((matterCoordinateEquiv.toLinearMap.comp
      ((lorentzSpinAction variationDirection internalPair).comp
        matterCoordinateEquiv.symm.toLinearMap)).toContinuousLinearMap
    ).restrictScalars ℝ

@[simp] theorem lorentzSpinCoordinateLinear_apply
    (variationDirection : LorentzianIndex) (internalPair : Fin 6)
    (coordinates : MatterCoordinateCarrier) :
    lorentzSpinCoordinateLinear variationDirection internalPair coordinates =
      matterCoordinateEquiv
        (lorentzSpinActionVector variationDirection internalPair
          (matterCoordinateEquiv.symm coordinates)) := by
  rfl

def matterCoordinateRealPairingBilinear :
    MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier →ₗ[ℝ] ℝ :=
  matterCoordinatePairingReBilinear

@[simp] theorem matterCoordinateRealPairingBilinear_apply
    (first second : MatterCoordinateCarrier) :
    matterCoordinateRealPairingBilinear first second =
      ∑ index : MatterCoordinateIndex, (first index * second index).re := by
  rfl

theorem matterCoordinateRealPairingBilinear_matterDualCoordinates
    (first : MatterCoordinateCarrier)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterCoordinateRealPairingBilinear first
        (StageNineConjugateMatterVariation.matterDualCoordinates dual) =
      ∑ index : MatterCoordinateIndex,
        (first index * dual
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))).re :=
  matterCoordinatePairingRe_matterDualCoordinates first dual

private theorem fixed_frozenLorentzMatterCoefficient_contDiff
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiff ℝ ∞
      (fun point =>
        formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
          point
          (withCoframe
            (toContinuumPointField FixedP506JointActual point) 1)
          (loweredLorentzBivectorOneFormCoordinate
            variationDirection internalPair)) := by
  rw [fixed_frozenLorentzMatterCoefficient_coordinateExpansion]
  simp_rw [← matterCoordinatePairingRe_matterDualCoordinates]
  exact
    (matterCoordinatePairingReBilinear.toContinuousBilinearMap.contDiff.comp
      (fixed_current_lorentzSpinCoordinateVector_contDiff
        variationDirection internalPair)).clm_apply
      (StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterCoordinates_contDiff
        FixedP506JointActual fixedGlobalMatterDualP286Complete_smooth)

private theorem
    fixed_current_conjugateMatterCoordinates_temporalDerivative_zero :
    fieldDirectionalDerivative
        (StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterCoordinates
          FixedP506JointActual)
        0 canonicalLorentzianTimeDirection =
      0 := by
  have dualZero :
      holonomicConjugateMatterDerivativeDual FixedP506JointActual 0
          canonicalLorentzianTimeDirection =
        0 := by
    rw [fixed_current_adjointTemporal_eq_native,
      fixed_current_adjointActionVelocity_zero]
  change
    StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterDerivativeCoordinates
        FixedP506JointActual 0 canonicalLorentzianTimeDirection =
      0
  apply PiLp.ext
  intro index
  change
    StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterDerivativeCoordinates
          FixedP506JointActual 0 canonicalLorentzianTimeDirection index =
      (0 : ℂ)
  have evaluated := LinearMap.congr_fun dualZero
    (matterCoordinateEquiv.symm
      (EuclideanSpace.single index (1 : ℂ)))
  unfold holonomicConjugateMatterDerivativeDual at evaluated
  simpa only [
    StageNineConjugateMatterVariation.matterDualOfCoordinates_basis_apply,
    LinearMap.zero_apply] using evaluated

private theorem fixed_frozenLorentzMatterCoefficient_temporalDerivative_zero
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource
            0 point
            (withCoframe (toContinuumPointField FixedP506JointActual point) 1)
            (loweredLorentzBivectorOneFormCoordinate
              variationDirection internalPair))
      0 canonicalLorentzianTimeDirection =
      0 := by
  rw [fixed_frozenLorentzMatterCoefficient_coordinateExpansion]
  simp_rw [← matterCoordinatePairingRe_matterDualCoordinates]
  have derivative := fieldDirectionalDerivative_continuousBilinear
      matterCoordinatePairingReBilinear.toContinuousBilinearMap
      (fixed_current_lorentzSpinCoordinateVector
        variationDirection internalPair)
      (StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterCoordinates
        FixedP506JointActual)
      (fixed_current_lorentzSpinCoordinateVector_contDiff
        variationDirection internalPair)
      (StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterCoordinates_contDiff
        FixedP506JointActual fixedGlobalMatterDualP286Complete_smooth)
      0 canonicalLorentzianTimeDirection
  change
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinatePairingReBilinear
            (fixed_current_lorentzSpinCoordinateVector
              variationDirection internalPair point)
            (StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterCoordinates
              FixedP506JointActual point))
        0 canonicalLorentzianTimeDirection =
      matterCoordinatePairingReBilinear
          (fieldDirectionalDerivative
            (fixed_current_lorentzSpinCoordinateVector
              variationDirection internalPair)
            0 canonicalLorentzianTimeDirection)
          (StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterCoordinates
            FixedP506JointActual 0) +
        matterCoordinatePairingReBilinear
          (fixed_current_lorentzSpinCoordinateVector
            variationDirection internalPair 0)
          (fieldDirectionalDerivative
            (StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterCoordinates
              FixedP506JointActual)
            0 canonicalLorentzianTimeDirection) at derivative
  rw [
    fixed_current_lorentzSpinCoordinateVector_temporalDerivative_zero,
    fixed_current_conjugateMatterCoordinates_temporalDerivative_zero] at derivative
  have outerZero :
      matterCoordinatePairingReBilinear (0 : MatterCoordinateCarrier) = 0 :=
    matterCoordinatePairingReBilinear.map_zero
  have innerZero :
      matterCoordinatePairingReBilinear
          (fixed_current_lorentzSpinCoordinateVector
            variationDirection internalPair 0)
          (0 : MatterCoordinateCarrier) =
        0 :=
    (matterCoordinatePairingReBilinear
      (fixed_current_lorentzSpinCoordinateVector
        variationDirection internalPair 0)).map_zero
  rw [outerZero, LinearMap.zero_apply, innerZero, zero_add] at derivative
  simpa only [
    StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterCoordinates] using derivative

private def fixedFrozenSpinResponse (point : BasePoint) :
    PhysicalBivectorThreeForm :=
  diracDualFormNativeActionSpinResponsePointCoframe
    positiveSmoothUnifiedSource FixedP506JointActual (point, 1)

private theorem fixedFrozenSpinResponse_contDiff :
    ContDiff ℝ ∞ fixedFrozenSpinResponse := by
  rw [contDiff_iff_contDiffAt]
  intro point
  have outer :=
    diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
      positiveSmoothUnifiedSource FixedP506JointActual
      fixedGlobalMatterDualP286Complete_smooth point
      (1 : LorentzianCoframe) (by simp)
  have inner : ContDiffAt ℝ ∞
      (fun candidate : BasePoint =>
        (candidate, (1 : LorentzianCoframe))) point :=
    contDiffAt_id.prodMk contDiffAt_const
  exact outer.comp point inner

private theorem fixedFrozenSpinResponse_coordinate
    (point : BasePoint) (internalPair : Fin 6) (triple : Fin 4) :
    fixedFrozenSpinResponse point internalPair triple =
      -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
          point
          (withCoframe
            (toContinuumPointField FixedP506JointActual point) 1)
          (loweredLorentzBivectorOneFormCoordinate
            (missingTripleOfOneForm triple) internalPair)) := by
  unfold fixedFrozenSpinResponse
    diracDualFormNativeActionSpinResponsePointCoframe
    formNativePhysicalSpinCurrentThreeForm
  change
    -formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 point
        (withCoframe
          (toContinuumPointField FixedP506JointActual point) 1)
        internalPair triple =
      _
  conv_lhs =>
    rw [show triple = missingTripleOfOneForm
        (missingTripleOfOneForm triple) by
      exact (missingTripleOfOneForm_involutive triple).symm]
  rw [formNativeMatterSpinThreeForm_coordinate]

private theorem fieldDirectionalDerivative_const_mul_real_at_origin
    (field : BasePoint → ℝ)
    (fieldDifferentiable : DifferentiableAt ℝ field 0)
    (scalar : ℝ)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => scalar * field point)
        0 derivativeDirection =
      scalar * fieldDirectionalDerivative field 0 derivativeDirection := by
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul fieldDifferentiable scalar]
  rfl

private theorem fixedFrozenSpinResponse_coordinate_temporalDerivative_zero
    (internalPair : Fin 6) (triple : Fin 4) :
    fieldDirectionalDerivative
        (fun point => fixedFrozenSpinResponse point internalPair triple)
        0 canonicalLorentzianTimeDirection =
      0 := by
  let direction := missingTripleOfOneForm triple
  let coefficient : BasePoint → ℝ := fun point =>
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
      point
      (withCoframe
        (toContinuumPointField FixedP506JointActual point) 1)
      (loweredLorentzBivectorOneFormCoordinate direction internalPair)
  have coefficientDifferentiable : DifferentiableAt ℝ coefficient 0 := by
    exact
      ((fixed_frozenLorentzMatterCoefficient_contDiff direction internalPair
        ).differentiable (by simp)).differentiableAt
  rw [show
    (fun point => fixedFrozenSpinResponse point internalPair triple) =
      fun point => -(oneWedgeThreeSign direction * coefficient point) by
    funext point
    exact fixedFrozenSpinResponse_coordinate point internalPair triple]
  rw [show
    (fun point => -(oneWedgeThreeSign direction * coefficient point)) =
      fun point => (-oneWedgeThreeSign direction) * coefficient point by
    funext point
    ring]
  rw [fieldDirectionalDerivative_const_mul_real_at_origin coefficient
      coefficientDifferentiable (-oneWedgeThreeSign direction)
      canonicalLorentzianTimeDirection,
    fixed_frozenLorentzMatterCoefficient_temporalDerivative_zero]
  simp

private theorem fixedFrozenSpinResponse_temporalDerivative_zero :
    fieldDirectionalDerivative fixedFrozenSpinResponse 0
        canonicalLorentzianTimeDirection =
      0 := by
  funext internalPair triple
  rw [fieldDirectionalDerivative_pi_apply fixedFrozenSpinResponse
    fixedFrozenSpinResponse_contDiff 0 canonicalLorentzianTimeDirection
    internalPair]
  rw [fieldDirectionalDerivative_pi_apply
    (fun point => fixedFrozenSpinResponse point internalPair)
    (contDiff_pi.mp fixedFrozenSpinResponse_contDiff internalPair)
    0 canonicalLorentzianTimeDirection triple]
  exact fixedFrozenSpinResponse_coordinate_temporalDerivative_zero
    internalPair triple

private theorem fixedP506JointActual_fderiv_pointCoframe_eq_frozen
    (outer : BasePoint × LorentzianCoframe → PhysicalBivectorThreeForm)
    (outerDifferentiable : DifferentiableAt ℝ outer (0, 1))
    (direction : LorentzianIndex) :
    (fderiv ℝ
        (outer ∘ fun point =>
          (point, FixedP506JointActual.coframe point)) 0)
        (coordinateDirection direction) =
      (fderiv ℝ
        (outer ∘ fun point =>
          (point, (1 : LorentzianCoframe))) 0)
        (coordinateDirection direction) := by
  have actualInner :
      HasFDerivAt
        (fun point : BasePoint =>
          (point, FixedP506JointActual.coframe point))
        ((ContinuousLinearMap.id ℝ BasePoint).prod
          (fderiv ℝ FixedP506JointActual.coframe 0)) 0 :=
    HasFDerivAt.prodMk (hasFDerivAt_id (x := (0 : BasePoint)))
      fixedP506JointActual_coframe_differentiableAt.hasFDerivAt
  have frozenInner :
      HasFDerivAt
        (fun point : BasePoint =>
          (point, (1 : LorentzianCoframe)))
        ((ContinuousLinearMap.id ℝ BasePoint).prod
          (0 : BasePoint →L[ℝ] LorentzianCoframe)) 0 :=
    HasFDerivAt.prodMk (hasFDerivAt_id (x := (0 : BasePoint)))
      (hasFDerivAt_const (x := (0 : BasePoint))
        (c := (1 : LorentzianCoframe)))
  have outerAtActual : DifferentiableAt ℝ outer
      (0, FixedP506JointActual.coframe 0) := by
    simpa only [fixedP506JointActual_coframe_origin_one] using
      outerDifferentiable
  have actualComposition :=
    outerAtActual.hasFDerivAt.comp 0 actualInner
  have frozenComposition :=
    outerDifferentiable.hasFDerivAt.comp 0 frozenInner
  rw [actualComposition.fderiv, frozenComposition.fderiv,
    fixedP506JointActual_coframe_origin_one]
  change
    (fderiv ℝ outer (0, 1))
        (coordinateDirection direction,
          (fderiv ℝ FixedP506JointActual.coframe 0)
            (coordinateDirection direction)) =
      (fderiv ℝ outer (0, 1))
        (coordinateDirection direction, 0)
  rw [fixedP506JointActual_coframe_fderiv_coordinate_zero direction]

/-- The fixed action current's source-generated spin response has zero
temporal derivative at the origin.  This is a reusable action-data seam for
downstream Cartan-curvature calculations; it assumes no curvature target or
Hessian coordinate. -/
theorem fixed_current_spinResponse_temporalDerivative_zero :
    fieldDirectionalDerivative
        (diracDualFormNativeActionSpinResponseAt
          positiveSmoothUnifiedSource FixedP506JointActual)
        0 canonicalLorentzianTimeDirection =
      0 := by
  let outer :=
    diracDualFormNativeActionSpinResponsePointCoframe
      positiveSmoothUnifiedSource FixedP506JointActual
  have outerDifferentiable : DifferentiableAt ℝ outer (0, 1) :=
    (diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
      positiveSmoothUnifiedSource FixedP506JointActual
      fixedGlobalMatterDualP286Complete_smooth 0
      (1 : LorentzianCoframe) (by simp)).differentiableAt (by simp)
  have derivativeEquality :=
    fixedP506JointActual_fderiv_pointCoframe_eq_frozen outer
      outerDifferentiable canonicalLorentzianTimeDirection
  rw [show
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        FixedP506JointActual =
      outer ∘ fun point =>
        (point, FixedP506JointActual.coframe point) by
    funext point
    exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
      positiveSmoothUnifiedSource FixedP506JointActual point]
  unfold fieldDirectionalDerivative
  rw [derivativeEquality]
  have frozenZero := fixedFrozenSpinResponse_temporalDerivative_zero
  unfold fieldDirectionalDerivative fixedFrozenSpinResponse at frozenZero
  change
    (fderiv ℝ
        (outer ∘ fun point => (point, (1 : LorentzianCoframe))) 0)
        (coordinateDirection canonicalLorentzianTimeDirection) =
      0 at frozenZero
  exact frozenZero

private theorem fixed_input_coframe_eq_current :
    FixedP506FormNativeJointActionSolvedSuccessor.coframe =
      FixedP506JointActual.coframe := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe]

private theorem fixed_input_matter_eq_current :
    FixedP506FormNativeJointActionSolvedSuccessor.matter =
      FixedP506JointActual.matter := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]

private theorem fixed_input_conjugateMatter_eq_current :
    FixedP506FormNativeJointActionSolvedSuccessor.conjugateMatter =
      FixedP506JointActual.conjugateMatter := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
    fixedP506JointActionSuccessor_conjugateMatter]

private theorem fixed_input_spinResponse_eq_current :
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor =
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        FixedP506JointActual := by
  funext point
  exact diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
    positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor FixedP506JointActual point
    (congrFun fixed_input_coframe_eq_current point)
    (congrFun fixed_input_matter_eq_current point)
    (congrFun fixed_input_conjugateMatter_eq_current point)

private theorem fixed_input_coframe_origin_one :
    FixedP506FormNativeJointActionSolvedSuccessor.coframe 0 = 1 := by
  rw [fixed_input_coframe_eq_current,
    fixedP506JointActual_coframe_origin_one]

private theorem fixed_input_coframe_differentiableAt :
    DifferentiableAt ℝ
      FixedP506FormNativeJointActionSolvedSuccessor.coframe 0 := by
  rw [fixed_input_coframe_eq_current]
  exact fixedP506JointActual_coframe_differentiableAt

private theorem fixed_input_spinResponse_differentiableAt :
    DifferentiableAt ℝ
      (diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor) 0 := by
  rw [fixed_input_spinResponse_eq_current]
  let outer :=
    diracDualFormNativeActionSpinResponsePointCoframe
      positiveSmoothUnifiedSource FixedP506JointActual
  have outerDifferentiable : DifferentiableAt ℝ outer (0, 1) :=
    (diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
      positiveSmoothUnifiedSource FixedP506JointActual
      fixedGlobalMatterDualP286Complete_smooth 0
      (1 : LorentzianCoframe) (by simp)).differentiableAt (by simp)
  have innerDifferentiable : DifferentiableAt ℝ
      (fun point : BasePoint =>
        (point, FixedP506JointActual.coframe point)) 0 :=
    differentiableAt_id.prodMk fixedP506JointActual_coframe_differentiableAt
  have outerAtActual : DifferentiableAt ℝ outer
      (0, FixedP506JointActual.coframe 0) := by
    simpa only [fixedP506JointActual_coframe_origin_one] using
      outerDifferentiable
  rw [show
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        FixedP506JointActual =
      outer ∘ fun point =>
        (point, FixedP506JointActual.coframe point) by
    funext point
    exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
      positiveSmoothUnifiedSource FixedP506JointActual point]
  exact outerAtActual.comp 0 innerDifferentiable

private def fixedInputCoframeSpinResponseCarrier (point : BasePoint) :
    LorentzianCoframe × PhysicalBivectorThreeForm :=
  (FixedP506FormNativeJointActionSolvedSuccessor.coframe point,
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor point)

private theorem fixedInputCoframeSpinResponseCarrier_differentiableAt :
    DifferentiableAt ℝ fixedInputCoframeSpinResponseCarrier 0 :=
  fixed_input_coframe_differentiableAt.prodMk
    fixed_input_spinResponse_differentiableAt

private theorem
    fixedInputCoframeSpinResponseCarrier_temporalDerivative_zero :
    fieldDirectionalDerivative fixedInputCoframeSpinResponseCarrier 0
        canonicalLorentzianTimeDirection =
      0 := by
  have productDerivative :=
    fixed_input_coframe_differentiableAt.fderiv_prodMk
      fixed_input_spinResponse_differentiableAt
  unfold fieldDirectionalDerivative fixedInputCoframeSpinResponseCarrier
  rw [productDerivative]
  change
    ((fderiv ℝ FixedP506FormNativeJointActionSolvedSuccessor.coframe 0)
        (coordinateDirection canonicalLorentzianTimeDirection),
      (fderiv ℝ
          (diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor) 0)
        (coordinateDirection canonicalLorentzianTimeDirection)) =
      0
  rw [fixed_input_coframe_eq_current,
    fixedP506JointActual_coframe_fderiv_coordinate_zero,
    fixed_input_spinResponse_eq_current]
  change
    (0,
      fieldDirectionalDerivative
        (diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
          FixedP506JointActual) 0 canonicalLorentzianTimeDirection) =
      0
  rw [fixed_current_spinResponse_temporalDerivative_zero]
  rfl

private theorem fixed_input_cartanContorsion_component_temporalDerivative_zero
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor point
            formDirection internalPair)
        0 canonicalLorentzianTimeDirection =
      0 := by
  let response :=
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor 0
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have carrierOrigin : fixedInputCoframeSpinResponseCarrier 0 =
      ((1 : LorentzianCoframe), response) := by
    unfold fixedInputCoframeSpinResponseCarrier response
    rw [fixed_input_coframe_origin_one]
  have outerDifferentiable : DifferentiableAt ℝ outer
      (fixedInputCoframeSpinResponseCarrier 0) := by
    rw [carrierOrigin]
    exact
      (cartanContorsionCoframeResponseComponent_contDiffAt
        (1 : LorentzianCoframe) response (by simp)
        formDirection internalPair).differentiableAt (by simp)
  have composition := outerDifferentiable.hasFDerivAt.comp 0
    fixedInputCoframeSpinResponseCarrier_differentiableAt.hasFDerivAt
  rw [show
    (fun point =>
      diracDualFormNativeActionCartanContorsionAt
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor point
        formDirection internalPair) =
      outer ∘ fixedInputCoframeSpinResponseCarrier by rfl]
  unfold fieldDirectionalDerivative
  rw [composition.fderiv]
  change
    (fderiv ℝ outer (fixedInputCoframeSpinResponseCarrier 0))
        (fieldDirectionalDerivative fixedInputCoframeSpinResponseCarrier 0
          canonicalLorentzianTimeDirection) =
      0
  rw [fixedInputCoframeSpinResponseCarrier_temporalDerivative_zero]
  simp

private theorem fixed_input_cartanSkew_131_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt
              positiveSmoothUnifiedSource
              FixedP506FormNativeJointActionSolvedSuccessor point)
            1 3 1)
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    fixed_input_cartanContorsion_component_temporalDerivative_zero 1 4

private theorem fixed_input_cartanSkew_223_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt
              positiveSmoothUnifiedSource
              FixedP506FormNativeJointActionSolvedSuccessor point)
            2 2 3)
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    fixed_input_cartanContorsion_component_temporalDerivative_zero 2 3

private theorem fixed_input_cartanSkew_323_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt
              positiveSmoothUnifiedSource
              FixedP506FormNativeJointActionSolvedSuccessor point)
            3 2 3)
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    fixed_input_cartanContorsion_component_temporalDerivative_zero 3 3

private theorem fixed_input_cartanSkew_112_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt
              positiveSmoothUnifiedSource
              FixedP506FormNativeJointActionSolvedSuccessor point)
            1 1 2)
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    fixed_input_cartanContorsion_component_temporalDerivative_zero 1 5

private theorem fixed_input_coframe_eq_primitive :
    FixedP506FormNativeJointActionSolvedSuccessor.coframe =
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe := by
  rw [fixed_input_coframe_eq_current,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]

private theorem canonicalZeroSliceOrigin :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem fixed_input_coframeComponent_contDiff
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ ∞
      (fun point =>
        FixedP506FormNativeJointActionSolvedSuccessor.coframe point
          internal coordinate) :=
  fixedP506FormNativeJointActionSolvedSuccessor_smooth.1 internal coordinate

private theorem fixed_input_coframeComponent_temporal_zeroSlice
    (space : StageNineSpatialPoint)
    (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point
            internal coordinate)
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      0 := by
  have jet := congrArg
    (fun actual =>
      actual.derivative canonicalLorentzianTimeDirection internal coordinate)
    (fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space)
  rw [← fixed_input_coframe_eq_primitive] at jet
  simpa [holonomicCoframeFirstJetAt, fieldDirectionalDerivative] using jet

private theorem
    fixed_input_coframeComponent_temporalDerivative_spatial_zero
    (axis : Fin 3) (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          fieldDirectionalDerivative
            (fun candidate =>
              FixedP506FormNativeJointActionSolvedSuccessor.coframe candidate
                internal coordinate)
            point canonicalLorentzianTimeDirection)
        0 axis.succ =
      0 := by
  let component : BasePoint → ℝ := fun point =>
    FixedP506FormNativeJointActionSolvedSuccessor.coframe point
      internal coordinate
  let temporalField : BasePoint → ℝ := fun point =>
    fieldDirectionalDerivative component point
      canonicalLorentzianTimeDirection
  have componentSmooth : ContDiff ℝ ∞ component :=
    fixed_input_coframeComponent_contDiff internal coordinate
  have temporalSmooth : ContDiff ℝ ∞ temporalField := by
    have derivativeSmooth : ContDiff ℝ ∞ (fderiv ℝ component) :=
      componentSmooth.fderiv_right (m := ∞) (by simp)
    exact derivativeSmooth.clm_apply contDiff_const
  have temporalDifferentiable : DifferentiableAt ℝ temporalField
      (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) :=
    (temporalSmooth.differentiable (by simp)).differentiableAt
  have sliceDerivative := temporalDifferentiable.hasFDerivAt.comp
    (0 : StageNineSpatialPoint)
    (canonicalCauchySlicePoint_hasFDerivAt 0 0)
  have sliceZero : temporalField ∘ canonicalCauchySlicePoint 0 =
      fun _ : StageNineSpatialPoint => 0 := by
    funext space
    exact fixed_input_coframeComponent_temporal_zeroSlice
      space internal coordinate
  have sliceFderivZero :
      fderiv ℝ (temporalField ∘ canonicalCauchySlicePoint 0)
          (0 : StageNineSpatialPoint) =
        0 := by
    rw [sliceZero]
    simp
  rw [sliceDerivative.fderiv] at sliceFderivZero
  have applied := congrArg
    (fun derivative : StageNineSpatialPoint →L[ℝ] ℝ =>
      derivative (canonicalSpatialCoordinateDirection axis))
    sliceFderivZero
  unfold fieldDirectionalDerivative
  change
    (fderiv ℝ temporalField 0) (coordinateDirection axis.succ) = 0
  simpa [component, temporalField, canonicalZeroSliceOrigin,
    ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection] using applied

theorem fixed_input_coframeComponent_mixed_temporal_spatial_zero
    (axis : Fin 3) (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          fieldDirectionalDerivative
            (fun candidate =>
              FixedP506FormNativeJointActionSolvedSuccessor.coframe candidate
                internal coordinate)
            point axis.succ)
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [mixedRealFieldDirectionalDerivative_comm
    (fun point =>
      FixedP506FormNativeJointActionSolvedSuccessor.coframe point
        internal coordinate)
    (fixed_input_coframeComponent_contDiff internal coordinate)
    0 axis.succ canonicalLorentzianTimeDirection]
  exact fixed_input_coframeComponent_temporalDerivative_spatial_zero
    axis internal coordinate

private def fixedInputCoframeJetCarrier
    (point : BasePoint) : IdentityECCoframeJetCarrier :=
  (FixedP506FormNativeJointActionSolvedSuccessor.coframe point,
    (holonomicCoframeFirstJetAt
      FixedP506FormNativeJointActionSolvedSuccessor.coframe point).derivative)

private def fixedInputFrozenCoframeJetCarrier
    (point : BasePoint) : IdentityECCoframeJetCarrier :=
  ((1 : LorentzianCoframe),
    (holonomicCoframeFirstJetAt
      FixedP506FormNativeJointActionSolvedSuccessor.coframe point).derivative)

private theorem fixedInputCoframeJetCarrier_contDiff :
    ContDiff ℝ ∞ fixedInputCoframeJetCarrier := by
  have coframeSmooth : ContDiff ℝ ∞
      FixedP506FormNativeJointActionSolvedSuccessor.coframe := by
    apply contDiff_pi'
    intro internal
    apply contDiff_pi'
    intro coordinate
    exact fixed_input_coframeComponent_contDiff internal coordinate
  refine coframeSmooth.prodMk ?_
  apply contDiff_pi'
  intro derivativeDirection
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  let component : BasePoint → ℝ := fun point =>
    FixedP506FormNativeJointActionSolvedSuccessor.coframe point
      internal coordinate
  have componentSmooth : ContDiff ℝ ∞ component :=
    fixed_input_coframeComponent_contDiff internal coordinate
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry (fun _ : BasePoint => component)) :=
    componentSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ component point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  change ContDiff ℝ ∞
    (fun point =>
      fderiv ℝ component point
        (coordinateDirection derivativeDirection))
  exact derivativeSmooth.clm_apply contDiff_const

private theorem fixedInputFrozenCoframeJetCarrier_contDiff :
    ContDiff ℝ ∞ fixedInputFrozenCoframeJetCarrier := by
  exact contDiff_const.prodMk
    (contDiff_snd.comp fixedInputCoframeJetCarrier_contDiff)

private theorem fixedInputCoframeJetCarrier_origin :
    fixedInputCoframeJetCarrier 0 =
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)) := by
  have jet :
      holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) =
        ({ coframe := 1, derivative := 0 } :
          PointwiseLorentzianCoframeJet) := by
    rw [fixed_input_coframe_eq_primitive]
    exact fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice 0
  rw [canonicalZeroSliceOrigin] at jet
  exact congrArg (fun actual => (actual.coframe, actual.derivative)) jet

private theorem fixedInputFrozenCoframeJetCarrier_origin :
    fixedInputFrozenCoframeJetCarrier 0 =
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)) := by
  have derivativeOrigin := congrArg Prod.snd fixedInputCoframeJetCarrier_origin
  simpa [fixedInputCoframeJetCarrier,
    fixedInputFrozenCoframeJetCarrier] using derivativeOrigin

private theorem fixedInputCoframeJetCarrier_temporalDerivative_eq_frozen :
    fieldDirectionalDerivative fixedInputCoframeJetCarrier 0
        canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative fixedInputFrozenCoframeJetCarrier 0
        canonicalLorentzianTimeDirection := by
  let derivativeField : BasePoint → LorentzianCoframeDerivative :=
    fun point =>
      (holonomicCoframeFirstJetAt
        FixedP506FormNativeJointActionSolvedSuccessor.coframe point).derivative
  have derivativeFieldDifferentiable : DifferentiableAt ℝ derivativeField 0 := by
    exact ((contDiff_snd.comp fixedInputCoframeJetCarrier_contDiff).differentiable
      (by simp)).differentiableAt
  have actualProductDerivative :=
    fixed_input_coframe_differentiableAt.fderiv_prodMk
      derivativeFieldDifferentiable
  have frozenProductDerivative :=
    (differentiableAt_const (c := (1 : LorentzianCoframe))).fderiv_prodMk
      derivativeFieldDifferentiable
  unfold fieldDirectionalDerivative fixedInputCoframeJetCarrier
    fixedInputFrozenCoframeJetCarrier
  change
    (fderiv ℝ
        (fun point =>
          (FixedP506FormNativeJointActionSolvedSuccessor.coframe point,
            derivativeField point)) 0)
        (coordinateDirection canonicalLorentzianTimeDirection) =
      (fderiv ℝ
        (fun point => ((1 : LorentzianCoframe), derivativeField point)) 0)
        (coordinateDirection canonicalLorentzianTimeDirection)
  let direction := coordinateDirection canonicalLorentzianTimeDirection
  calc
    _ = ((fderiv ℝ
          FixedP506FormNativeJointActionSolvedSuccessor.coframe 0).prod
          (fderiv ℝ derivativeField 0)) direction :=
      congrArg (fun derivative => derivative direction)
        actualProductDerivative
    _ = ((0 : BasePoint →L[ℝ] LorentzianCoframe).prod
          (fderiv ℝ derivativeField 0)) direction := by
      change
        ((fderiv ℝ
          FixedP506FormNativeJointActionSolvedSuccessor.coframe 0)
            direction,
          (fderiv ℝ derivativeField 0) direction) =
        (0, (fderiv ℝ derivativeField 0) direction)
      rw [fixed_input_coframe_eq_current,
        fixedP506JointActual_coframe_fderiv_coordinate_zero]
    _ = ((fderiv ℝ (fun _ : BasePoint => (1 : LorentzianCoframe)) 0).prod
          (fderiv ℝ derivativeField 0)) direction := by
      simp
    _ = (fderiv ℝ
          (fun point => ((1 : LorentzianCoframe), derivativeField point)) 0)
          direction :=
      (congrArg (fun derivative => derivative direction)
        frozenProductDerivative).symm

private theorem fixed_input_coframeDerivativeComponent_contDiff
    (derivativeDirection internal coordinate : LorentzianIndex) :
    ContDiff ℝ ∞
      (fun point =>
        (holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point).derivative
            derivativeDirection internal coordinate) := by
  let component : BasePoint → ℝ := fun point =>
    FixedP506FormNativeJointActionSolvedSuccessor.coframe point
      internal coordinate
  have componentSmooth : ContDiff ℝ ∞ component :=
    fixed_input_coframeComponent_contDiff internal coordinate
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry (fun _ : BasePoint => component)) :=
    componentSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ component point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  change ContDiff ℝ ∞
    (fun point =>
      fderiv ℝ component point
        (coordinateDirection derivativeDirection))
  exact derivativeSmooth.clm_apply contDiff_const

private theorem fieldDirectionalDerivative_sub_real_at_origin
    (first second : BasePoint → ℝ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => first point - second point)
        0 direction =
      fieldDirectionalDerivative first 0 direction -
        fieldDirectionalDerivative second 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_sub firstDifferentiable secondDifferentiable]
  rfl

private theorem fixed_input_leviCivita_component_differentiableAt
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        identityECSpinConnectionComponentOfCarrier
          formDirection internalOut internalIn
          (fixedInputCoframeJetCarrier point)) 0 := by
  let outer := identityECSpinConnectionComponentOfCarrier
    formDirection internalOut internalIn
  have outerAt : DifferentiableAt ℝ outer
      (fixedInputCoframeJetCarrier 0) := by
    rw [fixedInputCoframeJetCarrier_origin]
    exact identityECSpinConnectionComponentOfCarrier_differentiableAt
      formDirection internalOut internalIn
  exact outerAt.comp 0
    ((fixedInputCoframeJetCarrier_contDiff.differentiable
      (by simp)).differentiableAt)

private theorem fixed_input_frozenLeviCivita_component_differentiableAt
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        identityECSpinConnectionComponentOfCarrier
          formDirection internalOut internalIn
          (fixedInputFrozenCoframeJetCarrier point)) 0 := by
  let outer := identityECSpinConnectionComponentOfCarrier
    formDirection internalOut internalIn
  have outerAt : DifferentiableAt ℝ outer
      (fixedInputFrozenCoframeJetCarrier 0) := by
    rw [fixedInputFrozenCoframeJetCarrier_origin]
    exact identityECSpinConnectionComponentOfCarrier_differentiableAt
      formDirection internalOut internalIn
  exact outerAt.comp 0
    ((fixedInputFrozenCoframeJetCarrier_contDiff.differentiable
      (by simp)).differentiableAt)

private theorem
    fixed_input_leviCivita_component_temporalDerivative_eq_frozen
    (formDirection internalOut internalIn : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier
            formDirection internalOut internalIn
            (fixedInputCoframeJetCarrier point))
        0 canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier
            formDirection internalOut internalIn
            (fixedInputFrozenCoframeJetCarrier point))
        0 canonicalLorentzianTimeDirection := by
  let outer := identityECSpinConnectionComponentOfCarrier
    formDirection internalOut internalIn
  have outerDifferentiable : DifferentiableAt ℝ outer
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)) :=
    identityECSpinConnectionComponentOfCarrier_differentiableAt
      formDirection internalOut internalIn
  have actualInner : HasFDerivAt fixedInputCoframeJetCarrier
      (fderiv ℝ fixedInputCoframeJetCarrier 0) 0 :=
    ((fixedInputCoframeJetCarrier_contDiff.differentiable
      (by simp)).differentiableAt).hasFDerivAt
  have frozenInner : HasFDerivAt fixedInputFrozenCoframeJetCarrier
      (fderiv ℝ fixedInputFrozenCoframeJetCarrier 0) 0 :=
    ((fixedInputFrozenCoframeJetCarrier_contDiff.differentiable
      (by simp)).differentiableAt).hasFDerivAt
  have actualOuterAt : DifferentiableAt ℝ outer
      (fixedInputCoframeJetCarrier 0) := by
    simpa only [fixedInputCoframeJetCarrier_origin] using
      outerDifferentiable
  have frozenOuterAt : DifferentiableAt ℝ outer
      (fixedInputFrozenCoframeJetCarrier 0) := by
    simpa only [fixedInputFrozenCoframeJetCarrier_origin] using
      outerDifferentiable
  have actualComposition :=
    actualOuterAt.hasFDerivAt.comp 0 actualInner
  have frozenComposition :=
    frozenOuterAt.hasFDerivAt.comp 0 frozenInner
  change
    fieldDirectionalDerivative (outer ∘ fixedInputCoframeJetCarrier)
        0 canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative
        (outer ∘ fixedInputFrozenCoframeJetCarrier)
        0 canonicalLorentzianTimeDirection
  unfold fieldDirectionalDerivative
  rw [actualComposition.fderiv, frozenComposition.fderiv,
    fixedInputCoframeJetCarrier_origin,
    fixedInputFrozenCoframeJetCarrier_origin]
  change
    (fderiv ℝ outer
        ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)))
        ((fderiv ℝ fixedInputCoframeJetCarrier 0)
          (coordinateDirection canonicalLorentzianTimeDirection)) =
      (fderiv ℝ outer
        ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)))
        ((fderiv ℝ fixedInputFrozenCoframeJetCarrier 0)
          (coordinateDirection canonicalLorentzianTimeDirection))
  exact congrArg
    (fderiv ℝ outer
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)))
    fixedInputCoframeJetCarrier_temporalDerivative_eq_frozen

/-- At the identity contact, the actual fixed-input Levi--Civita temporal
derivative can be read through the public identity-coframe jet producer.
The frozen carrier remains an implementation detail. -/
theorem fixed_input_leviCivita_component_temporalDerivative_eq_identityJet
    (formDirection internalOut internalIn : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier
            formDirection internalOut internalIn
            (FixedP506FormNativeJointActionSolvedSuccessor.coframe point,
              (holonomicCoframeFirstJetAt
                FixedP506FormNativeJointActionSolvedSuccessor.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative
        (fun point =>
          (identityECCoframeJetOfDerivative
              (holonomicCoframeFirstJetAt
                FixedP506FormNativeJointActionSolvedSuccessor.coframe point
                ).derivative).lorentzSpinConnection
            formDirection internalOut internalIn)
        0 canonicalLorentzianTimeDirection := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier
            formDirection internalOut internalIn
            (fixedInputCoframeJetCarrier point))
        0 canonicalLorentzianTimeDirection = _
  rw [fixed_input_leviCivita_component_temporalDerivative_eq_frozen]
  rfl

private theorem fixed_input_frozenLeviCivita_131_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 3 1
            (fixedInputFrozenCoframeJetCarrier point))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [show
    (fun point =>
      identityECSpinConnectionComponentOfCarrier 1 3 1
        (fixedInputFrozenCoframeJetCarrier point)) =
      (fun point =>
        (holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point).derivative
            1 1 3 -
        (holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point).derivative
            3 1 1) by
    funext point
    exact identityECSpinConnectionComponentOfCarrier_one_131 _]
  rw [fieldDirectionalDerivative_sub_real_at_origin _ _
    (fixed_input_coframeDerivativeComponent_contDiff 1 1 3
      |>.differentiable (by simp) |>.differentiableAt)
    (fixed_input_coframeDerivativeComponent_contDiff 3 1 1
      |>.differentiable (by simp) |>.differentiableAt)
    canonicalLorentzianTimeDirection]
  have firstZero :=
    fixed_input_coframeComponent_mixed_temporal_spatial_zero
      (0 : Fin 3) 1 3
  have secondZero :=
    fixed_input_coframeComponent_mixed_temporal_spatial_zero
      (2 : Fin 3) 1 1
  simpa [holonomicCoframeFirstJetAt, fieldDirectionalDerivative] using
    sub_eq_zero.mpr (firstZero.trans secondZero.symm)

private theorem fixed_input_frozenLeviCivita_223_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 2 2 3
            (fixedInputFrozenCoframeJetCarrier point))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [show
    (fun point =>
      identityECSpinConnectionComponentOfCarrier 2 2 3
        (fixedInputFrozenCoframeJetCarrier point)) =
      (fun point =>
        (holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point).derivative
            3 2 2 -
        (holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point).derivative
            2 2 3) by
    funext point
    exact identityECSpinConnectionComponentOfCarrier_one_223 _]
  rw [fieldDirectionalDerivative_sub_real_at_origin _ _
    (fixed_input_coframeDerivativeComponent_contDiff 3 2 2
      |>.differentiable (by simp) |>.differentiableAt)
    (fixed_input_coframeDerivativeComponent_contDiff 2 2 3
      |>.differentiable (by simp) |>.differentiableAt)
    canonicalLorentzianTimeDirection]
  have firstZero :=
    fixed_input_coframeComponent_mixed_temporal_spatial_zero
      (2 : Fin 3) 2 2
  have secondZero :=
    fixed_input_coframeComponent_mixed_temporal_spatial_zero
      (1 : Fin 3) 2 3
  simpa [holonomicCoframeFirstJetAt, fieldDirectionalDerivative] using
    sub_eq_zero.mpr (firstZero.trans secondZero.symm)

private theorem fixed_input_leviCivita_131_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 3 1
            (fixedInputCoframeJetCarrier point))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [fixed_input_leviCivita_component_temporalDerivative_eq_frozen]
  exact fixed_input_frozenLeviCivita_131_temporalDerivative_zero

private theorem fixed_input_leviCivita_223_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 2 2 3
            (fixedInputCoframeJetCarrier point))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [fixed_input_leviCivita_component_temporalDerivative_eq_frozen]
  exact fixed_input_frozenLeviCivita_223_temporalDerivative_zero

private theorem fixed_minkowskiInternalMetric_inv_probe :
    minkowskiInternalMetric⁻¹ = minkowskiInternalMetric := by
  apply Matrix.inv_eq_left_inv
  rw [minkowskiInternalMetric, Matrix.diagonal_mul_diagonal]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num

private theorem fixed_identityCoframeMetric_inv_probe :
    (lorentzianMetricOfCoframe (1 : LorentzianCoframe))⁻¹ =
      minkowskiInternalMetric := by
  rw [show lorentzianMetricOfCoframe (1 : LorentzianCoframe) =
      minkowskiInternalMetric by
    simp [lorentzianMetricOfCoframe]]
  exact fixed_minkowskiInternalMetric_inv_probe

private theorem fixed_identityECSpinConnectionComponent_one_323
    (derivative : LorentzianCoframeDerivative) :
    identityECSpinConnectionComponentOfCarrier 3 2 3
        ((1 : LorentzianCoframe), derivative) =
      derivative 3 3 2 - derivative 2 3 3 := by
  unfold identityECSpinConnectionComponentOfCarrier
    pointwiseCoframeJetOfCarrier
    PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
    PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
    PointwiseLorentzianCoframeJet.metric
    PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    PointwiseLorentzianCoframeJet.metricDerivative
  rw [fixed_identityCoframeMetric_inv_probe]
  simp +decide [Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.one_apply, minkowskiInternalMetric, Matrix.diagonal_apply,
    minkowskiInternalSign, Fin.sum_univ_four]
  ring

private theorem fixed_identityECSpinConnectionComponent_one_112
    (derivative : LorentzianCoframeDerivative) :
    identityECSpinConnectionComponentOfCarrier 1 1 2
        ((1 : LorentzianCoframe), derivative) =
      derivative 2 1 1 - derivative 1 1 2 := by
  unfold identityECSpinConnectionComponentOfCarrier
    pointwiseCoframeJetOfCarrier
    PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
    PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
    PointwiseLorentzianCoframeJet.metric
    PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    PointwiseLorentzianCoframeJet.metricDerivative
  rw [fixed_identityCoframeMetric_inv_probe]
  simp +decide [Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.one_apply, minkowskiInternalMetric, Matrix.diagonal_apply,
    minkowskiInternalSign, Fin.sum_univ_four]

private theorem fixed_input_coframeDerivative_mixed_temporal_spatial_zero
    (axis : Fin 3) (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt
            FixedP506FormNativeJointActionSolvedSuccessor.coframe point
            ).derivative axis.succ internal coordinate)
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa [holonomicCoframeFirstJetAt, fieldDirectionalDerivative] using
    fixed_input_coframeComponent_mixed_temporal_spatial_zero
      axis internal coordinate

private theorem fixed_input_leviCivita_323_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 3 2 3
            (fixedInputCoframeJetCarrier point))
        0 canonicalLorentzianTimeDirection =
      0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 3 2 3
            (FixedP506FormNativeJointActionSolvedSuccessor.coframe point,
              (holonomicCoframeFirstJetAt
                FixedP506FormNativeJointActionSolvedSuccessor.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection =
      0
  rw [fixed_input_leviCivita_component_temporalDerivative_eq_identityJet]
  rw [show
    (fun point =>
      (identityECCoframeJetOfDerivative
        (holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point
          ).derivative).lorentzSpinConnection 3 2 3) =
      (fun point =>
        (holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point
          ).derivative 3 3 2 -
        (holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point
          ).derivative 2 3 3) by
    funext point
    exact fixed_identityECSpinConnectionComponent_one_323 _]
  rw [fieldDirectionalDerivative_sub_real_at_origin _ _
    ((fixed_input_coframeDerivativeComponent_contDiff 3 3 2).differentiable
      (by simp) |>.differentiableAt)
    ((fixed_input_coframeDerivativeComponent_contDiff 2 3 3).differentiable
      (by simp) |>.differentiableAt)
    canonicalLorentzianTimeDirection,
    show fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt
            FixedP506FormNativeJointActionSolvedSuccessor.coframe point
            ).derivative 3 3 2)
        0 canonicalLorentzianTimeDirection = 0 by
      simpa using fixed_input_coframeDerivative_mixed_temporal_spatial_zero
        (2 : Fin 3) 3 2,
    show fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt
            FixedP506FormNativeJointActionSolvedSuccessor.coframe point
            ).derivative 2 3 3)
        0 canonicalLorentzianTimeDirection = 0 by
      simpa using fixed_input_coframeDerivative_mixed_temporal_spatial_zero
        (1 : Fin 3) 3 3]
  norm_num

private theorem fixed_input_leviCivita_112_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 1 2
            (fixedInputCoframeJetCarrier point))
        0 canonicalLorentzianTimeDirection =
      0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 1 2
            (FixedP506FormNativeJointActionSolvedSuccessor.coframe point,
              (holonomicCoframeFirstJetAt
                FixedP506FormNativeJointActionSolvedSuccessor.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection =
      0
  rw [fixed_input_leviCivita_component_temporalDerivative_eq_identityJet]
  rw [show
    (fun point =>
      (identityECCoframeJetOfDerivative
        (holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point
          ).derivative).lorentzSpinConnection 1 1 2) =
      (fun point =>
        (holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point
          ).derivative 2 1 1 -
        (holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point
          ).derivative 1 1 2) by
    funext point
    exact fixed_identityECSpinConnectionComponent_one_112 _]
  rw [fieldDirectionalDerivative_sub_real_at_origin _ _
    ((fixed_input_coframeDerivativeComponent_contDiff 2 1 1).differentiable
      (by simp) |>.differentiableAt)
    ((fixed_input_coframeDerivativeComponent_contDiff 1 1 2).differentiable
      (by simp) |>.differentiableAt)
    canonicalLorentzianTimeDirection,
    show fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt
            FixedP506FormNativeJointActionSolvedSuccessor.coframe point
            ).derivative 2 1 1)
        0 canonicalLorentzianTimeDirection = 0 by
      simpa using fixed_input_coframeDerivative_mixed_temporal_spatial_zero
        (1 : Fin 3) 1 1,
    show fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt
            FixedP506FormNativeJointActionSolvedSuccessor.coframe point
            ).derivative 1 1 2)
        0 canonicalLorentzianTimeDirection = 0 by
      simpa using fixed_input_coframeDerivative_mixed_temporal_spatial_zero
        (0 : Fin 3) 1 2]
  norm_num

private theorem fixed_input_cartanContorsion_component_differentiableAt
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    DifferentiableAt ℝ
      (fun point =>
        diracDualFormNativeActionCartanContorsionAt
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor point
          formDirection internalPair) 0 := by
  let response :=
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor 0
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have carrierOrigin : fixedInputCoframeSpinResponseCarrier 0 =
      ((1 : LorentzianCoframe), response) := by
    unfold fixedInputCoframeSpinResponseCarrier response
    rw [fixed_input_coframe_origin_one]
  have outerDifferentiable : DifferentiableAt ℝ outer
      (fixedInputCoframeSpinResponseCarrier 0) := by
    rw [carrierOrigin]
    exact
      (cartanContorsionCoframeResponseComponent_contDiffAt
        (1 : LorentzianCoframe) response (by simp)
        formDirection internalPair).differentiableAt (by simp)
  change DifferentiableAt ℝ
    (outer ∘ fixedInputCoframeSpinResponseCarrier) 0
  exact outerDifferentiable.comp 0
    fixedInputCoframeSpinResponseCarrier_differentiableAt

private theorem fixed_input_cartanSkew_131_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor point)
          1 3 1) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    fixed_input_cartanContorsion_component_differentiableAt 1 4

private theorem fixed_input_cartanSkew_223_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor point)
          2 2 3) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    fixed_input_cartanContorsion_component_differentiableAt 2 3

private theorem fixed_input_cartanSkew_323_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor point)
          3 2 3) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    fixed_input_cartanContorsion_component_differentiableAt 3 3

private theorem fixed_input_cartanSkew_112_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor point)
          1 1 2) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    fixed_input_cartanContorsion_component_differentiableAt 1 5

private theorem fixed_fieldDirectionalDerivative_add_real_at_origin
    (first second : BasePoint → ℝ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => first point + second point)
        0 direction =
      fieldDirectionalDerivative first 0 direction +
        fieldDirectionalDerivative second 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add firstDifferentiable secondDifferentiable]
  rfl

private theorem fixed_input_cartanConnection_131_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor point
            1 3 1)
        0 canonicalLorentzianTimeDirection =
      0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 3 1
              (fixedInputCoframeJetCarrier point) +
            lorentzSkewConnectionOfBivectorOneForm
              (diracDualFormNativeActionCartanContorsionAt
                positiveSmoothUnifiedSource
                FixedP506FormNativeJointActionSolvedSuccessor point)
              1 3 1)
        0 canonicalLorentzianTimeDirection =
      0
  rw [fixed_fieldDirectionalDerivative_add_real_at_origin _ _
    (fixed_input_leviCivita_component_differentiableAt 1 3 1)
    fixed_input_cartanSkew_131_differentiableAt
    canonicalLorentzianTimeDirection,
    fixed_input_leviCivita_131_temporalDerivative_zero,
    fixed_input_cartanSkew_131_temporalDerivative_zero]
  norm_num

private theorem fixed_input_cartanConnection_223_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor point
            2 2 3)
        0 canonicalLorentzianTimeDirection =
      0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 2 2 3
              (fixedInputCoframeJetCarrier point) +
            lorentzSkewConnectionOfBivectorOneForm
              (diracDualFormNativeActionCartanContorsionAt
                positiveSmoothUnifiedSource
                FixedP506FormNativeJointActionSolvedSuccessor point)
              2 2 3)
        0 canonicalLorentzianTimeDirection =
      0
  rw [fixed_fieldDirectionalDerivative_add_real_at_origin _ _
    (fixed_input_leviCivita_component_differentiableAt 2 2 3)
    fixed_input_cartanSkew_223_differentiableAt
    canonicalLorentzianTimeDirection,
    fixed_input_leviCivita_223_temporalDerivative_zero,
    fixed_input_cartanSkew_223_temporalDerivative_zero]
  norm_num

private theorem fixed_input_cartanConnection_323_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor point
            3 2 3)
        0 canonicalLorentzianTimeDirection =
      0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 3 2 3
              (fixedInputCoframeJetCarrier point) +
            lorentzSkewConnectionOfBivectorOneForm
              (diracDualFormNativeActionCartanContorsionAt
                positiveSmoothUnifiedSource
                FixedP506FormNativeJointActionSolvedSuccessor point)
              3 2 3)
        0 canonicalLorentzianTimeDirection =
      0
  rw [fixed_fieldDirectionalDerivative_add_real_at_origin _ _
    (fixed_input_leviCivita_component_differentiableAt 3 2 3)
    fixed_input_cartanSkew_323_differentiableAt
    canonicalLorentzianTimeDirection,
    fixed_input_leviCivita_323_temporalDerivative_zero,
    fixed_input_cartanSkew_323_temporalDerivative_zero]
  norm_num

private theorem fixed_input_cartanConnection_112_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor point
            1 1 2)
        0 canonicalLorentzianTimeDirection =
      0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 1 2
              (fixedInputCoframeJetCarrier point) +
            lorentzSkewConnectionOfBivectorOneForm
              (diracDualFormNativeActionCartanContorsionAt
                positiveSmoothUnifiedSource
                FixedP506FormNativeJointActionSolvedSuccessor point)
              1 1 2)
        0 canonicalLorentzianTimeDirection =
      0
  rw [fixed_fieldDirectionalDerivative_add_real_at_origin _ _
    (fixed_input_leviCivita_component_differentiableAt 1 1 2)
    fixed_input_cartanSkew_112_differentiableAt
    canonicalLorentzianTimeDirection,
    fixed_input_leviCivita_112_temporalDerivative_zero,
    fixed_input_cartanSkew_112_temporalDerivative_zero]
  norm_num

private theorem fixed_restart_cartanConnection_131_temporalDerivative_zero :
    gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
        canonicalLorentzianTimeDirection 1 3 1 =
      0 := by
  unfold gravityConnectionDerivative
  rw [fixedP506L0CartanRestartActual, fixedP506L0RecenteredInput,
    spatiallyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact fixed_input_cartanConnection_131_temporalDerivative_zero

private theorem fixed_restart_cartanConnection_223_temporalDerivative_zero :
    gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
        canonicalLorentzianTimeDirection 2 2 3 =
      0 := by
  unfold gravityConnectionDerivative
  rw [fixedP506L0CartanRestartActual, fixedP506L0RecenteredInput,
    spatiallyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact fixed_input_cartanConnection_223_temporalDerivative_zero

/-- The exact fixed-restart `323` connection coordinate has zero temporal
first germ.  This is a source/action readout of the produced Cartan field;
no curvature target or residual coordinate is supplied. -/
theorem fixedP506L0CartanRestartActual_cartanConnection323_temporalDerivative_zero :
    gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
        canonicalLorentzianTimeDirection 3 2 3 =
      0 := by
  unfold gravityConnectionDerivative
  rw [fixedP506L0CartanRestartActual, fixedP506L0RecenteredInput,
    spatiallyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact fixed_input_cartanConnection_323_temporalDerivative_zero

/-- The exact fixed-restart `112` connection coordinate has zero temporal
first germ on the same source/action occurrence. -/
theorem fixedP506L0CartanRestartActual_cartanConnection112_temporalDerivative_zero :
    gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
        canonicalLorentzianTimeDirection 1 1 2 =
      0 := by
  unfold gravityConnectionDerivative
  rw [fixedP506L0CartanRestartActual, fixedP506L0RecenteredInput,
    spatiallyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact fixed_input_cartanConnection_112_temporalDerivative_zero

/-- Regularity of the Levi--Civita coordinate consumed by the fixed Cartan
restart, stated without exposing the private carrier abbreviation. -/
theorem
    fixedP506JointActionSolvedSuccessor_leviCivitaComponent_differentiableAt
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        identityECSpinConnectionComponentOfCarrier
          formDirection internalOut internalIn
          (FixedP506FormNativeJointActionSolvedSuccessor.coframe point,
            (holonomicCoframeFirstJetAt
              FixedP506FormNativeJointActionSolvedSuccessor.coframe point
              ).derivative)) 0 := by
  simpa only [fixedInputCoframeJetCarrier] using
    fixed_input_leviCivita_component_differentiableAt
      formDirection internalOut internalIn

/-- The `131` Levi--Civita coordinate has zero temporal first germ on the
fixed source/action-generated input. -/
theorem
    fixedP506JointActionSolvedSuccessor_leviCivita131_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 3 1
            (FixedP506FormNativeJointActionSolvedSuccessor.coframe point,
              (holonomicCoframeFirstJetAt
                FixedP506FormNativeJointActionSolvedSuccessor.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa only [fixedInputCoframeJetCarrier] using
    fixed_input_leviCivita_131_temporalDerivative_zero

/-- The `223` Levi--Civita coordinate has zero temporal first germ on the
fixed source/action-generated input. -/
theorem
    fixedP506JointActionSolvedSuccessor_leviCivita223_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 2 2 3
            (FixedP506FormNativeJointActionSolvedSuccessor.coframe point,
              (holonomicCoframeFirstJetAt
                FixedP506FormNativeJointActionSolvedSuccessor.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa only [fixedInputCoframeJetCarrier] using
    fixed_input_leviCivita_223_temporalDerivative_zero

theorem fixedP506L0CartanRestartActual_temporalElectricKernel_zero :
    gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
          canonicalLorentzianTimeDirection 1 3 1 +
        gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
          canonicalLorentzianTimeDirection 2 2 3 =
      0 := by
  rw [fixed_restart_cartanConnection_131_temporalDerivative_zero,
    fixed_restart_cartanConnection_223_temporalDerivative_zero]
  norm_num

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanRestartTemporalElectricKernel
