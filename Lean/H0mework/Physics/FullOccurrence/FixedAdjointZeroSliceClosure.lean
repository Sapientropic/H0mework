import H0mework.Physics.FullOccurrence.FixedPrimalZeroSliceClosure
import H0mework.Physics.ElectricEC.FixedGlobalDevelopmentAdjointZeroSliceActionRead
import H0mework.Physics.CoframeResponse.MatterActionAcceptance

/-!
# U6 adjoint Dirac zero-slice closure

The full-occurrence operator has generated one global actual `U6`.  Its
coframe and adjoint field are the corresponding whole fields of `U5`; its
connection is the same-source Cartan restart.  Thus the complete local data
read by the live adjoint action agree with the already generated Cartan
current on every zero-slice occurrence.

The final theorem reads the adjoint Euler coefficient directly on `U6` using
the point-local live-coframe acceptance seam.  No U5 residual receipt,
support branch, target derivative, or successor is consumed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAdjointZeroSliceClosure

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicRegularity
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalPrimalZeroSliceClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECGlobalDevelopmentAdjointZeroSliceActionRead
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECTemporalAdjointAmbientFirstJetRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionAcceptance
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit

open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev CartanCurrent : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source U5

private theorem u6_coframe_eq_cartan :
    U6.coframe = CartanCurrent.coframe := by
  calc
    U6.coframe = U5.coframe :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
        Source U5
    _ = CartanCurrent.coframe :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        Source U5).symm

private theorem u6_gravityConnection_eq_cartan :
    U6.gravityConnection = CartanCurrent.gravityConnection :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
    Source U5

private theorem u6_gaugeConnection_eq_cartan :
    U6.gaugeConnection = CartanCurrent.gaugeConnection := by
  calc
    U6.gaugeConnection = U5.gaugeConnection :=
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current
    _ = CartanCurrent.gaugeConnection :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
        Source U5).symm

private theorem u6_scalar_eq_cartan :
    U6.scalar = CartanCurrent.scalar := by
  calc
    U6.scalar = U5.scalar :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
        Source U5
    _ = CartanCurrent.scalar :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar
        Source U5).symm

private theorem u6_conjugateMatter_eq_cartan :
    U6.conjugateMatter = CartanCurrent.conjugateMatter := by
  calc
    U6.conjugateMatter = U5.conjugateMatter :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
        Source U5
    _ = CartanCurrent.conjugateMatter :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter
        Source U5).symm

private theorem u6_conjugateMatterDerivative_eq_cartan
    (point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual U6 point direction =
      holonomicConjugateMatterDerivativeDual CartanCurrent point direction := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [u6_conjugateMatter_eq_cartan]

private theorem u6_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt U6.coframe
        (canonicalCauchySlicePoint 0 space) =
      identityCoframeMatterGeometry := by
  rw [u6_coframe_eq_cartan]
  exact
    fixedP506L0CompleteJointLiveElectricECCartanRestart_coframeFirstJet_zeroSlice
      space

private theorem u6_actionVelocity_eq_cartan_zeroSlice
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity U6 point =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        CartanCurrent point := by
  dsimp only
  apply
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_of_pointData
  · rw [u6_coframe_eq_cartan]
  · exact congrFun u6_gravityConnection_eq_cartan _
  · exact congrFun u6_gaugeConnection_eq_cartan _
  · exact congrFun u6_scalar_eq_cartan _
  · exact congrFun u6_conjugateMatter_eq_cartan _
  · exact fun direction => u6_conjugateMatterDerivative_eq_cartan _ direction

private theorem u6_conjugateMatterCoordinates_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ (holonomicConjugateMatterCoordinates U6)
      (canonicalCauchySlicePoint 0 space) := by
  have fieldEquality : U6.conjugateMatter = U5.conjugateMatter :=
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
      Source U5
  have coordinateEquality :
      holonomicConjugateMatterCoordinates U6 =
        holonomicConjugateMatterCoordinates U5 := by
    unfold holonomicConjugateMatterCoordinates
    rw [fieldEquality]
  rw [coordinateEquality]
  exact
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatterCoordinates_differentiableAt_zeroSlice
      space

private theorem u6_coframe_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ U6.coframe
      (canonicalCauchySlicePoint 0 space) := by
  have fieldEquality : U6.coframe = Input.coframe := by
    calc
      U6.coframe = U5.coframe :=
        sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
          Source U5
      _ = fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.coframe :=
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC
      _ = fixedP506L0CompleteJointGlobalDevelopmentActual.coframe :=
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing
      _ = Input.coframe :=
        fixedP506L0CompleteJointGlobalDevelopmentActual_coframe
  rw [fieldEquality]
  exact
    ((holonomicCoframe_contDiff Input
      fixedP506FormNativeJointActionSolvedSuccessor_smooth).differentiable
        (by simp)).differentiableAt

/-- The final full-occurrence actual itself satisfies the generated live
adjoint action law at every fixed zero-slice occurrence. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_adjointActionLaw_zeroSlice
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw U6 point
      (holonomicConjugateMatterDerivativeDual U6 point
        canonicalLorentzianTimeDirection) := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  have cartanLaw :=
    fixedP506L0CompleteJointLiveElectricECCartanRestart_adjointActionLaw_zeroSlice
      space
  have cartanCoframeOne : CartanCurrent.coframe point = 1 :=
    coframe_eq_one_of_identity_firstJet CartanCurrent point
      (fixedP506L0CompleteJointLiveElectricECCartanRestart_coframeFirstJet_zeroSlice
        space)
  have cartanNondegenerate :
      Matrix.det (CartanCurrent.coframe point) ≠ 0 := by
    rw [cartanCoframeOne]
    simp
  have cartanNoncharacteristic :
      coframeTemporalPrincipalScalar (CartanCurrent.coframe point) ≠ 0 := by
    rw [cartanCoframeOne, coframeTemporalPrincipalScalar_one]
    exact one_ne_zero
  have cartanDerivativeEqVelocity :
      holonomicConjugateMatterDerivativeDual CartanCurrent point
          canonicalLorentzianTimeDirection =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          CartanCurrent point :=
    (holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_iff
      CartanCurrent point cartanNondegenerate cartanNoncharacteristic _).1
      cartanLaw
  have u6DerivativeEqVelocity :
      holonomicConjugateMatterDerivativeDual U6 point
          canonicalLorentzianTimeDirection =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity U6 point :=
    (u6_conjugateMatterDerivative_eq_cartan point
        canonicalLorentzianTimeDirection).trans
      (cartanDerivativeEqVelocity.trans
        (u6_actionVelocity_eq_cartan_zeroSlice space).symm)
  have u6CoframeOne : U6.coframe point = 1 :=
    coframe_eq_one_of_identity_firstJet U6 point
      (u6_coframeFirstJet_zeroSlice space)
  have u6Nondegenerate : Matrix.det (U6.coframe point) ≠ 0 := by
    rw [u6CoframeOne]
    simp
  have u6Noncharacteristic :
      coframeTemporalPrincipalScalar (U6.coframe point) ≠ 0 := by
    rw [u6CoframeOne, coframeTemporalPrincipalScalar_one]
    exact one_ne_zero
  exact
    (holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_iff U6 point
      u6Nondegenerate u6Noncharacteristic _).2 u6DerivativeEqVelocity

/-- The generated U6 live adjoint law reads out as the exact adjoint Euler
zero at every occurrence of the fixed P506/L0 zero slice. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterEuler_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient Source U6 direction
        (canonicalCauchySlicePoint 0 space) =
      0 := by
  exact
    holonomicDiracDualMatterEulerLagrange_eq_zero_of_liveActionLaw_identity_firstJet
      Source U6 (canonicalCauchySlicePoint 0 space)
      (u6_coframe_differentiableAt_zeroSlice space)
      (u6_conjugateMatterCoordinates_differentiableAt_zeroSlice space)
      (u6_coframeFirstJet_zeroSlice space)
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_adjointActionLaw_zeroSlice
        space)
      direction

/-- The `.matter` coordinate of the same U6 joint residual is zero on the
complete fixed P506/L0 zero slice. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterResidual_zeroSlice
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source U6
      (canonicalCauchySlicePoint 0 space)).matter =
      0 := by
  funext direction
  exact
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterEuler_zeroSlice
      space direction

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAdjointZeroSliceClosure
