import H0mework.Physics.ElectricJoint.ElectricECResidualTelescoping
import H0mework.Physics.JointVariation.GlobalDevelopmentFixed
import H0mework.Physics.ElectricEC.FixedOriginZeroFiber
import H0mework.Physics.ElectricEC.FixedOriginPhysicalRetention
import H0mework.Physics.RecenteredJoint.FixedFullJointConnectionOriginRegularity

/-!
# Fixed live-electric EC Lorentz critical pair

The fixed complete-joint occurrence already contains the ordered global
write

```text
U3 --current-native Cartan/reaction--> U4
   --Einstein--Cartan full-Cauchy--> U5.
```

The Cartan leg is the native producer for the Lorentz equation.  On the
canonical nondegenerate time domain, its output `U4` has zero Lorentz Euler
three-form.  The generic five-leg telescoping interface therefore identifies
the final `U5` Lorentz read exactly with the single downstream `U4 -> U5`
changed read.

This module constructs no new actual and does not turn that delta into a
correction.  The delta is the faithful critical-pair responsibility of the
already generated Einstein--Cartan tail.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECLorentzCriticalPair

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanConnectionLocalActualLiftRegression
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanReactionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECResidualTelescoping
open StageNineDiracDualFormNativeCompleteJointLiveElectricECSpacetimeOccurrence
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeIdentityECConstraintObservationReplacement
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginZeroFiber
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanCauchyEvolutionRegularity
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointConnectionOriginRegularity
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanRestart
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineJointActionLocalActualLift
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineResidualLimitCoframeBalanceDecision
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineTopologicalFourFormPairing

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev CartanInput : StageNineHolonomicConfiguration :=
  completeJointLiveElectricGlobalP286Current positiveSmoothUnifiedSource
    FixedInput

private abbrev CartanActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual

private abbrev FinalActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev FinalCurvatureTarget : PhysicalBivector :=
  StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginPhysicalRetention.fixedP506L0CompleteJointLiveElectricECGravityCurvatureTarget

private abbrev FixedOccurrence (point : BasePoint) :=
  fixedP506L0CompleteJointLiveElectricECSpacetimeOccurrence point

private theorem fixedOccurrence_after_cartan
    (point : BasePoint) :
    (FixedOccurrence point).after .cartan = CartanActual :=
  rfl

/-- The Lorentz coordinate of the authoritative joint residual at one fixed
spacetime occurrence. -/
def fixedP506L0CompleteJointLiveElectricECLorentzRead
    (point : BasePoint)
    (actual : StageNineHolonomicConfiguration) :
    PhysicalBivectorThreeForm :=
  (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
    actual point).lorentzConnection

/-- Exact downstream changed read generated by the existing Einstein--Cartan
tail.  It is an observation of `U4 -> U5`, not a write input. -/
def fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta
    (point : BasePoint) :
    PhysicalBivectorThreeForm :=
  completeJointLiveElectricECReadDelta
    (fixedP506L0CompleteJointLiveElectricECLorentzRead point)
    CartanActual FinalActual

/-- The generic telescoping law specialized to the native Cartan reader.
This theorem still displays the native `U4` value explicitly; no zero or
regularity fact is hidden in the algebraic transporter. -/
theorem
    fixedP506L0CompleteJointLiveElectricEC_finalLorentzRead_eq_cartanNative_add_einsteinCartanDelta
    (point : BasePoint) :
    fixedP506L0CompleteJointLiveElectricECLorentzRead point FinalActual =
      fixedP506L0CompleteJointLiveElectricECLorentzRead point CartanActual +
        fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta
          point := by
  simpa only [
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta,
    fixedOccurrence_after_cartan,
    fixedP506L0CompleteJointLiveElectricECSpacetimeOccurrence_finalActual,
    CartanActual, FinalActual] using
    (CompleteJointLiveElectricECSpacetimeOccurrence.read_final_eq_cartan_native_add_einsteinCartanDelta
        (FixedOccurrence point)
        (fixedP506L0CompleteJointLiveElectricECLorentzRead point))

/-- The `U4` value in the telescoping law is a genuine Cartan-native
settlement on the canonical generated nondegenerate domain. -/
theorem
    fixedP506L0CompleteJointLiveElectricEC_cartanNativeLorentzRead_zero
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    fixedP506L0CompleteJointLiveElectricECLorentzRead
        (canonicalCauchySlicePoint time space) CartanActual =
      0 := by
  change
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          positiveSmoothUnifiedSource CartanInput)
        (canonicalCauchySlicePoint time space) =
      0
  have coframeSmooth : ContDiff ℝ ∞ CartanInput.coframe := by
    rw [←
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        positiveSmoothUnifiedSource CartanInput]
    change ContDiff ℝ ∞ CartanActual.coframe
    rw [
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
    apply contDiff_pi'
    intro internal
    apply contDiff_pi'
    intro coordinate
    exact
      fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_contDiff
        internal coordinate
  have nondegenerate :
      Matrix.det
          (CartanInput.coframe
            (canonicalCauchySlicePoint time space)) ≠
        0 := by
    rw [←
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        positiveSmoothUnifiedSource CartanInput]
    change
      Matrix.det
          (CartanActual.coframe
            (canonicalCauchySlicePoint time space)) ≠
        0
    rw [
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
    exact
      fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate
        space inDomain
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at_of_coframeContDiff
      positiveSmoothUnifiedSource CartanInput coframeSmooth
      (canonicalCauchySlicePoint time space) nondegenerate

/-- On the same generated domain, the final Lorentz residual is exactly the
single Einstein--Cartan changed read.  Thus the remaining responsibility is
localized to the existing `U4 -> U5` critical pair without constructing a
sector-local successor. -/
theorem
    fixedP506L0CompleteJointLiveElectricEC_finalLorentzRead_eq_einsteinCartanDelta
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    fixedP506L0CompleteJointLiveElectricECLorentzRead
        (canonicalCauchySlicePoint time space) FinalActual =
      fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta
        (canonicalCauchySlicePoint time space) := by
  rw [
    fixedP506L0CompleteJointLiveElectricEC_finalLorentzRead_eq_cartanNative_add_einsteinCartanDelta,
    fixedP506L0CompleteJointLiveElectricEC_cartanNativeLorentzRead_zero
      time space inDomain,
    zero_add]

private theorem finalGravityAuxiliary_eq_cartan :
    FinalActual.gravityAuxiliary = CartanActual.gravityAuxiliary := by
  funext point
  rfl

private theorem finalMatterSpin_eq_cartan
    (point : BasePoint) :
    formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 point
        (toContinuumPointField FinalActual point) =
      formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 point
        (toContinuumPointField CartanActual point) := by
  have physicalSpinEquality :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource FinalActual CartanActual point
      (congrFun
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC
        point)
      (congrFun
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC
        point)
      (congrFun
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC
        point)
  unfold diracDualFormNativeActionSpinResponseAt
    formNativePhysicalSpinCurrentThreeForm at physicalSpinEquality
  exact neg_injective physicalSpinEquality

private theorem finalGravityAuxiliaryExteriorDerivative_eq_cartan
    (point : BasePoint) :
    holonomicGravityAuxiliaryExteriorDerivative FinalActual point =
      holonomicGravityAuxiliaryExteriorDerivative CartanActual point := by
  unfold holonomicGravityAuxiliaryExteriorDerivative
    holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
  rw [finalGravityAuxiliary_eq_cartan]

private theorem cartanInput_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    CartanInput.matter (canonicalCauchySlicePoint 0 space) =
      FixedInput.matter (canonicalCauchySlicePoint 0 space) := by
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      positiveSmoothUnifiedSource FixedInput).matter
        (canonicalCauchySlicePoint 0 space) =
      FixedInput.matter (canonicalCauchySlicePoint 0 space)
  exact
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      positiveSmoothUnifiedSource FixedInput space

private theorem cartanInput_conjugateMatter_zeroSlice
    (space : StageNineSpatialPoint) :
    CartanInput.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      FixedInput.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      positiveSmoothUnifiedSource FixedInput).conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      FixedInput.conjugateMatter (canonicalCauchySlicePoint 0 space)
  exact
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      positiveSmoothUnifiedSource FixedInput space

private theorem cartanActual_connection_zeroSlice_eq_restartOrigin
    (space : StageNineSpatialPoint) :
    CartanActual.gravityConnection (canonicalCauchySlicePoint 0 space) =
      (fixedP506L0CartanRestartActual space).gravityConnection 0 := by
  rw [
    fixedP506L0CartanRestartActual_connection_origin_eq_zeroSliceAction]
  change
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        CartanInput (canonicalCauchySlicePoint 0 space) =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        FixedInput (canonicalCauchySlicePoint 0 space)
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource CartanInput FixedInput
      (canonicalCauchySlicePoint 0 space) rfl
      (cartanInput_matter_zeroSlice space)
      (cartanInput_conjugateMatter_zeroSlice space)
  rw [spinEq]
  rfl

private theorem cartanActual_connection_zeroSlice_eq_origin
    (space : StageNineSpatialPoint) :
    CartanActual.gravityConnection (canonicalCauchySlicePoint 0 space) =
      CartanActual.gravityConnection 0 := by
  rw [cartanActual_connection_zeroSlice_eq_restartOrigin]
  rw [fixedP506L0CartanRestartActual_gravityConnection_origin_eq_zero]
  rw [← cartanActual_connection_zeroSlice_eq_restartOrigin 0]
  congr 1
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- The only arbitrary-point Lorentz effect of the EC tail is the change in
the primitive Lorentz connection acting on the same generated `II+`
auxiliary.  The auxiliary derivative and matter-spin terms cancel exactly.
This is the decisive read-after-write seam; it remains an observation. -/
theorem
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta_eq_connectionAction_sub
    (point : BasePoint) :
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta point =
      pointwisePhysicalBivectorConnectionExteriorAction
          (FinalActual.gravityConnection point)
          (CartanActual.gravityAuxiliary point) -
        pointwisePhysicalBivectorConnectionExteriorAction
          (CartanActual.gravityConnection point)
          (CartanActual.gravityAuxiliary point) := by
  change
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
          FinalActual point -
        holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
          CartanActual point =
      _
  unfold holonomicFormNativeLorentzEulerThreeForm
  rw [
    holonomicGravityAuxiliaryExteriorCovariantDerivative_eq_parts,
    holonomicGravityAuxiliaryExteriorCovariantDerivative_eq_parts,
    finalGravityAuxiliaryExteriorDerivative_eq_cartan point,
    finalMatterSpin_eq_cartan point,
    congrFun finalGravityAuxiliary_eq_cartan point]
  abel

/-- Zero-fiber criterion for the downstream EC critical pair.  No connection
equality is assumed: the action of the actual written connection difference
on the live auxiliary is the complete Lorentz responsibility. -/
theorem
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta_eq_zero_iff
    (point : BasePoint) :
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta point = 0 ↔
      pointwisePhysicalBivectorConnectionExteriorAction
          (FinalActual.gravityConnection point)
          (CartanActual.gravityAuxiliary point) =
        pointwisePhysicalBivectorConnectionExteriorAction
          (CartanActual.gravityConnection point)
          (CartanActual.gravityAuxiliary point) := by
  rw [
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta_eq_connectionAction_sub,
    sub_eq_zero]

private theorem cartanActual_auxiliary_zeroSlice_eq_identityIIPlus
    (space : StageNineSpatialPoint) :
    CartanActual.gravityAuxiliary (canonicalCauchySlicePoint 0 space) =
      physicalIIPlusBivector 1 := by
  change
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      positiveSmoothUnifiedSource CartanInput).gravityAuxiliary
        (canonicalCauchySlicePoint 0 space) =
      physicalIIPlusBivector 1
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliary]
  change
    physicalIIPlusBivector
        (CartanActual.coframe (canonicalCauchySlicePoint 0 space)) =
      physicalIIPlusBivector 1
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing,
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_zeroSlice]

/-- A fixed zero-slice spatial coordinate probe for the downstream EC
Lorentz critical pair.  This is a readout test only; the right-hand side is
not consumed by any writer. -/
theorem
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta_spatialOne_internalZero_tripleZero :
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta
        (canonicalCauchySlicePoint 0
          (canonicalSpatialCoordinateDirection 0)) 0 0 =
      (1 / 2 : ℝ) *
        (FinalCurvatureTarget 4 0 -
          originLorentzBracketCurvature
            (CartanActual.gravityConnection 0) 4 0) := by
  rw [
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta_eq_connectionAction_sub]
  rw [
    cartanActual_auxiliary_zeroSlice_eq_identityIIPlus,
    cartanActual_connection_zeroSlice_eq_origin]
  rw [show
    FinalActual.gravityConnection
        (canonicalCauchySlicePoint 0
          (canonicalSpatialCoordinateDirection 0)) =
      normalizedAffineLorentzConnectionField
        (FinalActual.gravityConnection 0)
        FinalCurvatureTarget
        (canonicalCauchySlicePoint 0
          (canonicalSpatialCoordinateDirection 0)) by
      exact congrFun
        StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginPhysicalRetention.fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityConnection_normalForm
        _]
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityConnection_origin_eq_preEC]
  simp [
    pointwisePhysicalBivectorConnectionExteriorAction,
    pointwisePhysicalBivectorExteriorCovariantDerivative,
    pointwisePhysicalBivectorCovariantDerivative,
    ordinaryLorentzBivectorConnectionAction,
    orderedInternalBivectorComponent,
    orderedSpacetimeBivectorComponent,
    normalizedAffineLorentzConnectionField,
    normalizedAffineBivectorOneForm,
    normalizedAffineBivectorComponentLinear,
    normalizedDerivativeBivector,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    physicalIIPlusBivector_one_eq_identityCoordinates,
    identityPhysicalIIPlusBivector,
    canonicalCauchySlicePoint,
    canonicalSpatialCoordinateDirection,
    canonicalLorentzianTimeDirection,
    pairFirst, pairSecond, threeFormFirst, threeFormSecond, threeFormThird,
    minkowskiInternalSign, baseCoordinate,
    Fin.sum_univ_four, Fin.sum_univ_six, Fin.sum_univ_three]

private theorem positiveSourceTargetMatterActual_coframe_one_here
    (point : BasePoint) :
    positiveSourceTargetMatterActual.coframe point = 1 := by
  rw [positiveSourceTargetMatterActual,
    sourceActionGeneratedJointLocalActualLift_coframe_at]
  change positivePhaseProbeCauchyState.coframe 0 = 1
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

private theorem fixedCartanReactionContact_zero_actionConnection_eq_fixedAction :
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fixedCartanReactionContact 0) 0 =
      fixedActionCartanConnection := by
  have coframeFieldEq :
      (fixedCartanReactionContact 0).coframe =
        positiveSourceTargetMatterActual.coframe := by
    funext point
    rw [fixedCartanReactionContact_coframe_one]
    exact (positiveSourceTargetMatterActual_coframe_one_here point).symm
  have coframeEq :
      (fixedCartanReactionContact 0).coframe 0 =
        positiveSourceTargetMatterActual.coframe 0 :=
    congrFun coframeFieldEq 0
  have matterEq :
      (fixedCartanReactionContact 0).matter 0 =
        positiveSourceTargetMatterActual.matter 0 := by
    calc
      _ = diracSpinTwoMatterProbe :=
        fixedCartanReactionContact_matter_origin 0
      _ = positiveSourceTargetMatterCauchyState.matter 0 :=
        positiveSourceTargetMatterCauchyState_matter.symm
      _ = _ :=
        (sourceActionGeneratedJointLocalActualLift_initialMatter
          positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
          0).symm
  have conjugateEq :
      (fixedCartanReactionContact 0).conjugateMatter 0 =
        positiveSourceTargetMatterActual.conjugateMatter 0 := by
    calc
      _ = diracSpinZeroMatterCoordinate :=
        fixedCartanReactionContact_conjugateMatter_origin 0
      _ = positiveSourceTargetMatterCauchyState.conjugateMatter 0 :=
        positiveSourceTargetMatterCauchyState_conjugate.symm
      _ = _ :=
        (sourceActionGeneratedJointLocalActualLift_initialConjugateMatter
          positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
          0).symm
  have response :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource
      (fixedCartanReactionContact 0) positiveSourceTargetMatterActual 0
      coframeEq matterEq conjugateEq
  unfold fixedActionCartanConnection
    diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [coframeFieldEq, response]

private theorem fixedCartanReactionContact_zero_connection_eq_fixedAction :
    (fixedCartanReactionContact 0).gravityConnection 0 =
      fixedActionCartanConnection := by
  calc
    _ =
        diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource (fixedCartanReactionContact 0) 0 :=
      sourceActionGeneratedDiracDualCartanReactionLocalActualLift_connection_selfGenerated
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState 0 0
    _ = _ :=
      fixedCartanReactionContact_zero_actionConnection_eq_fixedAction

private theorem cartanActual_connection_origin_eq_fixedAction :
    CartanActual.gravityConnection 0 = fixedActionCartanConnection := by
  calc
    CartanActual.gravityConnection 0 =
        CartanActual.gravityConnection
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
      congr 1
      apply PiLp.ext
      intro direction
      fin_cases direction <;>
        simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
          Fin.sum_univ_three]
    _ = (fixedP506L0CartanRestartActual 0).gravityConnection 0 :=
      cartanActual_connection_zeroSlice_eq_restartOrigin 0
    _ = sourceActionGeneratedDiracDualCartanConnectionField
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState 0 0 :=
      fixedP506L0CartanRestartActual_gravityConnection_origin_eq_fixedJointCartan
        0
    _ = (fixedCartanReactionContact 0).gravityConnection 0 := by
      rfl
    _ = fixedActionCartanConnection :=
      fixedCartanReactionContact_zero_connection_eq_fixedAction

/-- The fixed P506/L0 Cartan origin contributes a concrete nonzero
connection bracket to the downstream Lorentz changed read. -/
theorem
    fixedP506L0CompleteJointLiveElectricCartanOriginLorentzBracket_four_zero :
    originLorentzBracketCurvature
        (CartanActual.gravityConnection 0) 4 0 =
      (1 / 16 : ℝ) := by
  rw [cartanActual_connection_origin_eq_fixedAction,
    fixedActionCartanConnection_eq_positiveNormalForm]
  norm_num [
    originLorentzBracketCurvature,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    pairFirst, pairSecond, minkowskiInternalSign,
    Fin.sum_univ_four, Fin.sum_univ_six]
  simp +decide
  field_simp
  norm_num

/-- The same actual coordinate is reduced to the one still-unsettled EC
curvature target coefficient.  In particular, the already generated Cartan
bracket is no longer part of the open arithmetic. -/
theorem
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta_spatialOne_internalZero_tripleZero_eq_target_sub_one_sixteenth :
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta
        (canonicalCauchySlicePoint 0
          (canonicalSpatialCoordinateDirection 0)) 0 0 =
      (1 / 2 : ℝ) * (FinalCurvatureTarget 4 0 - (1 / 16 : ℝ)) := by
  rw [
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta_spatialOne_internalZero_tripleZero,
    fixedP506L0CompleteJointLiveElectricCartanOriginLorentzBracket_four_zero]

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- Positive fixed-point regression: the EC tail produces no Lorentz
changed read at the distinguished accepted occurrence. -/
theorem
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta_origin_zero :
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta 0 = 0 := by
  rw [← canonicalCauchySlicePoint_zero_zero]
  rw [←
    fixedP506L0CompleteJointLiveElectricEC_finalLorentzRead_eq_einsteinCartanDelta
      0 0
      (fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain 0)]
  rw [canonicalCauchySlicePoint_zero_zero]
  have jointZero :=
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentOriginResidual_zero
  simpa [
    fixedP506L0CompleteJointLiveElectricECLorentzRead,
    FinalActual, FinalECOriginResidual, FinalEC] using
    congrArg
      DiracDualFormNativePointwiseJointResidualCarrier.lorentzConnection
      jointZero

/-! ## Einstein--Cartan-native coframe read -/

/-- The exact repaired-root coframe assembly evaluated on the final `U5`
actual.  It is a readout of the three action-native terms, not a target
covector accepted by a writer. -/
def fixedP506L0CompleteJointLiveElectricECCoframeNativeAssembly
    (point : BasePoint)
    (variation : LorentzianCoframe) : ℝ :=
  let field := toContinuumPointField FinalActual point
  diracDualFormNativeCoframeGaugeEulerCovector
        positiveSmoothUnifiedSource field variation +
    diracDualFormNativeCoframeMatterEulerCovector
        positiveSmoothUnifiedSource point field variation -
      formNativeCoframeConstraintReaction field variation

/-- Arbitrary-point exact coframe seam of the final actual.  Nondegeneracy
is the only analytic mouth needed by the already authoritative coframe
variation theorem; no zero-fiber claim is inserted. -/
theorem
    fixedP506L0CompleteJointLiveElectricEC_finalCoframeRead_apply_eq_nativeAssembly
    (point : BasePoint)
    (nondegenerate : Matrix.det (FinalActual.coframe point) ≠ 0)
    (variation : LorentzianCoframe) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalActual point).coframe variation =
      fixedP506L0CompleteJointLiveElectricECCoframeNativeAssembly
        point variation := by
  exact
    diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
      positiveSmoothUnifiedSource point
      (toContinuumPointField FinalActual point)
      nondegenerate variation

/-- Fixed-lineage specialization of the exact coframe assembly on the same
canonical nondegenerate domain used by the Cartan settlement. -/
theorem
    fixedP506L0CompleteJointLiveElectricEC_finalCoframeRead_apply_eq_nativeAssembly_onDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space)
    (variation : LorentzianCoframe) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalActual (canonicalCauchySlicePoint time space)).coframe variation =
      fixedP506L0CompleteJointLiveElectricECCoframeNativeAssembly
        (canonicalCauchySlicePoint time space) variation := by
  apply
    fixedP506L0CompleteJointLiveElectricEC_finalCoframeRead_apply_eq_nativeAssembly
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate
      space inDomain

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECLorentzCriticalPair
