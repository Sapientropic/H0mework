import H0mework.Physics.GravityTail.FixedAllPointResidualNormalForm
import H0mework.Physics.ConstrainedCauchy.FixedDirectPrefixQuadraticCoframeBoundary
import H0mework.Physics.GravityTail.FixedOriginResidualClosure
import H0mework.Physics.Jets.IIPlusJetKinematics

/-!
# Constraint/Cauchy gravity-tail primitive seam closure

The emitted whole action jet and its occurrence-local native contact already
share one source/current action.  This file proves that their coframe,
connection, curvature, auxiliary, multiplier, matter-covariant-derivative and
auxiliary-exterior coordinates close from the generated value, curvature and
coframe-first-jet factors.  The same coframe value and complete first jet,
together with affine recenter naturality and the source-preserved scalar and
matter fields, also close both differential-momentum-divergence coordinates.

The calculus lemmas below are implementation details.  The sole public mouth
consumes the four generated factor families and returns the whole seam
equality.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailAllPointResidualNormalForm

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyDirectPrefixQuadraticCoframeBoundary
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianUpdate
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionAcceptance
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailJointPath
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailOriginResidualClosure
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyOriginJointResidual
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineGlobalConnection
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarPointwiseEquation
open StageNineScalarMomentumCoframeReadout
open StageNineMatterPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionCauchySplit
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineRadialCurveIntegralFirstJet

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGlobalActual

private abbrev Base : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Current

private abbrev ConstraintCartanBase : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalBase

private abbrev ConstraintRows : IdentityECEtaCompatibleRows :=
  sourceActionGeneratedIdentityECCoframeAccelerationRows
    Source ConstraintCartanBase

private abbrev ConstraintHessian : CoframeHolonomicSecondJet :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    Source ConstraintCartanBase

private abbrev ConstraintPrepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintPreparedActual

private abbrev ConstraintRestart : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintRestartActual

private abbrev Output : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual

private abbrev Contact (point : BasePoint) : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailProfileContact Source Current point

private abbrev RecenteredOutput (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration Output point

/-! ## Fixed transverse coframe obstruction -/

private def gravityTailSelectedTransverseDefectSum : ℝ :=
  cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
      Source Current
      (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 1))
      3 2 3 +
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
      Source Current
      (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 2))
      1 3 1 +
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
      Source Current
      (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 0))
      2 1 2

private theorem gravityTailSelectedTransverseDefectSum_eq_normalizedDiagonal :
    gravityTailSelectedTransverseDefectSum =
      normalizedDerivativeBivector
          (Current.gravityConnection 0)
          (diracDualFormNativeCoframeECContactCurvatureTarget Source Current 0)
          3 3 +
        normalizedDerivativeBivector
          (Current.gravityConnection 0)
          (diracDualFormNativeCoframeECContactCurvatureTarget Source Current 0)
          4 4 +
        normalizedDerivativeBivector
          (Current.gravityConnection 0)
          (diracDualFormNativeCoframeECContactCurvatureTarget Source Current 0)
          5 5 := by
  unfold gravityTailSelectedTransverseDefectSum
  change
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
          Source Current
          (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 1))
          (Fin.succ (2 : Fin 3)) 2 3 +
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
          Source Current
          (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 2))
          (Fin.succ (0 : Fin 3)) 3 1 +
      cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
        Source Current
        (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 0))
        (Fin.succ (1 : Fin 3)) 1 2 = _
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialFirstJetDerivativeDefect_zeroSlice_eq_baseConnectionDisplacement,
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialFirstJetDerivativeDefect_zeroSlice_eq_baseConnectionDisplacement,
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialFirstJetDerivativeDefect_zeroSlice_eq_baseConnectionDisplacement,
    fixedP506L0CartanECConstraintCauchyGravityTailBase_gravityConnection_eq_normalizedAffine]
  simp [normalizedAffineLorentzConnectionField,
    normalizedAffineBivectorOneForm,
    normalizedAffineBivectorComponentLinear,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    canonicalCauchySlicePoint, canonicalSpatialCoordinateDirection,
    baseCoordinate, pairFirst, pairSecond,
    minkowskiInternalSign, Fin.sum_univ_three, Fin.sum_univ_four,
    Fin.sum_univ_six]

private theorem
    gravityTailSelectedTransverseDefectSum_eq_constraintDifference :
    gravityTailSelectedTransverseDefectSum =
      -(2 : ℝ)⁻¹ *
        (identityDiracDualECConstraintObservation
            (diracDualFormNativeCoframeECContactCurvatureTarget
              Source Current 0) 0 -
          identityDiracDualECConstraintObservation
            (originLorentzBracketCurvature (Current.gravityConnection 0)) 0) := by
  rw [gravityTailSelectedTransverseDefectSum_eq_normalizedDiagonal]
  rw [identityDiracDualECConstraintObservation_explicit,
    identityDiracDualECConstraintObservation_explicit]
  simp [normalizedDerivativeBivector]
  ring

private theorem constraintHessian_constraintObservation_temporalDiagonal00 :
    identityDiracDualECConstraintObservation
        (identityECLeviCivitaCurvatureOfCoframeHessian ConstraintHessian) 0 =
      (319 / 108 : ℝ) := by
  have observed :=
    identityDiracDualECCurvatureObservation_typedHessianSection ConstraintRows
  have coordinate := congrFun (congrFun observed (0 : LorentzianIndex))
    (0 : LorentzianIndex)
  change
    identityDiracDualECConstraintObservation
        (identityECLeviCivitaCurvatureOfCoframeHessian ConstraintHessian) 0 =
      ConstraintRows.1 0 0 at coordinate
  have rows :=
    fixedP506L0CartanECCauchyTemporalBase_accelerationRows_e1_exact
  change ConstraintRows.1 0 0 = (319 / 108 : ℝ) ∧ _ at rows
  rw [rows.1] at coordinate
  exact coordinate

private theorem constraintCartanBase_connection_origin_eq_current :
    ConstraintCartanBase.gravityConnection 0 = Current.gravityConnection 0 := by
  have pointZero :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  have baseOrigin :=
    base_connection_zeroSlice_eq_fixedAction (0 : StageNineSpatialPoint)
  rw [pointZero] at baseOrigin
  rw [baseOrigin,
    fixedP506L0CartanECConstraintCauchyGlobalActual_gravityConnection_origin_eq_fixedAction]

private theorem constraintCartanBase_connectionDerivative_origin_zero
    (direction formDirection internalOut internalIn : LorentzianIndex) :
    gravityConnectionDerivative ConstraintCartanBase 0 direction
        formDirection internalOut internalIn = 0 := by
  fin_cases direction
  · exact base_connection_temporalDerivative_origin_zero
      formDirection internalOut internalIn
  · simpa using base_connection_spatialDerivative_origin_zero
      (0 : Fin 3) formDirection internalOut internalIn
  · simpa using base_connection_spatialDerivative_origin_zero
      (1 : Fin 3) formDirection internalOut internalIn
  · simpa using base_connection_spatialDerivative_origin_zero
      (2 : Fin 3) formDirection internalOut internalIn

private theorem constraintCartanBase_curvature_origin_eq_currentOriginBracket :
    holonomicGravityCurvature ConstraintCartanBase 0 =
      originLorentzBracketCurvature (Current.gravityConnection 0) := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature originLorentzBracketCurvature
  dsimp only
  rw [
    constraintCartanBase_connectionDerivative_origin_zero,
    constraintCartanBase_connectionDerivative_origin_zero,
    constraintCartanBase_connection_origin_eq_current]
  ring

private theorem gravityTailContactTarget_constraintObservation_eq_prepared :
    identityDiracDualECConstraintObservation
        (diracDualFormNativeCoframeECContactCurvatureTarget Source Current 0) 0 =
      identityDiracDualECConstraintObservation
        (holonomicGravityCurvature ConstraintPrepared 0) 0 := by
  rw [←
    fixedP506L0CartanECConstraintCauchyGlobalActual_curvature_eq_contactTarget_origin]
  rw [fixedP506L0CartanECConstraintCauchyGlobalActual_curvature_origin]
  unfold diracDualFormNativeECCauchyCurvatureTarget
  rw [identityDiracDualECConstraintObservation_totalTarget]
  unfold diracDualFormNativeECCauchyCurrentCurvature
  have restartPrepared :
      diracDualFormNativeECNormalPreparedActual ConstraintRestart =
        ConstraintRestart :=
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      _).2
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
        Source ConstraintPrepared)
  rw [restartPrepared,
    fixedP506L0CartanECConstraintRestartActual_curvature_origin]

private theorem constraintPrepared_curvature_origin_eq_base_add_hessian :
    holonomicGravityCurvature ConstraintPrepared 0 =
      holonomicGravityCurvature ConstraintCartanBase 0 +
        identityECLeviCivitaCurvatureOfCoframeHessian ConstraintHessian := by
  exact
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_curvature_origin
      Source ConstraintCartanBase
      fixedP506L0CartanECCauchyTemporalBase_smooth

private theorem
    gravityTailContactTarget_constraintDifference_temporalDiagonal00 :
    identityDiracDualECConstraintObservation
          (diracDualFormNativeCoframeECContactCurvatureTarget Source Current 0) 0 -
        identityDiracDualECConstraintObservation
          (originLorentzBracketCurvature (Current.gravityConnection 0)) 0 =
      (319 / 108 : ℝ) := by
  rw [gravityTailContactTarget_constraintObservation_eq_prepared,
    constraintPrepared_curvature_origin_eq_base_add_hessian,
    identityDiracDualECConstraintObservation_add,
    constraintCartanBase_curvature_origin_eq_currentOriginBracket]
  simp only [Pi.add_apply]
  rw [constraintHessian_constraintObservation_temporalDiagonal00]
  ring

/-- The fixed constraint Hessian leaves an exact nonzero magnetic trace in
the current radial coframe writer: three transverse initial-slice defects
sum to `-319/216`.  No target or defect value is supplied to this readout. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTail_zeroSlice_transverseCoframeDefectSum_eq_neg_319_div_216 :
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
          Source Current
          (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 1))
          3 2 3 +
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
          Source Current
          (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 2))
          1 3 1 +
      cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
        Source Current
        (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 0))
        2 1 2 = -(319 / 216 : ℝ) := by
  change gravityTailSelectedTransverseDefectSum = -(319 / 216 : ℝ)
  rw [gravityTailSelectedTransverseDefectSum_eq_constraintDifference,
    gravityTailContactTarget_constraintDifference_temporalDiagonal00]
  norm_num

private theorem
    not_all_gravityTail_zeroSlice_transverseCoframeFirstJetDefects_vanish :
    ¬ ∀ (space : StageNineSpatialPoint) (axis : Fin 3)
        (internal coordinate : LorentzianIndex),
      cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
          Source Current (canonicalCauchySlicePoint 0 space)
          axis.succ internal coordinate = 0 := by
  intro allZero
  have first := allZero
    (canonicalSpatialCoordinateDirection 1) (2 : Fin 3) 2 3
  have second := allZero
    (canonicalSpatialCoordinateDirection 2) (0 : Fin 3) 3 1
  have third := allZero
    (canonicalSpatialCoordinateDirection 0) (1 : Fin 3) 1 2
  have first' :
      cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
          Source Current
          (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 1))
          3 2 3 = 0 := first
  have second' :
      cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
          Source Current
          (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 2))
          1 3 1 = 0 := second
  have third' :
      cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
          Source Current
          (canonicalCauchySlicePoint 0 (canonicalSpatialCoordinateDirection 0))
          2 1 2 = 0 := third
  have sumZero : gravityTailSelectedTransverseDefectSum = 0 := by
    unfold gravityTailSelectedTransverseDefectSum
    rw [first', second', third']
    ring
  have fixedSum :=
    fixedP506L0CartanECConstraintCauchyGravityTail_zeroSlice_transverseCoframeDefectSum_eq_neg_319_div_216
  change gravityTailSelectedTransverseDefectSum = -(319 / 216 : ℝ)
    at fixedSum
  rw [fixedSum] at sumZero
  norm_num at sumZero

/-- The existing fixed radial coframe writer cannot supply the all-point
coframe-first-jet factor consumed below: its initial-slice magnetic trace is
already nonzero.  This rejects only this writer, not a new source-native
compatible coframe potential generated from the same occurrence. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialFirstJetDefectCoordinates_not_allPoint_zero :
    ¬ ∀ (point : BasePoint) (internal coordinate : LorentzianIndex),
      cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0 := by
  intro allZero
  apply not_all_gravityTail_zeroSlice_transverseCoframeFirstJetDefects_vanish
  intro space axis internal coordinate
  have coordinateZero := allZero
    (canonicalCauchySlicePoint 0 space) internal coordinate
  have applied := congrArg
    (fun defect : BasePoint →L[ℝ] ℝ => defect (coordinateDirection axis.succ))
    coordinateZero
  simpa [
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect]
    using applied

/-- The obstruction is intrinsic to the sampled fixed-source one-form, not
an artifact of choosing radial integration.  No globally `C²` coframe can
have all sixteen synchronized profile one-forms as its exact derivative.
Consequently a source-native settlement must regenerate a compatible
Base/contact jet; replacing only the primitive-path compiler cannot close the
all-point first-jet seam. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailProfileCoframeJet_has_no_contDiff_two_globalPotential :
    ¬ ∃ coframe : BasePoint → LorentzianCoframe,
      (∀ internal coordinate : LorentzianIndex,
        ContDiff ℝ 2 (fun point => coframe point internal coordinate)) ∧
      ∀ point internal coordinate,
        fderiv ℝ (fun candidate => coframe candidate internal coordinate) point =
          cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
            Source Current point internal coordinate := by
  rintro ⟨coframe, smooth, derivativeEq⟩
  apply
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialFirstJetDefectCoordinates_not_allPoint_zero
  intro point internal coordinate
  apply ContinuousLinearMap.ext
  intro direction
  rw [
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate,
    radialCurveIntegralFirstJetDefect_apply_eq_integral_antisymmetry
      (fun contact =>
        cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
          Source Current contact internal coordinate)
      (fixedP506L0CartanECConstraintCauchyGravityTailCoframeJetCoordinateCLM_contDiff
        internal coordinate)]
  have oneFormEq :
      (fun contact =>
          cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
            Source Current contact internal coordinate) =
        fderiv ℝ (fun candidate => coframe candidate internal coordinate) := by
    funext contact
    exact (derivativeEq contact internal coordinate).symm
  rw [oneFormEq]
  have symmetric (candidate : BasePoint) :
      fderiv ℝ
          (fderiv ℝ (fun point => coframe point internal coordinate)) candidate
          direction point =
        fderiv ℝ
          (fderiv ℝ (fun point => coframe point internal coordinate)) candidate
          point direction :=
    (smooth internal coordinate).contDiffAt.isSymmSndFDerivAt (by norm_num)
      |>.eq direction point
  simp only [zero_apply]
  simp_rw [symmetric]
  simp

private theorem coframe_point_eq_of_valueDefect_zero
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0) :
    Output.coframe point = (Contact point).coframe 0 := by
  have seamCoordinate :=
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_coframe_eq_valueDefect
      point).trans valueDefect
  change Output.coframe point - (Contact point).coframe 0 = 0 at seamCoordinate
  exact sub_eq_zero.mp seamCoordinate

private theorem gravityConnection_point_eq_of_valueDefect_zero
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect point =
        0) :
    Output.gravityConnection point = (Contact point).gravityConnection 0 := by
  have seamCoordinate :=
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_gravityConnection_eq_valueDefect
      point).trans valueDefect
  change
    Output.gravityConnection point - (Contact point).gravityConnection 0 = 0
    at seamCoordinate
  exact sub_eq_zero.mp seamCoordinate

private theorem gravityCurvature_point_eq_of_integrabilityFactor_zero
    (point : BasePoint)
    (integrabilityFactor :
      fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
        point = 0) :
    holonomicGravityCurvature Output point =
      holonomicGravityCurvature (Contact point) 0 := by
  have seamCoordinate :=
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_gravityCurvature_eq_integrabilityFactor
      point).trans integrabilityFactor
  change
    holonomicGravityCurvature Output point -
        holonomicGravityCurvature (Contact point) 0 = 0
    at seamCoordinate
  exact sub_eq_zero.mp seamCoordinate

private theorem output_gravityAuxiliary_eq_iiPlus (point : BasePoint) :
    Output.gravityAuxiliary point =
      physicalIIPlusBivector (Output.coframe point) := by
  unfold Output
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite]
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_simplicity
      Source Current point

private theorem contact_gravityAuxiliary_eq_iiPlus (point : BasePoint) :
    (Contact point).gravityAuxiliary 0 =
      physicalIIPlusBivector ((Contact point).coframe 0) := by
  unfold Contact cartanECSynchronizedGravityTailProfileContact
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_auxiliary
      Source (fullyRecenterHolonomicConfiguration Base point) 0 0

private theorem output_matter_eq_base : Output.matter = Base.matter := by
  rfl

private theorem output_scalar_eq_base : Output.scalar = Base.scalar := by
  rfl

private theorem output_conjugateMatter_eq_base :
    Output.conjugateMatter = Base.conjugateMatter := by
  rfl

private theorem output_gaugeConnection_eq_base :
    Output.gaugeConnection = Base.gaugeConnection := by
  rfl

private theorem contact_matter_eq_recenter (point : BasePoint) :
    (Contact point).matter =
      (fullyRecenterHolonomicConfiguration Base point).matter := by
  rfl

private theorem contact_scalar_eq_recenter (point : BasePoint) :
    (Contact point).scalar =
      (fullyRecenterHolonomicConfiguration Base point).scalar := by
  rfl

private theorem contact_conjugateMatter_eq_recenter (point : BasePoint) :
    (Contact point).conjugateMatter =
      (fullyRecenterHolonomicConfiguration Base point).conjugateMatter := by
  rfl

private theorem contact_gaugeConnection_eq_recenter (point : BasePoint) :
    (Contact point).gaugeConnection =
      (fullyRecenterHolonomicConfiguration Base point).gaugeConnection := by
  rfl

private theorem recenteredOutput_scalar_eq_contact (point : BasePoint) :
    (RecenteredOutput point).scalar = (Contact point).scalar := by
  calc
    (RecenteredOutput point).scalar =
        (fullyRecenterHolonomicConfiguration Base point).scalar := by
      unfold RecenteredOutput fullyRecenterHolonomicConfiguration
      rw [output_scalar_eq_base]
    _ = (Contact point).scalar := (contact_scalar_eq_recenter point).symm

private theorem recenteredOutput_gaugeConnection_eq_contact
    (point : BasePoint) :
    (RecenteredOutput point).gaugeConnection =
      (Contact point).gaugeConnection := by
  calc
    (RecenteredOutput point).gaugeConnection =
        (fullyRecenterHolonomicConfiguration Base point).gaugeConnection := by
      unfold RecenteredOutput fullyRecenterHolonomicConfiguration
      rw [output_gaugeConnection_eq_base]
    _ = (Contact point).gaugeConnection :=
      (contact_gaugeConnection_eq_recenter point).symm

private theorem recenteredOutput_conjugateMatter_eq_contact
    (point : BasePoint) :
    (RecenteredOutput point).conjugateMatter =
      (Contact point).conjugateMatter := by
  calc
    (RecenteredOutput point).conjugateMatter =
        (fullyRecenterHolonomicConfiguration Base point).conjugateMatter := by
      unfold RecenteredOutput fullyRecenterHolonomicConfiguration
      rw [output_conjugateMatter_eq_base]
    _ = (Contact point).conjugateMatter :=
      (contact_conjugateMatter_eq_recenter point).symm

private theorem matterCovariantDerivative_point_eq
    (point : BasePoint)
    (connectionEq :
      Output.gravityConnection point =
        (Contact point).gravityConnection 0) :
    holonomicMatterCovariantDerivative Output point =
      holonomicMatterCovariantDerivative (Contact point) 0 := by
  funext direction
  let coordinateField : BasePoint → MatterCoordinateCarrier :=
    fun candidate => matterCoordinateEquiv (Base.matter candidate)
  have derivativeEq :=
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      coordinateField point 0 direction
  simp only [canonicalSpacetimeContactTranslation_zero] at derivativeEq
  change
    fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv
          (Base.matter (canonicalSpacetimeContactTranslation point candidate)))
        0 direction =
      fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv (Base.matter candidate))
        point direction
    at derivativeEq
  unfold holonomicMatterCovariantDerivative
  rw [output_matter_eq_base, output_gaugeConnection_eq_base,
    contact_matter_eq_recenter point,
    contact_gaugeConnection_eq_recenter point]
  rw [connectionEq]
  simp only [fullyRecenterHolonomicConfiguration]
  simp only [canonicalSpacetimeContactTranslation_zero]
  rw [← derivativeEq]

private theorem coframeFirstJet_point_eq
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (jetDefect :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    holonomicCoframeFirstJetAt Output.coframe point =
      holonomicCoframeFirstJetAt (Contact point).coframe 0 := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_coframeFirstJet_eq_radialFirstJet]
  unfold Contact cartanECSynchronizedGravityTailProfileContact
  rw [
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframeFirstJet_contact]
  change
    cartanECSynchronizedGravityTailCoframeRadialFirstJet
        Source Current point =
      cartanECSynchronizedGravityTailProfileCoframeFirstJet
        Source Current point
  apply coframeJet_eq_of_fields_eq
  · have valueEq :
        cartanECSynchronizedGravityTailCoframePathField Source Current point =
          Base.coframe point := by
      exact sub_eq_zero.mp valueDefect
    unfold cartanECSynchronizedGravityTailCoframeRadialFirstJet
    rw [cartanECSynchronizedGravityTailProfileCoframeFirstJet_coframe_eq_base]
    exact valueEq
  · funext derivativeDirection internal coordinate
    rw [
      cartanECSynchronizedGravityTailCoframeRadialFirstJet_derivative_eq_profile_add_defect]
    unfold cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
    rw [jetDefect internal coordinate]
    simp

private theorem recenteredOutput_coframeFirstJet_origin_eq_output
    (point : BasePoint) :
    holonomicCoframeFirstJetAt (RecenteredOutput point).coframe 0 =
      holonomicCoframeFirstJetAt Output.coframe point := by
  apply coframeJet_eq_of_fields_eq
  · exact fullyRecenterHolonomicConfiguration_coframe_origin Output point
  · funext derivativeDirection internal coordinate
    have derivativeEq :=
      fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
        (fun candidate => Output.coframe candidate internal coordinate)
        point 0 derivativeDirection
    change
      fderiv ℝ
          (fun candidate =>
            Output.coframe
              (canonicalSpacetimeContactTranslation point candidate)
              internal coordinate) 0
          (coordinateDirection derivativeDirection) = _
    rw [show
      (fun candidate =>
        Output.coframe
          (canonicalSpacetimeContactTranslation point candidate)
          internal coordinate) =
        (fun candidate => Output.coframe candidate internal coordinate) ∘
          canonicalSpacetimeContactTranslation point by rfl]
    simpa [fieldDirectionalDerivative, holonomicCoframeFirstJetAt] using
      derivativeEq

private theorem recenteredOutput_coframeFirstJet_origin_eq_contact
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (jetDefect :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    holonomicCoframeFirstJetAt (RecenteredOutput point).coframe 0 =
      holonomicCoframeFirstJetAt (Contact point).coframe 0 :=
  (recenteredOutput_coframeFirstJet_origin_eq_output point).trans
    (coframeFirstJet_point_eq point valueDefect jetDefect)

private theorem output_coframe_component_differentiableAt
    (point : BasePoint) (internal coordinate : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate => Output.coframe candidate internal coordinate) point := by
  change DifferentiableAt ℝ
    (fun candidate =>
      cartanECSynchronizedGravityTailCoframePathField
        Source Current candidate internal coordinate) point
  exact
    (cartanECSynchronizedGravityTailCoframePathField_coordinate_hasFDerivAt_of_contDiff
      Source Current internal coordinate
      (fixedP506L0CartanECConstraintCauchyGravityTailCoframeJetCoordinateCLM_contDiff
        internal coordinate)
      point).differentiableAt

private theorem contact_coframe_component_differentiableAt
    (point : BasePoint) (internal coordinate : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate => (Contact point).coframe candidate internal coordinate)
      0 := by
  have smooth :=
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contDiff
      Source (fullyRecenterHolonomicConfiguration Base point) 0
  exact
    (contDiff_pi.mp (contDiff_pi.mp smooth internal) coordinate).differentiable
        (by simp) |>.differentiableAt

private theorem coframe_differentiableAt_of_components
    (coframe : BasePoint → LorentzianCoframe)
    (point : BasePoint)
    (componentDifferentiable : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => coframe candidate internal coordinate) point) :
    DifferentiableAt ℝ coframe point := by
  apply differentiableAt_pi.mpr
  intro internal
  apply differentiableAt_pi.mpr
  intro coordinate
  exact componentDifferentiable internal coordinate

private theorem output_coframe_differentiableAt (point : BasePoint) :
    DifferentiableAt ℝ Output.coframe point :=
  coframe_differentiableAt_of_components Output.coframe point
    (output_coframe_component_differentiableAt point)

private theorem contact_coframe_differentiableAt (point : BasePoint) :
    DifferentiableAt ℝ (Contact point).coframe 0 :=
  coframe_differentiableAt_of_components (Contact point).coframe 0
    (contact_coframe_component_differentiableAt point)

private theorem recenteredOutput_coframe_differentiableAt
    (point : BasePoint) :
    DifferentiableAt ℝ (RecenteredOutput point).coframe 0 := by
  change DifferentiableAt ℝ
    (Output.coframe ∘ canonicalSpacetimeContactTranslation point) 0
  have translationDifferentiable : DifferentiableAt ℝ
      (canonicalSpacetimeContactTranslation point) 0 := by
    unfold canonicalSpacetimeContactTranslation
    fun_prop
  have outputDifferentiable : DifferentiableAt ℝ Output.coframe
      (canonicalSpacetimeContactTranslation point 0) := by
    simpa using output_coframe_differentiableAt point
  exact outputDifferentiable.comp 0 translationDifferentiable

private theorem fieldDirectionalDerivative_pi_apply_of_differentiableAt
    {I V : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → I → V)
    (point : BasePoint) (direction : LorentzianIndex) (index : I)
    (fieldDifferentiableAt : DifferentiableAt ℝ field point) :
    (fieldDirectionalDerivative field point direction) index =
      fieldDirectionalDerivative (fun candidate => field candidate index)
        point direction := by
  unfold fieldDirectionalDerivative
  have derivativeEquality := fderiv_apply fieldDifferentiableAt index
  have applied := congrArg
    (fun derivative : BasePoint →L[ℝ] V =>
      derivative (coordinateDirection direction)) derivativeEquality
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using applied.symm

private theorem coframe_fderiv_eq_of_firstJet_eq
    (first second : BasePoint → LorentzianCoframe)
    (firstPoint secondPoint : BasePoint)
    (firstDifferentiable : DifferentiableAt ℝ first firstPoint)
    (secondDifferentiable : DifferentiableAt ℝ second secondPoint)
    (firstJetEq :
      holonomicCoframeFirstJetAt first firstPoint =
        holonomicCoframeFirstJetAt second secondPoint) :
    fderiv ℝ first firstPoint = fderiv ℝ second secondPoint := by
  apply ContinuousLinearMap.ext
  intro tangent
  have tangentExpansion :
      tangent = ∑ direction : LorentzianIndex,
        tangent direction • coordinateDirection direction := by
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [coordinateDirection, Fin.sum_univ_four]
  rw [tangentExpansion, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  simp only [map_smul]
  congr 1
  ext internal coordinate
  change
    (fieldDirectionalDerivative first firstPoint direction) internal coordinate =
      (fieldDirectionalDerivative second secondPoint direction) internal coordinate
  calc
    _ = (fieldDirectionalDerivative
          (fun candidate => first candidate internal)
          firstPoint direction) coordinate :=
      congrFun
        (fieldDirectionalDerivative_pi_apply_of_differentiableAt
          first firstPoint direction internal firstDifferentiable)
        coordinate
    _ = fieldDirectionalDerivative
          (fun candidate => first candidate internal coordinate)
          firstPoint direction :=
      fieldDirectionalDerivative_pi_apply_of_differentiableAt
        (fun candidate => first candidate internal) firstPoint direction
        coordinate (differentiableAt_pi.mp firstDifferentiable internal)
    _ = fieldDirectionalDerivative
          (fun candidate => second candidate internal coordinate)
          secondPoint direction := by
      exact congrArg
        (fun jet => jet.derivative direction internal coordinate) firstJetEq
    _ = (fieldDirectionalDerivative
          (fun candidate => second candidate internal)
          secondPoint direction) coordinate :=
      (fieldDirectionalDerivative_pi_apply_of_differentiableAt
        (fun candidate => second candidate internal) secondPoint direction
        coordinate (differentiableAt_pi.mp secondDifferentiable internal)).symm
    _ = (fieldDirectionalDerivative second secondPoint direction)
          internal coordinate :=
      congrFun
        (fieldDirectionalDerivative_pi_apply_of_differentiableAt
          second secondPoint direction internal secondDifferentiable).symm
        coordinate

private theorem recenteredOutput_coframe_fderiv_origin_eq_contact
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (jetDefect :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    fderiv ℝ (RecenteredOutput point).coframe 0 =
      fderiv ℝ (Contact point).coframe 0 :=
  coframe_fderiv_eq_of_firstJet_eq
    (RecenteredOutput point).coframe (Contact point).coframe 0 0
    (recenteredOutput_coframe_differentiableAt point)
    (contact_coframe_differentiableAt point)
    (recenteredOutput_coframeFirstJet_origin_eq_contact point valueDefect
      jetDefect)

private theorem recenteredOutput_coframe_origin_eq_one
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0) :
    (RecenteredOutput point).coframe 0 = (1 : LorentzianCoframe) := by
  calc
    (RecenteredOutput point).coframe 0 = Output.coframe point :=
      fullyRecenterHolonomicConfiguration_coframe_origin Output point
    _ = (Contact point).coframe 0 :=
      coframe_point_eq_of_valueDefect_zero point valueDefect
    _ = Base.coframe point := by
      unfold Contact cartanECSynchronizedGravityTailProfileContact
      rw [
        sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact]
      exact fullyRecenterHolonomicConfiguration_coframe_origin Base point
    _ = 1 := congrFun
      fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one point

private theorem recenteredOutput_scalarCovariantDerivative_eq_contact
    (point : BasePoint) :
    holonomicScalarCovariantDerivative (RecenteredOutput point) =
      holonomicScalarCovariantDerivative (Contact point) := by
  funext candidate direction
  unfold holonomicScalarCovariantDerivative
  rw [recenteredOutput_scalar_eq_contact point,
    recenteredOutput_gaugeConnection_eq_contact point]

private theorem contact_scalarCovariantDerivative_eq_recenteredBase
    (point : BasePoint) :
    holonomicScalarCovariantDerivative (Contact point) =
      holonomicScalarCovariantDerivative
        (fullyRecenterHolonomicConfiguration Base point) := by
  funext candidate direction
  unfold holonomicScalarCovariantDerivative
  rw [contact_scalar_eq_recenter point,
    contact_gaugeConnection_eq_recenter point]

private theorem recenteredBase_scalarCovariantDerivative_contDiff
    (point : BasePoint) :
    ContDiff ℝ ∞
      (holonomicScalarCovariantDerivative
        (fullyRecenterHolonomicConfiguration Base point)) := by
  apply contDiff_pi'
  intro direction
  exact holonomicScalarCovariantDerivative_contDiff
    (fullyRecenterHolonomicConfiguration Base point)
    (fullyRecenterHolonomicConfiguration_smooth Base
      fixedP506L0CartanECConstraintCauchyGravityTailBase_smooth point)
    direction

private def gravityTailScalarMomentumInner
    (configuration : StageNineHolonomicConfiguration) :
    BasePoint →
      LorentzianCoframe ×
        (LorentzianIndex → ScalarCoordinateCarrier) :=
  fun candidate =>
    (configuration.coframe candidate,
      holonomicScalarCovariantDerivative configuration candidate)

private theorem recenteredOutput_scalarMomentumInner_differentiableAt
    (point : BasePoint) :
    DifferentiableAt ℝ
      (gravityTailScalarMomentumInner (RecenteredOutput point)) 0 := by
  unfold gravityTailScalarMomentumInner
  exact (recenteredOutput_coframe_differentiableAt point).prodMk
    (by
      rw [recenteredOutput_scalarCovariantDerivative_eq_contact point,
        contact_scalarCovariantDerivative_eq_recenteredBase point]
      exact (recenteredBase_scalarCovariantDerivative_contDiff point
        ).differentiable (by simp) |>.differentiableAt)

private theorem contact_scalarMomentumInner_differentiableAt
    (point : BasePoint) :
    DifferentiableAt ℝ
      (gravityTailScalarMomentumInner (Contact point)) 0 := by
  unfold gravityTailScalarMomentumInner
  exact (contact_coframe_differentiableAt point).prodMk
    (by
      rw [contact_scalarCovariantDerivative_eq_recenteredBase point]
      exact (recenteredBase_scalarCovariantDerivative_contDiff point
        ).differentiable (by simp) |>.differentiableAt)

private theorem recenteredOutput_scalarMomentumInner_origin_eq_contact
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0) :
    gravityTailScalarMomentumInner (RecenteredOutput point) 0 =
      gravityTailScalarMomentumInner (Contact point) 0 := by
  apply Prod.ext
  · exact (fullyRecenterHolonomicConfiguration_coframe_origin Output point
      ).trans (coframe_point_eq_of_valueDefect_zero point valueDefect)
  · exact congrFun
      (recenteredOutput_scalarCovariantDerivative_eq_contact point) 0

private theorem recenteredOutput_scalarMomentumInner_fderiv_origin_eq_contact
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (jetDefect :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    fderiv ℝ
        (gravityTailScalarMomentumInner (RecenteredOutput point)) 0 =
      fderiv ℝ
        (gravityTailScalarMomentumInner (Contact point)) 0 := by
  unfold gravityTailScalarMomentumInner
  let commonDerivative :=
    (fderiv ℝ (Contact point).coframe 0).prod
      (fderiv ℝ
        (holonomicScalarCovariantDerivative (Contact point)) 0)
  have contactScalarDifferentiable : DifferentiableAt ℝ
      (holonomicScalarCovariantDerivative (Contact point)) 0 := by
    rw [contact_scalarCovariantDerivative_eq_recenteredBase point]
    exact (recenteredBase_scalarCovariantDerivative_contDiff point
      ).differentiable (by simp) |>.differentiableAt
  have recenteredDerivative : HasFDerivAt
      (fun candidate : BasePoint =>
        ((RecenteredOutput point).coframe candidate,
          holonomicScalarCovariantDerivative
            (RecenteredOutput point) candidate))
      commonDerivative 0 := by
    apply HasFDerivAt.prodMk
    · rw [← recenteredOutput_coframe_fderiv_origin_eq_contact point
        valueDefect jetDefect]
      exact (recenteredOutput_coframe_differentiableAt point).hasFDerivAt
    · rw [recenteredOutput_scalarCovariantDerivative_eq_contact point]
      exact contactScalarDifferentiable.hasFDerivAt
  have contactDerivative : HasFDerivAt
      (fun candidate : BasePoint =>
        ((Contact point).coframe candidate,
          holonomicScalarCovariantDerivative (Contact point) candidate))
      commonDerivative 0 :=
    HasFDerivAt.prodMk (contact_coframe_differentiableAt point).hasFDerivAt
      contactScalarDifferentiable.hasFDerivAt
  exact recenteredDerivative.fderiv.trans contactDerivative.fderiv.symm

private theorem
    recenteredOutput_scalarMomentumComposition_fderiv_origin_eq_contact
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (jetDefect :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          gravityTailScalarMomentumInner (RecenteredOutput point)) 0 =
      fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          gravityTailScalarMomentumInner (Contact point)) 0 := by
  let outer :=
    scalarMomentumCoframeCovariantReadout direction derivativeDirection
  have outerAtContact : DifferentiableAt ℝ outer
      (gravityTailScalarMomentumInner (Contact point) 0) := by
    have contactCoframeOrigin :
        (Contact point).coframe 0 = (1 : LorentzianCoframe) := by
      calc
        (Contact point).coframe 0 = Output.coframe point :=
          (coframe_point_eq_of_valueDefect_zero point valueDefect).symm
        _ = (RecenteredOutput point).coframe 0 :=
          (fullyRecenterHolonomicConfiguration_coframe_origin Output point).symm
        _ = 1 := recenteredOutput_coframe_origin_eq_one point valueDefect
    change DifferentiableAt ℝ outer
      ((Contact point).coframe 0,
        holonomicScalarCovariantDerivative (Contact point) 0)
    rw [contactCoframeOrigin]
    exact
      (scalarMomentumCoframeCovariantReadout_contDiffAt_one direction
        derivativeDirection
        (holonomicScalarCovariantDerivative (Contact point) 0)
        ).differentiableAt (by simp)
  have outerAtRecentered : DifferentiableAt ℝ outer
      (gravityTailScalarMomentumInner (RecenteredOutput point) 0) := by
    rw [recenteredOutput_scalarMomentumInner_origin_eq_contact point
      valueDefect]
    exact outerAtContact
  change
    fderiv ℝ
        (outer ∘ gravityTailScalarMomentumInner (RecenteredOutput point)) 0 =
      fderiv ℝ
        (outer ∘ gravityTailScalarMomentumInner (Contact point)) 0
  rw [fderiv_comp 0 outerAtRecentered
      (recenteredOutput_scalarMomentumInner_differentiableAt point),
    fderiv_comp 0 outerAtContact
      (contact_scalarMomentumInner_differentiableAt point),
    recenteredOutput_scalarMomentumInner_origin_eq_contact point valueDefect]
  exact congrArg
    (fun innerDerivative :
        BasePoint →L[ℝ]
          (LorentzianCoframe ×
            (LorentzianIndex → ScalarCoordinateCarrier)) =>
      (fderiv ℝ outer
        (gravityTailScalarMomentumInner (Contact point) 0)).comp
          innerDerivative)
    (recenteredOutput_scalarMomentumInner_fderiv_origin_eq_contact point
      valueDefect jetDefect)

private theorem recenteredOutput_scalarDivergence_origin_eq_contact
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (jetDefect :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    (fun direction =>
      scalarDifferentialMomentumDivergence Source
        (RecenteredOutput point) direction 0) =
      fun direction =>
        scalarDifferentialMomentumDivergence Source
          (Contact point) direction 0 := by
  funext direction
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  unfold fieldDirectionalDerivative
  rw [scalarDifferentialMomentum_eq_readout,
    scalarDifferentialMomentum_eq_readout]
  change
    (fderiv ℝ
      (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
        gravityTailScalarMomentumInner (RecenteredOutput point)) 0)
        (coordinateDirection derivativeDirection) =
      (fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          gravityTailScalarMomentumInner (Contact point)) 0)
          (coordinateDirection derivativeDirection)
  rw [recenteredOutput_scalarMomentumComposition_fderiv_origin_eq_contact
    point valueDefect jetDefect direction derivativeDirection]

private theorem recenteredOutput_conjugateMatterCoordinates_eq_contact
    (point : BasePoint) :
    holonomicConjugateMatterCoordinates (RecenteredOutput point) =
      holonomicConjugateMatterCoordinates (Contact point) := by
  funext candidate
  unfold holonomicConjugateMatterCoordinates
  rw [recenteredOutput_conjugateMatter_eq_contact point]

private theorem contact_conjugateMatterCoordinates_eq_recenteredBase
    (point : BasePoint) :
    holonomicConjugateMatterCoordinates (Contact point) =
      holonomicConjugateMatterCoordinates
        (fullyRecenterHolonomicConfiguration Base point) := by
  funext candidate
  unfold holonomicConjugateMatterCoordinates
  rw [contact_conjugateMatter_eq_recenter point]

private theorem contact_conjugateMatterCoordinates_differentiableAt
    (point : BasePoint) :
    DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates (Contact point)) 0 := by
  rw [contact_conjugateMatterCoordinates_eq_recenteredBase point]
  exact
    (holonomicConjugateMatterCoordinates_contDiff
      (fullyRecenterHolonomicConfiguration Base point)
      (fullyRecenterHolonomicConfiguration_smooth Base
        fixedP506L0CartanECConstraintCauchyGravityTailBase_smooth point)
      ).differentiable (by simp) |>.differentiableAt

private theorem recenteredOutput_matterMomentumPointCoframe_eq_contact
    (point : BasePoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentumPointCoframe Source
        (RecenteredOutput point) direction derivativeDirection =
      matterDifferentialMomentumPointCoframe Source
        (Contact point) direction derivativeDirection := by
  funext joint
  unfold matterDifferentialMomentumPointCoframe
    matterDifferentialVariationVector generatedVolumeDensity
  simp only [toContinuumPointField, withCoframe]
  rw [recenteredOutput_conjugateMatter_eq_contact point]

private def gravityTailPointCoframeSection
    (configuration : StageNineHolonomicConfiguration) :
    BasePoint → BasePoint × LorentzianCoframe :=
  fun candidate => (candidate, configuration.coframe candidate)

private theorem recenteredOutput_pointCoframeSection_differentiableAt
    (point : BasePoint) :
    DifferentiableAt ℝ
      (gravityTailPointCoframeSection (RecenteredOutput point)) 0 := by
  unfold gravityTailPointCoframeSection
  exact differentiableAt_id.prodMk
    (recenteredOutput_coframe_differentiableAt point)

private theorem contact_pointCoframeSection_differentiableAt
    (point : BasePoint) :
    DifferentiableAt ℝ
      (gravityTailPointCoframeSection (Contact point)) 0 := by
  unfold gravityTailPointCoframeSection
  exact differentiableAt_id.prodMk (contact_coframe_differentiableAt point)

private theorem recenteredOutput_pointCoframeSection_origin_eq_contact
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0) :
    gravityTailPointCoframeSection (RecenteredOutput point) 0 =
      gravityTailPointCoframeSection (Contact point) 0 := by
  apply Prod.ext
  · rfl
  · exact (fullyRecenterHolonomicConfiguration_coframe_origin Output point
      ).trans (coframe_point_eq_of_valueDefect_zero point valueDefect)

private theorem recenteredOutput_pointCoframeSection_fderiv_origin_eq_contact
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (jetDefect :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    fderiv ℝ
        (gravityTailPointCoframeSection (RecenteredOutput point)) 0 =
      fderiv ℝ
        (gravityTailPointCoframeSection (Contact point)) 0 := by
  unfold gravityTailPointCoframeSection
  let commonDerivative :=
    (fderiv ℝ (fun candidate : BasePoint => candidate) 0).prod
      (fderiv ℝ (Contact point).coframe 0)
  have recenteredDerivative : HasFDerivAt
      (fun candidate : BasePoint =>
        (candidate, (RecenteredOutput point).coframe candidate))
      commonDerivative 0 := by
    apply HasFDerivAt.prodMk differentiableAt_id.hasFDerivAt
    rw [← recenteredOutput_coframe_fderiv_origin_eq_contact point
      valueDefect jetDefect]
    exact (recenteredOutput_coframe_differentiableAt point).hasFDerivAt
  have contactDerivative : HasFDerivAt
      (fun candidate : BasePoint =>
        (candidate, (Contact point).coframe candidate))
      commonDerivative 0 :=
    HasFDerivAt.prodMk differentiableAt_id.hasFDerivAt
      (contact_coframe_differentiableAt point).hasFDerivAt
  exact recenteredDerivative.fderiv.trans contactDerivative.fderiv.symm

private theorem
    recenteredOutput_matterMomentumComposition_fderiv_origin_eq_contact
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (jetDefect :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fderiv ℝ
        (matterDifferentialMomentumPointCoframe Source
            (RecenteredOutput point) direction derivativeDirection ∘
          gravityTailPointCoframeSection (RecenteredOutput point)) 0 =
      fderiv ℝ
        (matterDifferentialMomentumPointCoframe Source
            (Contact point) direction derivativeDirection ∘
          gravityTailPointCoframeSection (Contact point)) 0 := by
  let outer := matterDifferentialMomentumPointCoframe Source
    (Contact point) direction derivativeDirection
  have outerAtContact : DifferentiableAt ℝ outer
      (gravityTailPointCoframeSection (Contact point) 0) := by
    have contactCoframeOrigin :
        (Contact point).coframe 0 = (1 : LorentzianCoframe) := by
      calc
        (Contact point).coframe 0 = Output.coframe point :=
          (coframe_point_eq_of_valueDefect_zero point valueDefect).symm
        _ = (RecenteredOutput point).coframe 0 :=
          (fullyRecenterHolonomicConfiguration_coframe_origin Output point).symm
        _ = 1 := recenteredOutput_coframe_origin_eq_one point valueDefect
    change DifferentiableAt ℝ outer (0, (Contact point).coframe 0)
    rw [contactCoframeOrigin]
    exact
      matterDifferentialMomentumPointCoframe_differentiableAt_of_conjugateMatterCoordinates
        Source (Contact point) 0 1 (by norm_num)
        (contact_conjugateMatterCoordinates_differentiableAt point)
        direction derivativeDirection
  have outerAtRecentered : DifferentiableAt ℝ outer
      (gravityTailPointCoframeSection (RecenteredOutput point) 0) := by
    rw [recenteredOutput_pointCoframeSection_origin_eq_contact point
      valueDefect]
    exact outerAtContact
  rw [recenteredOutput_matterMomentumPointCoframe_eq_contact point direction
    derivativeDirection]
  change
    fderiv ℝ
        (outer ∘ gravityTailPointCoframeSection (RecenteredOutput point)) 0 =
      fderiv ℝ
        (outer ∘ gravityTailPointCoframeSection (Contact point)) 0
  rw [fderiv_comp 0 outerAtRecentered
      (recenteredOutput_pointCoframeSection_differentiableAt point),
    fderiv_comp 0 outerAtContact
      (contact_pointCoframeSection_differentiableAt point),
    recenteredOutput_pointCoframeSection_origin_eq_contact point valueDefect]
  exact congrArg
    (fun innerDerivative :
        BasePoint →L[ℝ] (BasePoint × LorentzianCoframe) =>
      (fderiv ℝ outer
        (gravityTailPointCoframeSection (Contact point) 0)).comp
          innerDerivative)
    (recenteredOutput_pointCoframeSection_fderiv_origin_eq_contact point
      valueDefect jetDefect)

private theorem recenteredOutput_matterDivergence_origin_eq_contact
    (point : BasePoint)
    (valueDefect :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (jetDefect :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    (fun direction =>
      matterDifferentialMomentumDivergence Source
        (RecenteredOutput point) direction 0) =
      fun direction =>
        matterDifferentialMomentumDivergence Source
          (Contact point) direction 0 := by
  funext direction
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  unfold fieldDirectionalDerivative
  rw [matterDifferentialMomentum_eq_pointCoframe_actualSection,
    matterDifferentialMomentum_eq_pointCoframe_actualSection]
  change
    (fderiv ℝ
      (matterDifferentialMomentumPointCoframe Source
          (RecenteredOutput point) direction derivativeDirection ∘
        gravityTailPointCoframeSection (RecenteredOutput point)) 0)
        (coordinateDirection derivativeDirection) =
      (fderiv ℝ
        (matterDifferentialMomentumPointCoframe Source
            (Contact point) direction derivativeDirection ∘
          gravityTailPointCoframeSection (Contact point)) 0)
          (coordinateDirection derivativeDirection)
  rw [recenteredOutput_matterMomentumComposition_fderiv_origin_eq_contact
    point valueDefect jetDefect direction derivativeDirection]

private theorem gravityAuxiliaryExterior_point_eq
    (point : BasePoint)
    (coframeValue :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (connectionValue :
      fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect point =
        0)
    (coframeJet :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    holonomicGravityAuxiliaryExteriorCovariantDerivative Output point =
      holonomicGravityAuxiliaryExteriorCovariantDerivative (Contact point) 0 := by
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
  rw [gravityConnection_point_eq_of_valueDefect_zero point connectionValue]
  apply congrArg
    (pointwisePhysicalBivectorExteriorCovariantDerivative
      ((Contact point).gravityConnection 0))
  apply holonomicGravityAuxiliaryJet_eq_of_iiPlus_of_coframeFirstJet_eq
  · funext candidate
    exact output_gravityAuxiliary_eq_iiPlus candidate
  · funext candidate
    unfold Contact cartanECSynchronizedGravityTailProfileContact
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_auxiliary
        Source (fullyRecenterHolonomicConfiguration Base point) 0 candidate
  · exact output_coframe_component_differentiableAt point
  · exact contact_coframe_component_differentiableAt point
  · exact coframeFirstJet_point_eq point coframeValue coframeJet

private theorem seam_coframe_zero
    (point : BasePoint)
    (coframeValue :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).coframe = 0 := by
  simpa [
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_coframe_eq_valueDefect]
    using coframeValue

private theorem seam_curvature_zero
    (point : BasePoint)
    (curvature :
      fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
        point = 0) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).gravityCurvature = 0 := by
  simpa [
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_gravityCurvature_eq_integrabilityFactor]
    using curvature

private theorem seam_auxiliary_zero
    (point : BasePoint)
    (coframeValue :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).gravityAuxiliary = 0 := by
  change Output.gravityAuxiliary point - (Contact point).gravityAuxiliary 0 = 0
  apply sub_eq_zero.mpr
  rw [output_gravityAuxiliary_eq_iiPlus,
    contact_gravityAuxiliary_eq_iiPlus,
    coframe_point_eq_of_valueDefect_zero point coframeValue]

/-- The fixed radial coframe realization settles the generated gravity
auxiliary coordinate on the complete initial Cauchy slice through the
source-action simplicity law; no auxiliary equation is supplied. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_gravityAuxiliary_zeroSlice
    (space : StageNineSpatialPoint) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam
      (canonicalCauchySlicePoint 0 space)).gravityAuxiliary = 0 := by
  apply seam_auxiliary_zero
  rw [←
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_coframe_eq_valueDefect]
  exact
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_coframe_zeroSlice
      space

private theorem gravityAuxiliary_point_eq
    (point : BasePoint)
    (coframeValue :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0) :
    Output.gravityAuxiliary point = (Contact point).gravityAuxiliary 0 := by
  rw [output_gravityAuxiliary_eq_iiPlus,
    contact_gravityAuxiliary_eq_iiPlus,
    coframe_point_eq_of_valueDefect_zero point coframeValue]

private theorem contravariantGravityCurvature_point_eq
    (point : BasePoint)
    (curvature :
      fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
        point = 0) :
    holonomicContravariantGravityCurvature Output point =
      holonomicContravariantGravityCurvature (Contact point) 0 := by
  exact congrArg gravityInternalPairVarianceNormalization
    (gravityCurvature_point_eq_of_integrabilityFactor_zero point curvature)

private theorem gravitySimplicityMultiplier_point_eq
    (point : BasePoint)
    (coframeValue :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (curvature :
      fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
        point = 0) :
    Output.gravitySimplicityMultiplier point =
      (Contact point).gravitySimplicityMultiplier 0 := by
  calc
    Output.gravitySimplicityMultiplier point =
        formNativeGravityReactionField Output point := by
      exact congrFun
        (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_reactionSelfGenerated
          Source Current) point
    _ = formNativeGravityReactionField (Contact point) 0 := by
      unfold formNativeGravityReactionField
      rw [gravityAuxiliary_point_eq point coframeValue,
        contravariantGravityCurvature_point_eq point curvature]
    _ = (Contact point).gravitySimplicityMultiplier 0 := by
      apply congrFun
      unfold Contact cartanECSynchronizedGravityTailProfileContact
      exact
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_reactionSelfGenerated
          Source (fullyRecenterHolonomicConfiguration Base point) 0).symm

private theorem seam_multiplier_zero
    (point : BasePoint)
    (coframeValue :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (curvature :
      fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
        point = 0) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).gravitySimplicityMultiplier = 0 := by
  change
    Output.gravitySimplicityMultiplier point -
        (Contact point).gravitySimplicityMultiplier 0 = 0
  exact sub_eq_zero.mpr
    (gravitySimplicityMultiplier_point_eq point coframeValue curvature)

private theorem seam_matterCovariantDerivative_zero
    (point : BasePoint)
    (connectionValue :
      fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect point =
        0) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).matterCovariantDerivative = 0 := by
  change
    holonomicMatterCovariantDerivative Output point -
        holonomicMatterCovariantDerivative (Contact point) 0 = 0
  apply sub_eq_zero.mpr
  exact matterCovariantDerivative_point_eq point
    (gravityConnection_point_eq_of_valueDefect_zero point connectionValue)

private theorem seam_connection_zero
    (point : BasePoint)
    (connectionValue :
      fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect point =
        0) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).gravityConnection = 0 := by
  simpa [
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_gravityConnection_eq_valueDefect]
    using connectionValue

private theorem seam_auxiliaryExterior_zero
    (point : BasePoint)
    (coframeValue :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (connectionValue :
      fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect point =
        0)
    (coframeJet :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).gravityAuxiliaryExteriorCovariantDerivative = 0 := by
  change
    holonomicGravityAuxiliaryExteriorCovariantDerivative Output point -
        holonomicGravityAuxiliaryExteriorCovariantDerivative (Contact point) 0 =
      0
  exact sub_eq_zero.mpr
    (gravityAuxiliaryExterior_point_eq point coframeValue connectionValue
      coframeJet)

private theorem seam_scalarDivergence_zero
    (point : BasePoint)
    (coframeValue :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (coframeJet :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).scalarDifferentialMomentumDivergence = 0 := by
  change
    (fun direction =>
      scalarDifferentialMomentumDivergence Source Output direction point) -
        (fun direction =>
          scalarDifferentialMomentumDivergence Source
            (Contact point) direction 0) = 0
  apply sub_eq_zero.mpr
  exact
    (scalarDifferentialMomentumDivergence_fullyRecenter_origin_unconditional
      Source Output point).symm.trans
      (recenteredOutput_scalarDivergence_origin_eq_contact point coframeValue
        coframeJet)

private theorem seam_matterDivergence_zero
    (point : BasePoint)
    (coframeValue :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0)
    (coframeJet :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).matterDifferentialMomentumDivergence = 0 := by
  change
    (fun direction =>
      matterDifferentialMomentumDivergence Source Output direction point) -
        (fun direction =>
          matterDifferentialMomentumDivergence Source
            (Contact point) direction 0) = 0
  apply sub_eq_zero.mpr
  exact
    (matterDifferentialMomentumDivergence_fullyRecenter_origin_unconditional
      Source Output point).symm.trans
      (recenteredOutput_matterDivergence_origin_eq_contact point coframeValue
        coframeJet)

/-- The complete action-jet seam closes from the four source-generated
coframe-value, connection-value, curvature and coframe-first-jet factor
families. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_eq_zero_of_primitive_factors
    (point : BasePoint)
    (coframeValue :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point = 0)
    (connectionValue :
      fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect point = 0)
    (curvature :
      fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor point = 0)
    (coframeJet :
      ∀ internal coordinate : LorentzianIndex,
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source Current point internal coordinate = 0) :
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point = 0 := by
  apply GravityTailActionJetSeam.ext
  · exact seam_coframe_zero point coframeValue
  · exact seam_curvature_zero point curvature
  · exact seam_auxiliary_zero point coframeValue
  · exact seam_multiplier_zero point coframeValue curvature
  · exact seam_matterCovariantDerivative_zero point connectionValue
  · exact seam_connection_zero point connectionValue
  · exact seam_auxiliaryExterior_zero point coframeValue connectionValue
      coframeJet
  · simpa only [gravityTailActionJetSeam_zero_scalarDivergence] using
      seam_scalarDivergence_zero point coframeValue coframeJet
  · simpa only [gravityTailActionJetSeam_zero_matterDivergence] using
      seam_matterDivergence_zero point coframeValue coframeJet

/-- The coframe path begins at the exact gravity-base value, so its value
factor vanishes at the source occurrence. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect_origin_zero :
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect 0 = 0 := by
  unfold fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect
  rw [cartanECSynchronizedGravityTailCoframePathField_zero]
  unfold cartanECSynchronizedGravityTailCoframePathAnchor
  simp

/-- The Lorentz path and the occurrence-local normalized contact share their
exact source connection value. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect_origin_zero :
    fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect 0 = 0 := by
  unfold fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect
  rw [cartanECSynchronizedGravityTailPathConnectionField_zero]
  unfold cartanECSynchronizedGravityTailPathAnchor
  rw [cartanECSynchronizedGravityTailProfileContact_connection_normalForm]
  rw [normalizedAffineLorentzConnectionField_zero]
  rw [cartanECSynchronizedGravityTailProfileOrigin_eq_base]
  simp

/-- At the source occurrence, emitted curvature and the local profile target
are the same source-current curvature, so the generated integrability factor
vanishes. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor_origin_zero :
    fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor 0 = 0 := by
  rw [←
    fixedP506L0CartanECConstraintCauchyGravityTail_gravityCurvature_eq_target_iff_integrabilityFactor_zero]
  calc
    holonomicGravityCurvature Output 0 =
        holonomicGravityCurvature Current 0 :=
      fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_curvature_origin_eq_current
    _ = cartanECSynchronizedGravityTailProfileTarget Source Current 0 :=
      fixedP506L0CartanECConstraintCauchyGravityTailProfileTarget_origin_eq_current.symm

/-- All four generated primitive factors close at the exact radial source,
hence the complete nine-coordinate action-jet seam closes there. -/
theorem fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_origin_zero :
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam 0 = 0 := by
  exact
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_eq_zero_of_primitive_factors
      0
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect_origin_zero
      fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect_origin_zero
      fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor_origin_zero
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialFirstJetDefect_origin_zero

end

end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailAllPointResidualNormalForm
