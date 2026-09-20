import H0mework.Physics.CurrentAction.LorentzContactResponse
import H0mework.Physics.MatterPreparation.ContorsionSpatialProfileActualLift
import H0mework.Physics.CoframeJets.StateDependentCartanCoframeFirstJetLocalActualLift

/-!
# S9-C3h200j: restart the complete action on the generated spatial profile

C3h200i generated a nonconstant spatial coframe/simple-`B` profile from the
eighteen Lorentz action coordinates of the exact P506/L0 pre-contorsion
actual.  This module restricts that actual to its canonical Cauchy slice and
uses the resulting whole spatial field as the next current:

```text
exact P506/L0 source/action
→ C3h200i spatial-profile actual
→ canonical Cauchy current U_profile
→ action-prepared U_profile
→ complete current-state response recomputed at canonical contact 0.
```

The current is not replaced by a constant contact value: its spatial profile
is precisely what carries the BF-momentum divergence.  Only contact `0` is an
identity-coframe contact, so the C3h198 identity principal is invoked there,
not globally.  Old P286 or matter equation receipts are not transported.
Temporal Lorentz Gauss remains a downstream acceptance and is not an input to
any constructor in this module.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCurrentResponse

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineConnectionSectorSourceBalance
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzContactResponse
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineEinsteinCartanSkewCoframeActualResponseOperator
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEinsteinCartanSpatialSkewCoframeActualResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionActionVariation
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
open StageNineStateDependentCartanCoframeFirstJetLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- The whole C3h200i spatial profile, restricted to canonical time zero.
It is a named carrier rather than an `abbrev`, so downstream action transport
does not repeatedly unfold the complete generated actual during unification.
-/
def PreContorsionSpatialProfileCurrent : StageNineCauchyState :=
  canonicalCauchyRestriction 0 preContorsionSpatialProfileActual

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 0 = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- Spatial differentiation after canonical Cauchy restriction is the
corresponding spacetime directional derivative.  This is a chain-rule
bridge, not a regularity receipt stored in the Cauchy state. -/
private theorem fderiv_canonicalCauchySlicePoint_spatial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → V)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (derivativeDirection : Fin 3)
    (differentiable : DifferentiableAt ℝ field
      (canonicalCauchySlicePoint time space)) :
    fderiv ℝ (field ∘ canonicalCauchySlicePoint time) space
        (canonicalSpatialCoordinateDirection derivativeDirection) =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint time space)
        derivativeDirection.succ := by
  have derivative := differentiable.hasFDerivAt.comp space
    (canonicalCauchySlicePoint_hasFDerivAt time space)
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

private theorem finThree_sum_eq_of_pointwise
    (first second : Fin 3 → ℝ)
    (pointwise : ∀ direction, first direction = second direction) :
    (∑ direction : Fin 3, first direction) =
      ∑ direction : Fin 3, second direction := by
  apply Finset.sum_congr rfl
  intro direction _
  exact pointwise direction

/-- The canonical spatial basis used by the fresh finite dual is the same
ambient Lorentz one-form basis used by the profile actual. -/
private theorem canonicalSpatialCoordinateDirection_eq_full
    (spatialDirection : Fin 3)
    (internalPair : Fin 6) :
    canonicalLorentzSpatialBivectorOneForm
        (canonicalLorentzSpatialBivectorCoordinateDirection
          spatialDirection internalPair) =
      lorentzBivectorOneFormCoordinateDirection spatialDirection.succ
        internalPair := by
  funext formDirection candidatePair
  refine Fin.cases ?_ (fun candidateSpatial => ?_) formDirection
  · fin_cases spatialDirection <;>
      simp [canonicalLorentzSpatialBivectorOneForm,
        lorentzBivectorOneFormCoordinateDirection]
  · simp [canonicalLorentzSpatialBivectorOneForm,
      canonicalLorentzSpatialBivectorCoordinateDirection,
      lorentzBivectorOneFormCoordinateDirection]

@[simp] theorem preContorsionSpatialProfileCurrent_coframe_origin :
    PreContorsionSpatialProfileCurrent.coframe 0 = 1 := by
  change
    preContorsionSpatialProfileActual.coframe
        (canonicalCauchySlicePoint 0 0) = 1
  rw [canonicalCauchySlicePoint_zero_zero,
    preContorsionSpatialProfileActual_coframe_origin]

/-- `B = II⁺(e)` is inherited pointwise from the generated profile actual, so
the latest current is already action-prepared. -/
theorem preContorsionSpatialProfileCurrent_gravityAuxiliaryPrepared :
    (fun space =>
        actionGeneratedGravityAuxiliary
          PreContorsionSpatialProfileCurrent space) =
      PreContorsionSpatialProfileCurrent.gravityAuxiliary := by
  funext space
  change
    physicalIIPlusBivector
        (preContorsionSpatialProfileActual.coframe
          (canonicalCauchySlicePoint 0 space)) =
      preContorsionSpatialProfileActual.gravityAuxiliary
        (canonicalCauchySlicePoint 0 space)
  exact
    (congrFun
      preContorsionSpatialProfileActual_gravityAuxiliary_generated
      (canonicalCauchySlicePoint 0 space)).symm

theorem preContorsionSpatialProfileCurrent_actionPrepared :
    sourceActionGeneratedJointPrimitiveActionInitialState
        PreContorsionSpatialProfileCurrent =
      PreContorsionSpatialProfileCurrent := by
  exact actionInitialState_eq_self_of_gravityAuxiliaryPrepared _
    preContorsionSpatialProfileCurrent_gravityAuxiliaryPrepared

/-- The zero step is the latest profile current itself, not a reprojection to
an identity-coframe carrier. -/
theorem preContorsionSpatialProfileCurrent_zeroStep :
    currentCanonicalFullActionLorentzStateResponseUpdate
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0 =
      PreContorsionSpatialProfileCurrent := by
  exact
    currentCanonicalFullActionLorentzStateResponseUpdate_zero_of_actionPrepared
      positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
      preContorsionSpatialProfileCurrent_actionPrepared

/-- The nonconstant static spatial jet survives restriction to the latest
Cauchy current.  It is a spatial derivative of `e`, not a time response or a
derivative of the coframe velocity. -/
theorem preContorsionSpatialProfileCurrent_coframeSpatialDerivative
    (space : StageNineSpatialPoint)
    (derivativeDirection : Fin 3)
    (internal coordinate : LorentzianIndex) :
    cauchyCoframeSpatialDerivativeCoordinate
        PreContorsionSpatialProfileCurrent space derivativeDirection
        internal coordinate =
      fieldDirectionalDerivative
        (fun point =>
          preContorsionSpatialProfileActual.coframe point internal coordinate)
        (canonicalCauchySlicePoint 0 space)
        derivativeDirection.succ := by
  exact cauchyCoframeSpatialDerivativeCoordinate_restriction
    0 preContorsionSpatialProfileActual
    preContorsionSpatialProfileActual_smooth
    space derivativeDirection internal coordinate

/-- Complete C3h198 response authority, recomputed on the latest whole
profile current at its identity-coframe contact. -/
theorem preContorsionSpatialProfileCurrent_contactResponse :
    StageNineCurrentCanonicalFullActionLorentzContactResponseLaw
      positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0 := by
  exact currentCanonicalFullActionLorentzContactResponse_realizes
    positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0
    preContorsionSpatialProfileCurrent_coframe_origin

/-! ## Coherent BF-momentum replay -/

private theorem profileCurrent_freshActual_coframe_origin
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent space).coframe 0 =
      preContorsionSpatialProfileActual.coframe
        (canonicalCauchySlicePoint 0 space) := by
  rw [currentCanonicalGravityPreservingActual_coframe]
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
      space).coframe 0 = _
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe]
  rfl

private theorem profileCurrent_freshActual_gravityAuxiliary_origin
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent space).gravityAuxiliary 0 =
      preContorsionSpatialProfileActual.gravityAuxiliary
        (canonicalCauchySlicePoint 0 space) := by
  rw [currentCanonicalGravityPreservingActual_gravityAuxiliary]
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
      space).gravityAuxiliary 0 = _
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_auxiliary]
  change
    physicalIIPlusBivector
        (preContorsionSpatialProfileActual.coframe
          (canonicalCauchySlicePoint 0 space)) = _
  exact
    (congrFun
      preContorsionSpatialProfileActual_gravityAuxiliary_generated
      (canonicalCauchySlicePoint 0 space)).symm

/-- At every contact, the freshly recomputed momentum value is exactly the
momentum of the already generated profile actual at the matching slice point.
Only `e` and its derived `B` are consumed by this readout. -/
theorem preContorsionSpatialProfileCurrent_BFMomentumEvaluation_eq_profile
    (derivativeDirection : LorentzianIndex)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    currentCanonicalFullActionLorentzBFMomentumEvaluation
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        derivativeDirection space direction =
      lorentzConnectionBFDifferentialMomentum
        preContorsionSpatialProfileActual
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          (canonicalLorentzSpatialBivectorOneForm direction))
        (canonicalCauchySlicePoint 0 space) := by
  unfold currentCanonicalFullActionLorentzBFMomentumEvaluation
    lorentzConnectionBFDifferentialMomentum generatedVolumeDensity
    toContinuumPointField
  dsimp only
  rw [profileCurrent_freshActual_coframe_origin,
    profileCurrent_freshActual_gravityAuxiliary_origin]

/-- Differentiating the whole fresh contact family recovers the corresponding
spacetime derivative of the generated profile momentum. -/
theorem preContorsionSpatialProfileCurrent_BFMomentumDerivative_eq_profile
    (derivativeDirection : Fin 3)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    currentCanonicalFullActionLorentzSpatialBFMomentumDerivative
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        space derivativeDirection direction =
      lorentzConnectionSpatialBFMomentumDerivative
        preContorsionSpatialProfileActual
        (canonicalLorentzSpatialBivectorOneForm direction)
        (canonicalCauchySlicePoint 0 space) derivativeDirection := by
  unfold currentCanonicalFullActionLorentzSpatialBFMomentumDerivative
    lorentzConnectionSpatialBFMomentumDerivative
  rw [show
    (currentCanonicalFullActionLorentzBFMomentumEvaluation
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        derivativeDirection.succ · direction) =
      (lorentzConnectionBFDifferentialMomentum
        preContorsionSpatialProfileActual
        (lorentzConnectionExteriorDerivativeDirection
          derivativeDirection.succ
          (canonicalLorentzSpatialBivectorOneForm direction))) ∘
        canonicalCauchySlicePoint 0 by
    funext candidate
    exact
      preContorsionSpatialProfileCurrent_BFMomentumEvaluation_eq_profile
        derivativeDirection.succ candidate direction]
  exact fderiv_canonicalCauchySlicePoint_spatial
    (lorentzConnectionBFDifferentialMomentum
      preContorsionSpatialProfileActual
      (lorentzConnectionExteriorDerivativeDirection derivativeDirection.succ
        (canonicalLorentzSpatialBivectorOneForm direction)))
    0 space derivativeDirection
    ((lorentzConnectionBFDifferentialMomentum_contDiff
      preContorsionSpatialProfileActual
      preContorsionSpatialProfileActual_smooth
      preContorsionSpatialProfileActual_nondegenerate
      (lorentzConnectionExteriorDerivativeDirection derivativeDirection.succ
        (canonicalLorentzSpatialBivectorOneForm direction))).differentiable
      (by simp)).differentiableAt

/-- The whole fresh contact-family spatial divergence is the generated
profile actual's spatial divergence at the matching zero-slice point.  This
is an all-space momentum transporter; no temporal Gauss equation is claimed.
-/
theorem
    preContorsionSpatialProfileCurrent_spatialBFMomentumDivergence_eq_profileSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        space direction =
      lorentzConnectionSpatialBFMomentumDivergence
        preContorsionSpatialProfileActual
        (canonicalLorentzSpatialBivectorOneForm direction)
        (canonicalCauchySlicePoint 0 space) := by
  rw [currentCanonicalFullActionLorentzSpatialBFMomentumDivergence_eq_sum,
    lorentzConnectionSpatialBFMomentumDivergence_eq_sum]
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact preContorsionSpatialProfileCurrent_BFMomentumDerivative_eq_profile
    derivativeDirection space direction

/-- The profile has no temporal input jet.  Consequently its temporal
BF-momentum derivative vanishes; this is an output of the spatial producer,
not a supplied temporal receipt. -/
private theorem preContorsionSpatialProfileActual_BFMomentum_timeDerivative_zero
    (direction : LorentzSpatialBivectorDirection) :
    fieldDirectionalDerivative
        (lorentzConnectionBFDifferentialMomentum
          preContorsionSpatialProfileActual
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalLorentzSpatialBivectorOneForm direction)))
        0 canonicalLorentzianTimeDirection = 0 := by
  exact
    spatialSkewCoframeActualOn_BFMomentum_timeDerivative_zero
      PreContorsionP286Actual generatedSpatialSkewCoframeJet
      (canonicalLorentzSpatialBivectorOneForm direction)

/-- The three contact-family derivatives are precisely the three spatial
summands of the profile-actual momentum divergence. -/
private theorem
    preContorsionSpatialProfileCurrent_spatialBFMomentumDivergence_eq_spatial
    (direction : LorentzSpatialBivectorDirection) :
    currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        0 direction =
      lorentzConnectionSpatialBFMomentumDivergence
        preContorsionSpatialProfileActual
        (canonicalLorentzSpatialBivectorOneForm direction) 0 := by
  have currentSumEqProfileSlice :
      (∑ derivativeDirection : Fin 3,
        currentCanonicalFullActionLorentzSpatialBFMomentumDerivative
          positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
          0 derivativeDirection direction) =
        ∑ derivativeDirection : Fin 3,
          lorentzConnectionSpatialBFMomentumDerivative
            preContorsionSpatialProfileActual
            (canonicalLorentzSpatialBivectorOneForm direction)
            (canonicalCauchySlicePoint 0 0) derivativeDirection := by
    exact finThree_sum_eq_of_pointwise _ _ fun derivativeDirection =>
      preContorsionSpatialProfileCurrent_BFMomentumDerivative_eq_profile
        derivativeDirection 0 direction
  have profileFamilySliceEqOrigin :
      (fun derivativeDirection : Fin 3 =>
        lorentzConnectionSpatialBFMomentumDerivative
          preContorsionSpatialProfileActual
          (canonicalLorentzSpatialBivectorOneForm direction)
          (canonicalCauchySlicePoint 0 0) derivativeDirection) =
        fun derivativeDirection : Fin 3 =>
          lorentzConnectionSpatialBFMomentumDerivative
            preContorsionSpatialProfileActual
            (canonicalLorentzSpatialBivectorOneForm direction)
            0 derivativeDirection := by
    exact congrArg
      (fun point : BasePoint =>
        fun derivativeDirection : Fin 3 =>
          lorentzConnectionSpatialBFMomentumDerivative
            preContorsionSpatialProfileActual
            (canonicalLorentzSpatialBivectorOneForm direction)
            point derivativeDirection)
      canonicalCauchySlicePoint_zero_zero
  have profileSumSliceEqOrigin := congrArg
    (fun family : Fin 3 → ℝ =>
      ∑ derivativeDirection : Fin 3, family derivativeDirection)
    profileFamilySliceEqOrigin
  exact
    (currentCanonicalFullActionLorentzSpatialBFMomentumDivergence_eq_sum
      positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
      0 direction).trans
      (currentSumEqProfileSlice.trans
        (profileSumSliceEqOrigin.trans
          (lorentzConnectionSpatialBFMomentumDivergence_eq_sum
            preContorsionSpatialProfileActual
            (canonicalLorentzSpatialBivectorOneForm direction) 0).symm))

private theorem
    preContorsionSpatialProfileActual_spatialBFMomentumDivergence_eq_full
    (direction : LorentzSpatialBivectorDirection) :
    lorentzConnectionSpatialBFMomentumDivergence
        preContorsionSpatialProfileActual
        (canonicalLorentzSpatialBivectorOneForm direction) 0 =
      lorentzConnectionBFDifferentialMomentumDivergence
        preContorsionSpatialProfileActual
        (canonicalLorentzSpatialBivectorOneForm direction) 0 := by
  rw [lorentzConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial]
  unfold lorentzConnectionTemporalBFMomentumDerivative
  rw [preContorsionSpatialProfileActual_BFMomentum_timeDerivative_zero]
  simp

/-- At the canonical contact, the fresh current-family spatial divergence is
the full profile-actual divergence.  The missing fourth summand is proved
zero from the producer's zero temporal input jet. -/
theorem preContorsionSpatialProfileCurrent_spatialBFMomentumDivergence_eq_profile
    (direction : LorentzSpatialBivectorDirection) :
    currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        0 direction =
      lorentzConnectionBFDifferentialMomentumDivergence
        preContorsionSpatialProfileActual
        (canonicalLorentzSpatialBivectorOneForm direction) 0 := by
  exact
    (preContorsionSpatialProfileCurrent_spatialBFMomentumDivergence_eq_spatial
      direction).trans
      (preContorsionSpatialProfileActual_spatialBFMomentumDivergence_eq_full
        direction)

/-! ## Fresh algebraic-action replay at the same contact -/

private theorem
    profileCurrent_freshActual_gravityConnection_origin_eq_profileSlice
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent space).gravityConnection 0 =
      preContorsionSpatialProfileActual.gravityConnection
        (canonicalCauchySlicePoint 0 space) := by
  rw [currentCanonicalGravityPreservingActual_gravityConnection_origin]
  rfl

private theorem profileCurrent_freshActual_matter_origin_eq_profileSlice
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent space).matter 0 =
      preContorsionSpatialProfileActual.matter
        (canonicalCauchySlicePoint 0 space) := by
  rw [currentCanonicalGravityPreservingActual_matter_origin_eq_currentSlice]
  rfl

private theorem
    profileCurrent_freshActual_conjugateMatter_origin_eq_profileSlice
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent space).conjugateMatter 0 =
      preContorsionSpatialProfileActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) := by
  rw [
    currentCanonicalGravityPreservingActual_conjugateMatter_origin_eq_currentSlice]
  rfl

private theorem profileCurrent_freshActual_gravityBF_eq_profileSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzBivectorOneForm) :
    lorentzGravityBFAlgebraicCoefficient
        (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent space)
        direction 0 =
      lorentzGravityBFAlgebraicCoefficient preContorsionSpatialProfileActual
        direction (canonicalCauchySlicePoint 0 space) := by
  have curvatureDirectionEq :
      lorentzConnectionAlgebraicCurvatureDirection
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionSpatialProfileCurrent space)
          direction 0 =
        lorentzConnectionAlgebraicCurvatureDirection
          preContorsionSpatialProfileActual direction
          (canonicalCauchySlicePoint 0 space) := by
    funext internalPair spacetimePair
    unfold lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    rw [
      profileCurrent_freshActual_gravityConnection_origin_eq_profileSlice]
  unfold lorentzGravityBFAlgebraicCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [profileCurrent_freshActual_coframe_origin,
    profileCurrent_freshActual_gravityAuxiliary_origin,
    curvatureDirectionEq]

private theorem profileCurrent_freshActual_matterSpin_eq_profileSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzBivectorOneForm) :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent space)
        direction 0 =
      lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        preContorsionSpatialProfileActual direction
        (canonicalCauchySlicePoint 0 space) := by
  have spinCoordinatesEq :
      actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionSpatialProfileCurrent space)
          0 =
        actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          preContorsionSpatialProfileActual
          (canonicalCauchySlicePoint 0 space) := by
    exact actualMatterSpinActionCoordinates_eq_of_fields_at
      positiveSmoothUnifiedSource
      (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent space)
      preContorsionSpatialProfileActual 0 (canonicalCauchySlicePoint 0 space)
      (profileCurrent_freshActual_coframe_origin space)
      (profileCurrent_freshActual_matter_origin_eq_profileSlice space)
      (profileCurrent_freshActual_conjugateMatter_origin_eq_profileSlice space)
  have spinDualEq :
      einsteinCartanMatterSpinActionDual positiveSmoothUnifiedSource
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionSpatialProfileCurrent space)
          0 =
        einsteinCartanMatterSpinActionDual positiveSmoothUnifiedSource
          preContorsionSpatialProfileActual
          (canonicalCauchySlicePoint 0 space) := by
    apply einsteinCartanLorentzDual_eq_of_coordinate_eq
    intro formDirection internalPair
    exact congrFun (congrFun spinCoordinatesEq formDirection) internalPair
  exact DFunLike.congr_fun spinDualEq direction

/-- At every profile contact, the fresh local action graph reads exactly the
algebraic Lorentz coefficient of the already generated profile actual at the
matching zero-slice point.  This is a field-value transporter, not an
equation or stationarity receipt. -/
theorem preContorsionSpatialProfileCurrent_freshAlgebraicAction_eq_profileSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource
        (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent space)
        direction 0 =
      lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource preContorsionSpatialProfileActual direction
        (canonicalCauchySlicePoint 0 space) := by
  rw [lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    profileCurrent_freshActual_gravityBF_eq_profileSlice,
    profileCurrent_freshActual_matterSpin_eq_profileSlice]

private theorem profileCurrent_freshActual_coframe_origin_eq_profile :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent 0).coframe 0 =
      preContorsionSpatialProfileActual.coframe 0 := by
  rw [profileCurrent_freshActual_coframe_origin,
    canonicalCauchySlicePoint_zero_zero]

private theorem profileCurrent_freshActual_matter_origin_eq_profile :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent 0).matter 0 =
      preContorsionSpatialProfileActual.matter 0 := by
  rw [currentCanonicalGravityPreservingActual_matter_origin_eq_currentSlice]
  change
    preContorsionSpatialProfileActual.matter
        (canonicalCauchySlicePoint 0 0) =
      preContorsionSpatialProfileActual.matter 0
  rw [canonicalCauchySlicePoint_zero_zero]

private theorem profileCurrent_freshActual_conjugateMatter_origin_eq_profile :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent 0).conjugateMatter 0 =
      preContorsionSpatialProfileActual.conjugateMatter 0 := by
  rw [
    currentCanonicalGravityPreservingActual_conjugateMatter_origin_eq_currentSlice]
  change
    preContorsionSpatialProfileActual.conjugateMatter
        (canonicalCauchySlicePoint 0 0) =
      preContorsionSpatialProfileActual.conjugateMatter 0
  rw [canonicalCauchySlicePoint_zero_zero]

private theorem profileCurrent_freshActual_gravityConnection_origin_zero :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent 0).gravityConnection 0 = 0 := by
  rw [currentCanonicalGravityPreservingActual_gravityConnection_origin]
  change
    preContorsionSpatialProfileActual.gravityConnection
        (canonicalCauchySlicePoint 0 0) = 0
  rw [canonicalCauchySlicePoint_zero_zero,
    preContorsionSpatialProfileActual_gravityConnection_origin]

private theorem profileCurrent_freshActual_gravityBFAlgebraic_zero
    (direction : LorentzBivectorOneForm) :
    lorentzGravityBFAlgebraicCoefficient
        (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent 0)
        direction 0 = 0 := by
  have curvatureDirectionZero :
      lorentzConnectionAlgebraicCurvatureDirection
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionSpatialProfileCurrent 0)
          direction 0 = 0 := by
    funext internalPair spacetimePair
    unfold lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    rw [profileCurrent_freshActual_gravityConnection_origin_zero]
    simp
  unfold lorentzGravityBFAlgebraicCoefficient
  rw [curvatureDirectionZero]
  simp [gravityBFCurvatureIncrementDensity, gravityCoframePairing,
    coframeTwoFormMetricPairing]

private theorem profileCurrent_freshActual_matterSpin_eq_profile
    (direction : LorentzBivectorOneForm) :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent 0)
        direction 0 =
      lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        preContorsionSpatialProfileActual direction 0 := by
  have spinCoordinatesEq :
      actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionSpatialProfileCurrent 0)
          0 =
        actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          preContorsionSpatialProfileActual 0 := by
    exact actualMatterSpinActionCoordinates_eq_of_origin_fields
      positiveSmoothUnifiedSource
      (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent 0)
      preContorsionSpatialProfileActual
      profileCurrent_freshActual_coframe_origin_eq_profile
      profileCurrent_freshActual_matter_origin_eq_profile
      profileCurrent_freshActual_conjugateMatter_origin_eq_profile
  have spinDualEq :
      einsteinCartanMatterSpinActionDual positiveSmoothUnifiedSource
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionSpatialProfileCurrent 0)
          0 =
        einsteinCartanMatterSpinActionDual positiveSmoothUnifiedSource
          preContorsionSpatialProfileActual 0 := by
    apply einsteinCartanLorentzDual_eq_of_coordinate_eq
    intro formDirection internalPair
    exact congrFun (congrFun spinCoordinatesEq formDirection) internalPair
  exact DFunLike.congr_fun spinDualEq direction

/-- The fresh action graph and the generated profile actual give the same
algebraic Lorentz coefficient at their common contact. -/
theorem preContorsionSpatialProfileCurrent_freshAlgebraicAction_eq_profile
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource
        (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent 0)
        direction 0 =
      lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource preContorsionSpatialProfileActual
        direction 0 := by
  rw [lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    profileCurrent_freshActual_gravityBFAlgebraic_zero,
    preContorsionSpatialProfileActual_gravityBFAlgebraic_zero,
    profileCurrent_freshActual_matterSpin_eq_profile]

/-- All eighteen fresh spatial Lorentz action coordinates vanish at the
canonical profile contact.  This replays the producer equation on the latest
current and is therefore consistency, not an independent constraint. -/
theorem preContorsionSpatialProfileCurrent_rawActionCoordinate_zero
    (spatialDirection : Fin 3)
    (internalPair : Fin 6) :
    currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0
        (canonicalLorentzSpatialBivectorCoordinateDirection
      spatialDirection internalPair) = 0 := by
  change
    lorentzConnectionAlgebraicSpinCurrentCoefficient
          positiveSmoothUnifiedSource
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionSpatialProfileCurrent 0)
          (canonicalLorentzSpatialBivectorOneForm
            (canonicalLorentzSpatialBivectorCoordinateDirection
              spatialDirection internalPair))
          0 -
        currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
          positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0
          (canonicalLorentzSpatialBivectorCoordinateDirection
            spatialDirection internalPair) =
      0
  rw [preContorsionSpatialProfileCurrent_freshAlgebraicAction_eq_profile,
    preContorsionSpatialProfileCurrent_spatialBFMomentumDivergence_eq_profile,
    canonicalSpatialCoordinateDirection_eq_full]
  simpa [lorentzConnectionEulerLagrangeCoefficient] using
    preContorsionSpatialProfileActual_spatialLorentzEuler_origin
      spatialDirection internalPair

theorem preContorsionSpatialProfileCurrent_actionCoordinates_zero :
    currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0 =
      0 := by
  funext spatialDirection internalPair
  exact preContorsionSpatialProfileCurrent_rawActionCoordinate_zero
    spatialDirection internalPair

/-- The finite-dual momentum response vanishes on every spatial test
direction at the canonical contact, not merely on one probe coordinate. -/
theorem preContorsionSpatialProfileCurrent_momentumVelocity_zero :
    currentCanonicalFullActionLorentzSpatialBFMomentumVelocity
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0 =
      0 := by
  funext direction
  change
    lorentzSpatialBivectorLinearExtension
        (currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
          positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0)
        direction = 0
  rw [preContorsionSpatialProfileCurrent_actionCoordinates_zero]
  simp [lorentzSpatialBivectorLinearExtension]

/-- The action-owned BF Legendre section therefore installs no extra
temporal auxiliary jet at this already closed spatial profile contact. -/
theorem preContorsionSpatialProfileCurrent_lorentzAuxiliaryVelocity_zero :
    currentCanonicalFullActionLorentzAuxiliaryVelocity
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0 =
      0 := by
  unfold currentCanonicalFullActionLorentzAuxiliaryVelocity
  rw [preContorsionSpatialProfileCurrent_actionCoordinates_zero]
  funext internalPair spacetimePair
  fin_cases spacetimePair <;>
    simp [lorentzSpatialAuxiliaryVelocityEmbedding]

/-- With zero action-owned auxiliary velocity, the contact actualizer adds no
new temporal `B` jet.  The nonconstant spatial profile itself remains in the
input current and is not erased by this equality. -/
theorem preContorsionSpatialProfileCurrent_localActual_eq_freshActual :
    currentCanonicalFullActionLorentzActualFirstJetLift
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0 =
      currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent 0 := by
  unfold currentCanonicalFullActionLorentzActualFirstJetLift
  rw [preContorsionSpatialProfileCurrent_lorentzAuxiliaryVelocity_zero]
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  funext point internalPair spacetimePair
  simp

/-- C3h200j packages the complete contact response and the genuine
same-contact Lorentz replay.  Its zero response is producer consistency; the
nonzero spatial jet records that the generated profile is not the trivial
constant configuration. -/
structure PositiveP506MatterPreContorsionSpatialProfileCurrentResponseLaw :
    Prop where
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  endpointEleven :
    positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
        canonicalSource_generatedLineage_height_pos = 11
  actionPrepared :
    sourceActionGeneratedJointPrimitiveActionInitialState
        PreContorsionSpatialProfileCurrent =
      PreContorsionSpatialProfileCurrent
  zeroStep :
    currentCanonicalFullActionLorentzStateResponseUpdate
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0 =
      PreContorsionSpatialProfileCurrent
  completeContactResponse :
    StageNineCurrentCanonicalFullActionLorentzContactResponseLaw
      positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0
  nonzeroSpatialProfile : generatedSpatialSkewCoframeJet ≠ 0
  freshProfileMomentum : ∀ direction,
    currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        0 direction =
      lorentzConnectionBFDifferentialMomentumDivergence
        preContorsionSpatialProfileActual
        (canonicalLorentzSpatialBivectorOneForm direction) 0
  freshProfileAlgebraic : ∀ direction,
    lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource
        (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent 0)
        direction 0 =
      lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource preContorsionSpatialProfileActual
        direction 0
  spatialActionCoordinatesZero :
    currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0 = 0
  momentumVelocityZero :
    currentCanonicalFullActionLorentzSpatialBFMomentumVelocity
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0 = 0
  noAddedTemporalAuxiliaryJet :
    currentCanonicalFullActionLorentzAuxiliaryVelocity
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0 = 0
  localActualNoAddedAuxiliaryJet :
    currentCanonicalFullActionLorentzActualFirstJetLift
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent 0 =
      currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent 0

theorem
    positiveP506MatterPreContorsionSpatialProfileCurrentResponse_realizes_C3h200j :
    PositiveP506MatterPreContorsionSpatialProfileCurrentResponseLaw := by
  exact
    { exactP506L0Lineage :=
        positiveSmoothUnifiedSource_generates_exactP506L0Lineage
      endpointEleven := positiveSmoothUnifiedSource_generates_endpoint_eleven
      actionPrepared := preContorsionSpatialProfileCurrent_actionPrepared
      zeroStep := preContorsionSpatialProfileCurrent_zeroStep
      completeContactResponse :=
        preContorsionSpatialProfileCurrent_contactResponse
      nonzeroSpatialProfile := generatedSpatialSkewCoframeJet_nonzero
      freshProfileMomentum :=
        preContorsionSpatialProfileCurrent_spatialBFMomentumDivergence_eq_profile
      freshProfileAlgebraic :=
        preContorsionSpatialProfileCurrent_freshAlgebraicAction_eq_profile
      spatialActionCoordinatesZero :=
        preContorsionSpatialProfileCurrent_actionCoordinates_zero
      momentumVelocityZero :=
        preContorsionSpatialProfileCurrent_momentumVelocity_zero
      noAddedTemporalAuxiliaryJet :=
        preContorsionSpatialProfileCurrent_lorentzAuxiliaryVelocity_zero
      localActualNoAddedAuxiliaryJet :=
        preContorsionSpatialProfileCurrent_localActual_eq_freshActual }

end


end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCurrentResponse
