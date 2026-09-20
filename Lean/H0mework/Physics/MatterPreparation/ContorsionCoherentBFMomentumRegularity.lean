import H0mework.Physics.Lorentz.ChangedBackgroundLorentzOriginCarrierCore
import H0mework.Physics.MatterPreparation.ContorsionSpatialProfileCoherentBFMomentumRegularity
import H0mework.Physics.MatterPreparation.ContorsionCoherentActual

/-!
# S9-C3h200s: final-current coherent Lorentz BF-momentum regularity

C3h200r generated one coherent whole-domain actual from the corrected
`Ufinal` current and its freshly recomputed complete action response.  This
module proves the differentiability bridge needed to evaluate the full
Lorentz connection equation on that same actual:

```text
source/action-generated Ufinal
→ continuous contact-dependent Lorentz auxiliary response
→ exact coherent BF-momentum normal form
→ genuine origin Fréchet derivative
→ all-direction BF divergence on the C3h200r actual
→ full Lorentz EL producer consistency
→ temporal Gauss structural projection.
```

A private smooth zero-slice surrogate is used only to prove continuity of an
algebraic readout.  It is not a source datum, physical endpoint, solution
candidate, residual witness, or branch choice.  The generated C3h200r actual
itself remains the object judged by the final equations.

This checkpoint does not prove `D Gauss(Ufinal)[V(Ufinal)] = 0`, constraint
propagation, or a local flow.  Reaccepting the Lorentz equation that generated
the C3h200n correction is producer consistency; its temporal restriction is
only a structural identity.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentBFMomentumRegularity

open Filter Asymptotics
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineChangedBackgroundLorentzOriginResponseFiber
open StageNineConnectionSectorSourceBalance
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityGaugeActionLocalActualLift
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzActionCauchySplit
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionMomentumRegularity
open StageNinePlebanskiMultiplierVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalFullActionCoherentDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentBFMomentumRegularity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCurrentResponse
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshResponseTangentSimplicity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzTriangularActualLift
open scoped ContDiff Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-! ## Continuous final-current action response -/

/-- A reusable proof-only smooth carrier with the generated profile's primitive
zero-slice fields and the exact normalized-affine connection written by
C3h200n.  It is used solely to expose continuity of the algebraic action
coefficient. -/
def preContorsionFullLorentzZeroSliceRegularityActual :
    StageNineHolonomicConfiguration :=
  { preContorsionSpatialProfileActual with
    gravityConnection :=
      changedBackgroundLorentzOriginConnection
        coherentPreContorsionProfileActual
        preContorsionFullLorentzConnectionCorrection }

/-- The proof-only zero-slice carrier has genuine smooth primitive fields.
This theorem is regularity authority only; it supplies no equation receipt. -/
theorem
    preContorsionFullLorentzZeroSliceRegularityActual_smooth :
    preContorsionFullLorentzZeroSliceRegularityActual.Smooth := by
  have smooth := preContorsionSpatialProfileActual_smooth
  exact
    ⟨smooth.1,
      changedBackgroundLorentzOriginConnection_smooth
        coherentPreContorsionProfileActual
        preContorsionFullLorentzConnectionCorrection,
      smooth.2.2.1,
      smooth.2.2.2.1,
      smooth.2.2.2.2.1,
      smooth.2.2.2.2.2.1,
      smooth.2.2.2.2.2.2.1,
      smooth.2.2.2.2.2.2.2.1,
      smooth.2.2.2.2.2.2.2.2⟩

/-- The proof-only zero-slice carrier retains the generated nondegenerate
profile coframe. -/
theorem
    preContorsionFullLorentzZeroSliceRegularityActual_nondegenerate :
    preContorsionFullLorentzZeroSliceRegularityActual.Nondegenerate := by
  exact preContorsionSpatialProfileActual_nondegenerate

private theorem
    finalCurrent_freshActual_coframe_origin_eq_regularSlice
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent space).coframe 0 =
      preContorsionFullLorentzZeroSliceRegularityActual.coframe
        (canonicalCauchySlicePoint 0 space) := by
  rw [currentCanonicalGravityPreservingActual_coframe_origin_eq_currentSlice,
    congrFun preContorsionFullLorentzTriangularCurrent_coframe_eq_profile
      space]
  rfl

private theorem
    finalCurrent_freshActual_gravityAuxiliary_origin_eq_regularSlice
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent space).gravityAuxiliary 0 =
      preContorsionFullLorentzZeroSliceRegularityActual.gravityAuxiliary
        (canonicalCauchySlicePoint 0 space) := by
  rw [currentCanonicalGravityPreservingActual_gravityAuxiliary_point]
  unfold actionGeneratedGravityAuxiliary
  rw [congrFun
    preContorsionFullLorentzTriangularCurrent_coframe_eq_profile space]
  change
    physicalIIPlusBivector
        (preContorsionSpatialProfileActual.coframe
          (canonicalCauchySlicePoint 0 space)) =
      preContorsionSpatialProfileActual.gravityAuxiliary
        (canonicalCauchySlicePoint 0 space)
  rw [preContorsionSpatialProfileActual_gravityAuxiliary_generated]

private theorem
    finalCurrent_freshActual_gravityConnection_origin_eq_regularSlice
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent space).gravityConnection 0 =
      preContorsionFullLorentzZeroSliceRegularityActual.gravityConnection
        (canonicalCauchySlicePoint 0 space) := by
  rw [currentCanonicalGravityPreservingActual_gravityConnection_origin]
  rfl

private theorem
    finalCurrent_freshActual_matter_origin_eq_regularSlice
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent space).matter 0 =
      preContorsionFullLorentzZeroSliceRegularityActual.matter
        (canonicalCauchySlicePoint 0 space) := by
  rw [currentCanonicalGravityPreservingActual_matter_origin_eq_currentSlice]
  change
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.matter
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.matter
        (canonicalCauchySlicePoint 0 space)
  rw [
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual,
    changedBackgroundLorentzOriginCarrier_matter]
  change
    (currentCanonicalFullActionLorentzCoherentDiagonalActual
      positiveSmoothUnifiedSource
      PreContorsionSpatialProfileCurrent).matter
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.matter
        (canonicalCauchySlicePoint 0 space)
  rw [coherentDiagonalActual_matter_slice,
    preContorsionSpatialProfileCurrent_zeroStep]
  rfl

private theorem
    finalCurrent_freshActual_conjugateMatter_origin_eq_regularSlice
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent space).conjugateMatter 0 =
      preContorsionFullLorentzZeroSliceRegularityActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) := by
  rw [
    currentCanonicalGravityPreservingActual_conjugateMatter_origin_eq_currentSlice]
  change
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space)
  rw [
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual,
    changedBackgroundLorentzOriginCarrier_conjugateMatter]
  change
    (currentCanonicalFullActionLorentzCoherentDiagonalActual
      positiveSmoothUnifiedSource
      PreContorsionSpatialProfileCurrent).conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space)
  rw [coherentDiagonalActual_conjugateMatter_slice,
    preContorsionSpatialProfileCurrent_zeroStep]
  rfl

private theorem finalCurrent_freshActual_gravityBF_eq_regularSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzBivectorOneForm) :
    lorentzGravityBFAlgebraicCoefficient
        (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent space)
        direction 0 =
      lorentzGravityBFAlgebraicCoefficient
        preContorsionFullLorentzZeroSliceRegularityActual direction
        (canonicalCauchySlicePoint 0 space) := by
  have curvatureDirectionEq :
      lorentzConnectionAlgebraicCurvatureDirection
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionFullLorentzTriangularCurrent space)
          direction 0 =
        lorentzConnectionAlgebraicCurvatureDirection
          preContorsionFullLorentzZeroSliceRegularityActual direction
          (canonicalCauchySlicePoint 0 space) := by
    funext internalPair spacetimePair
    unfold lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    rw [finalCurrent_freshActual_gravityConnection_origin_eq_regularSlice]
  unfold lorentzGravityBFAlgebraicCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [finalCurrent_freshActual_coframe_origin_eq_regularSlice,
    finalCurrent_freshActual_gravityAuxiliary_origin_eq_regularSlice,
    curvatureDirectionEq]

private theorem finalCurrent_freshActual_matterSpin_eq_regularSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzBivectorOneForm) :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent space)
        direction 0 =
      lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        preContorsionFullLorentzZeroSliceRegularityActual direction
        (canonicalCauchySlicePoint 0 space) := by
  have spinCoordinatesEq :
      actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionFullLorentzTriangularCurrent space)
          0 =
        actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          preContorsionFullLorentzZeroSliceRegularityActual
          (canonicalCauchySlicePoint 0 space) := by
    exact actualMatterSpinActionCoordinates_eq_of_fields_at
      positiveSmoothUnifiedSource
      (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent space)
      preContorsionFullLorentzZeroSliceRegularityActual 0
      (canonicalCauchySlicePoint 0 space)
      (finalCurrent_freshActual_coframe_origin_eq_regularSlice space)
      (finalCurrent_freshActual_matter_origin_eq_regularSlice space)
      (finalCurrent_freshActual_conjugateMatter_origin_eq_regularSlice space)
  have spinDualEq :
      einsteinCartanMatterSpinActionDual positiveSmoothUnifiedSource
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionFullLorentzTriangularCurrent space)
          0 =
        einsteinCartanMatterSpinActionDual positiveSmoothUnifiedSource
          preContorsionFullLorentzZeroSliceRegularityActual
          (canonicalCauchySlicePoint 0 space) := by
    apply einsteinCartanLorentzDual_eq_of_coordinate_eq
    intro formDirection internalPair
    exact congrFun (congrFun spinCoordinatesEq formDirection) internalPair
  exact DFunLike.congr_fun spinDualEq direction

private theorem
    preContorsionFullLorentzTriangularCurrent_freshAlgebraicAction_eq_regularSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource
        (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent space)
        direction 0 =
      lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource
        preContorsionFullLorentzZeroSliceRegularityActual direction
        (canonicalCauchySlicePoint 0 space) := by
  rw [lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    finalCurrent_freshActual_gravityBF_eq_regularSlice,
    finalCurrent_freshActual_matterSpin_eq_regularSlice]

theorem
    preContorsionFullLorentzTriangularCurrent_rawActionReadout_eq_regularSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent space direction =
      lorentzConnectionAlgebraicSpinCurrentCoefficient
          positiveSmoothUnifiedSource
          preContorsionFullLorentzZeroSliceRegularityActual
          (canonicalLorentzSpatialBivectorOneForm direction)
          (canonicalCauchySlicePoint 0 space) -
        StageNineLorentzActionCanonicalPairUpdate.lorentzConnectionSpatialBFMomentumDivergence
          preContorsionSpatialProfileActual
          (canonicalLorentzSpatialBivectorOneForm direction)
          (canonicalCauchySlicePoint 0 space) := by
  change
    lorentzConnectionAlgebraicSpinCurrentCoefficient
          positiveSmoothUnifiedSource
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionFullLorentzTriangularCurrent space)
          (canonicalLorentzSpatialBivectorOneForm direction) 0 -
        currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent space direction = _
  rw [
    preContorsionFullLorentzTriangularCurrent_freshAlgebraicAction_eq_regularSlice,
    preContorsionFullLorentzTriangularCurrent_spatialBFMomentumDivergence_eq_profileCurrent,
    preContorsionSpatialProfileCurrent_spatialBFMomentumDivergence_eq_profileSlice]

private theorem
    preContorsionFullLorentzTriangularCurrent_rawActionReadout_continuous
    (direction : LorentzSpatialBivectorDirection) :
    Continuous fun space =>
      currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent space direction := by
  rw [show (fun space =>
      currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent space direction) =
    fun space =>
      lorentzConnectionAlgebraicSpinCurrentCoefficient
          positiveSmoothUnifiedSource
          preContorsionFullLorentzZeroSliceRegularityActual
          (canonicalLorentzSpatialBivectorOneForm direction)
          (canonicalCauchySlicePoint 0 space) -
        StageNineLorentzActionCanonicalPairUpdate.lorentzConnectionSpatialBFMomentumDivergence
          preContorsionSpatialProfileActual
          (canonicalLorentzSpatialBivectorOneForm direction)
          (canonicalCauchySlicePoint 0 space) by
    funext space
    exact
      preContorsionFullLorentzTriangularCurrent_rawActionReadout_eq_regularSlice
        space direction]
  have sliceContinuous : Continuous (canonicalCauchySlicePoint 0) := by
    rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
      funext space
      rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
      simp]
    exact canonicalSpatialInclusion.continuous
  exact
    (lorentzConnectionAlgebraicSpinCurrentCoefficient_continuous
      positiveSmoothUnifiedSource
      preContorsionFullLorentzZeroSliceRegularityActual
      preContorsionFullLorentzZeroSliceRegularityActual_smooth
      preContorsionFullLorentzZeroSliceRegularityActual_nondegenerate
      (canonicalLorentzSpatialBivectorOneForm direction)).comp
        sliceContinuous |>.sub
      ((preContorsionSpatialProfileActual_spatialBFMomentumDivergence_continuous
        (canonicalLorentzSpatialBivectorOneForm direction)).comp
          sliceContinuous)

/-- The complete 18-coordinate Lorentz action response of `Ufinal` varies
continuously with the contact.  No zero-response receipt is assumed. -/
theorem
    preContorsionFullLorentzTriangularCurrent_actionCoordinates_continuous :
    Continuous
      (currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent) := by
  apply continuous_pi
  intro spatialDirection
  apply continuous_pi
  intro internalPair
  exact
    preContorsionFullLorentzTriangularCurrent_rawActionReadout_continuous
      (canonicalLorentzSpatialBivectorCoordinateDirection
        spatialDirection internalPair)

/-- The action-owned Lorentz auxiliary velocity installed by the coherent
actualizer is continuous across contacts. -/
theorem
    preContorsionFullLorentzTriangularCurrent_auxiliaryVelocity_continuous :
    Continuous
      (currentCanonicalFullActionLorentzAuxiliaryVelocity
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent) := by
  have coordinatesContinuous :=
    preContorsionFullLorentzTriangularCurrent_actionCoordinates_continuous
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  fin_cases spacetimePair <;>
    simp [currentCanonicalFullActionLorentzAuxiliaryVelocity,
      lorentzSpatialAuxiliaryVelocityEmbedding] <;>
    fun_prop

/-! ## Coherent BF-momentum normal form and differentiability -/

/-- The C3h200r actual's coframe is the generated profile pulled back to the
canonical zero slice. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_coframe_normalForm
    (point : BasePoint) :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe
        point =
      preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point) := by
  rw [canonicalZeroSliceProjection_apply]
  change
    (currentCanonicalFullActionLorentzActualFirstJetLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      (canonicalSpatialProjection point)).coframe
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) = _
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      (canonicalSpatialProjection point)).coframe
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) = _
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe,
    congrFun preContorsionFullLorentzTriangularCurrent_coframe_eq_profile
      (canonicalSpatialProjection point)]
  rfl

/-- The only extra gravity-auxiliary term is canonical time multiplied by
the contact-dependent action response generated from `Ufinal`. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_gravityAuxiliary_normalForm
    (point : BasePoint) :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gravityAuxiliary
        point =
      preContorsionSpatialProfileActual.gravityAuxiliary
          (canonicalZeroSliceProjection point) +
        canonicalTimeProjection point •
          currentCanonicalFullActionLorentzAuxiliaryVelocity
            positiveSmoothUnifiedSource
            PreContorsionFullLorentzTriangularCurrent
            (canonicalSpatialProjection point) := by
  rw [canonicalZeroSliceProjection_apply]
  change
    (currentCanonicalFullActionLorentzActualFirstJetLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      (canonicalSpatialProjection point)).gravityAuxiliary
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) = _
  unfold currentCanonicalFullActionLorentzActualFirstJetLift
  rw [currentCanonicalGravityPreservingActual_gravityAuxiliary]
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      (canonicalSpatialProjection point)).gravityAuxiliary
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) +
      localBaseCoordinate canonicalLorentzianTimeDirection
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) •
        currentCanonicalFullActionLorentzAuxiliaryVelocity
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent
          (canonicalSpatialProjection point) = _
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_auxiliary]
  unfold actionGeneratedGravityAuxiliary
  rw [congrFun
    preContorsionFullLorentzTriangularCurrent_coframe_eq_profile
      (canonicalSpatialProjection point)]
  change
    physicalIIPlusBivector
        (preContorsionSpatialProfileActual.coframe
          (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))) +
        _ =
      preContorsionSpatialProfileActual.gravityAuxiliary
          (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)) +
        _
  rw [preContorsionSpatialProfileActual_gravityAuxiliary_generated]
  simp [localBaseCoordinate_apply]

/-- Coefficient of the generated time-dependent correction to one Lorentz
BF-momentum field. -/
def coherentFullLorentzBFMomentumCorrectionCoefficient
    (direction : PhysicalBivector) (point : BasePoint) : ℝ :=
  generatedVolumeDensity
      (toContinuumPointField preContorsionSpatialProfileActual
        (canonicalZeroSliceProjection point)) *
    gravityAuxiliaryHodgePairingPolynomial
      (preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point))
      (currentCanonicalFullActionLorentzAuxiliaryVelocity
        positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
        (canonicalSpatialProjection point))
      direction

theorem coherentFullLorentzBFMomentumCorrectionCoefficient_continuous
    (direction : PhysicalBivector) :
    Continuous
      (coherentFullLorentzBFMomentumCorrectionCoefficient direction) := by
  have zeroSliceContinuous := canonicalZeroSliceProjection.continuous
  have coframeContinuous : Continuous fun point =>
      preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point) :=
    (holonomicCoframe_continuous preContorsionSpatialProfileActual
      preContorsionSpatialProfileActual_smooth).comp zeroSliceContinuous
  have velocityContinuous : Continuous fun point =>
      currentCanonicalFullActionLorentzAuxiliaryVelocity
        positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
        (canonicalSpatialProjection point) :=
    preContorsionFullLorentzTriangularCurrent_auxiliaryVelocity_continuous.comp
      canonicalSpatialProjection.continuous
  have velocityTransformContinuous : Continuous fun point =>
      fun internalPair =>
        coframeTwoFormLinear
          (preContorsionSpatialProfileActual.coframe
            (canonicalZeroSliceProjection point))
          (currentCanonicalFullActionLorentzAuxiliaryVelocity
            positiveSmoothUnifiedSource
            PreContorsionFullLorentzTriangularCurrent
            (canonicalSpatialProjection point) internalPair) := by
    apply continuous_pi
    intro internalPair
    exact coframeTwoFormLinear_apply_continuous
      (fun point => preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point)) coframeContinuous
      (fun point =>
        currentCanonicalFullActionLorentzAuxiliaryVelocity
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent
          (canonicalSpatialProjection point) internalPair)
      ((continuous_apply internalPair).comp velocityContinuous)
  have directionTransformContinuous : Continuous fun point =>
      fun internalPair =>
        coframeTwoFormLinear
          (preContorsionSpatialProfileActual.coframe
            (canonicalZeroSliceProjection point))
          (direction internalPair) := by
    apply continuous_pi
    intro internalPair
    exact coframeTwoFormLinear_apply_continuous
      (fun point => preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point)) coframeContinuous
      (fun _ => direction internalPair) continuous_const
  have hodgeDirectionTransformContinuous : Continuous fun point =>
      fun internalPair =>
        lorentzianCoframeHodge
          (coframeTwoFormLinear
            (preContorsionSpatialProfileActual.coframe
              (canonicalZeroSliceProjection point))
            (direction internalPair)) := by
    apply continuous_pi
    intro internalPair
    exact lorentzianCoframeHodge_apply_continuous
      (fun point =>
        coframeTwoFormLinear
          (preContorsionSpatialProfileActual.coframe
            (canonicalZeroSliceProjection point))
          (direction internalPair))
      ((continuous_apply internalPair).comp directionTransformContinuous)
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity
        (toContinuumPointField preContorsionSpatialProfileActual
          (canonicalZeroSliceProjection point)) :=
    (holonomicGeneratedVolumeDensity_contDiff
      preContorsionSpatialProfileActual
      preContorsionSpatialProfileActual_smooth
      preContorsionSpatialProfileActual_nondegenerate).continuous.comp
        zeroSliceContinuous
  unfold coherentFullLorentzBFMomentumCorrectionCoefficient
    gravityAuxiliaryHodgePairingPolynomial
  apply volumeContinuous.mul
  apply continuous_finsetSum
  intro internalPair _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro spacetimePair _
  exact (continuous_const.mul
      ((continuous_apply spacetimePair).comp
        ((continuous_apply internalPair).comp
          velocityTransformContinuous))).mul
    ((continuous_apply spacetimePair).comp
      ((continuous_apply internalPair).comp
        hodgeDirectionTransformContinuous))

@[simp] theorem coherentFullLorentzBFMomentumCorrectionCoefficient_origin
    (direction : PhysicalBivector) :
    coherentFullLorentzBFMomentumCorrectionCoefficient direction 0 = 0 := by
  unfold coherentFullLorentzBFMomentumCorrectionCoefficient
  rw [canonicalZeroSliceProjection.map_zero,
    canonicalSpatialProjection.map_zero,
    preContorsionFullLorentzTriangularCurrent_lorentzAuxiliaryVelocity_zero]
  simp [gravityAuxiliaryHodgePairingPolynomial]

/-- Exact BF-momentum normal form on the generated C3h200r actual. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_BFMomentum_normalForm
    (direction : PhysicalBivector) (point : BasePoint) :
    lorentzConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction point =
      lorentzConnectionBFDifferentialMomentum
          preContorsionSpatialProfileActual direction
          (canonicalZeroSliceProjection point) +
        canonicalTimeProjection point *
          coherentFullLorentzBFMomentumCorrectionCoefficient direction
            point := by
  unfold lorentzConnectionBFDifferentialMomentum
    coherentFullLorentzBFMomentumCorrectionCoefficient
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_coframe_normalForm,
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_gravityAuxiliary_normalForm,
    gravityAuxiliaryHodgePairingPolynomial_add_smul_left
      (preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point))
      (preContorsionSpatialProfileActual_nondegenerate
        (canonicalZeroSliceProjection point))]
  ring

private theorem hasFDerivAt_mul_zero_of_first_zero_second_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {first second : E → ℝ} {firstDerivative : E →L[ℝ] ℝ}
    (firstHasDerivative : HasFDerivAt first firstDerivative 0)
    (firstZero : first 0 = 0)
    (secondContinuous : ContinuousAt second 0)
    (secondZero : second 0 = 0) :
    HasFDerivAt (fun point => first point * second point)
      (0 : E →L[ℝ] ℝ) 0 := by
  have firstOrder : first =O[𝓝 0] fun point : E => ‖point‖ := by
    have firstOrderVector : first =O[𝓝 0] fun point : E => point := by
      simpa [firstZero] using firstHasDerivative.isBigO_sub
    exact firstOrderVector.norm_right
  have secondLittle : second =o[𝓝 0] fun _ : E => (1 : ℝ) := by
    rw [isLittleO_one_iff]
    simpa only [secondZero] using secondContinuous.tendsto
  have productLittle :
      (fun point => first point * second point) =o[𝓝 0]
        fun point : E => ‖point‖ * (1 : ℝ) :=
    firstOrder.mul_isLittleO secondLittle
  have productLittleNorm :
      (fun point => first point * second point) =o[𝓝 0]
        fun point : E => ‖point‖ := by
    simpa only [mul_one] using productLittle
  have productLittleVector :
      (fun point => first point * second point) =o[𝓝 0]
        fun point : E => point :=
    productLittleNorm.of_norm_right
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only [zero_add, firstZero, secondZero, mul_zero, zero_apply,
    sub_zero] using productLittleVector

/-- The C3h200r BF momentum has a genuine Fréchet derivative at the common
origin.  Its derivative is the same zero-slice pullback derivative already
computed from the generated profile. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_BFMomentum_hasFDerivAt_origin
    (direction : PhysicalBivector) :
    HasFDerivAt
      (lorentzConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction)
      ((fderiv ℝ
        (lorentzConnectionBFDifferentialMomentum
          preContorsionSpatialProfileActual direction) 0).comp
        canonicalZeroSliceProjection)
      0 := by
  rw [show
    lorentzConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction =
      fun point =>
        lorentzConnectionBFDifferentialMomentum
            positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
            direction point +
          canonicalTimeProjection point *
            (coherentFullLorentzBFMomentumCorrectionCoefficient direction
                point -
              coherentProfileBFMomentumCorrectionCoefficient direction
                point) by
    funext point
    rw [
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_BFMomentum_normalForm,
      coherentProfileActual_BFMomentum_normalForm]
    ring]
  have differenceContinuous :
      ContinuousAt
        (fun point =>
          coherentFullLorentzBFMomentumCorrectionCoefficient direction point -
            coherentProfileBFMomentumCorrectionCoefficient direction point)
        0 :=
    ((coherentFullLorentzBFMomentumCorrectionCoefficient_continuous
      direction).sub
      (coherentProfileBFMomentumCorrectionCoefficient_continuous
        direction)).continuousAt
  have differenceZero :
      coherentFullLorentzBFMomentumCorrectionCoefficient direction 0 -
          coherentProfileBFMomentumCorrectionCoefficient direction 0 =
        0 := by
    rw [coherentFullLorentzBFMomentumCorrectionCoefficient_origin,
      coherentProfileBFMomentumCorrectionCoefficient_origin]
    ring
  have correctionDerivative :=
    hasFDerivAt_mul_zero_of_first_zero_second_continuous
      canonicalTimeProjection.hasFDerivAt
      canonicalTimeProjection.map_zero differenceContinuous differenceZero
  have combinedDerivative :=
    (coherentProfileActual_BFMomentum_hasFDerivAt_origin direction).add
      correctionDerivative
  have combinedDerivative' :
      HasFDerivAt
        ((lorentzConnectionBFDifferentialMomentum
            positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
            direction) +
          fun point =>
            canonicalTimeProjection point *
              (coherentFullLorentzBFMomentumCorrectionCoefficient direction
                  point -
                coherentProfileBFMomentumCorrectionCoefficient direction
                  point))
        ((fderiv ℝ
          (lorentzConnectionBFDifferentialMomentum
            preContorsionSpatialProfileActual direction) 0).comp
          canonicalZeroSliceProjection)
        0 := by
    simpa only [add_zero] using combinedDerivative
  apply combinedDerivative'.congr_of_eventuallyEq
  filter_upwards with point
  rfl

/-- The complete origin differential agrees with the older generated
profile-coherent actual.  This is a derivative transporter, not an equality
of the two actuals. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_BFMomentum_fderiv_eq_profileCoherent
    (direction : PhysicalBivector) :
    fderiv ℝ
        (lorentzConnectionBFDifferentialMomentum
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          direction)
        0 =
      fderiv ℝ
        (lorentzConnectionBFDifferentialMomentum
          positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
          direction)
        0 := by
  rw [
    (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_BFMomentum_hasFDerivAt_origin
      direction).fderiv,
    (coherentProfileActual_BFMomentum_hasFDerivAt_origin direction).fderiv]

/-! ## Full divergence and Lorentz base acceptance -/

/-- All four derivative directions of the C3h200r BF momentum reproduce the
C3h200n final actual's full divergence. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_fullBFMomentumDivergence_eq_finalActual
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionBFDifferentialMomentumDivergence
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction 0 =
      lorentzConnectionBFDifferentialMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        direction 0 := by
  calc
    lorentzConnectionBFDifferentialMomentumDivergence
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction 0 =
      lorentzConnectionBFDifferentialMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction 0 := by
      unfold lorentzConnectionBFDifferentialMomentumDivergence
      apply Finset.sum_congr rfl
      intro derivativeDirection _
      unfold fieldDirectionalDerivative
      rw [
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_BFMomentum_fderiv_eq_profileCoherent
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction)]
    _ = lorentzConnectionBFDifferentialMomentumDivergence
        preContorsionSpatialProfileActual direction 0 :=
      coherentProfileActual_fullBFMomentumDivergence_eq_profile direction
    _ = lorentzCoordinatePairing preContorsionFullLorentzProfileDivergence
        direction :=
      preContorsionSpatialProfileActual_fullDivergence_eq_pairing direction
    _ = lorentzConnectionBFDifferentialMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        direction 0 :=
      (fullLorentzTriangularActual_fullDivergence_eq_pairing direction).symm

/-- The algebraic Lorentz coefficient is local in the primitive origin
fields and therefore agrees with the C3h200n final actual on the generated
zero slice. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_algebraicAction_eq_finalActual
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction 0 =
      lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        direction 0 := by
  have fidelity :=
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_initialSliceFidelity
      0
  rw [canonicalCauchySlicePoint_zero_zero] at fidelity
  rcases fidelity with
    ⟨coframeEq, connectionEq, auxiliaryEq, _multiplierEq,
      _gaugeConnectionEq, _gaugeAuxiliaryEq, _scalarEq, matterEq,
      conjugateMatterEq⟩
  have gravityBFEq :
      lorentzGravityBFAlgebraicCoefficient
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          direction 0 =
        lorentzGravityBFAlgebraicCoefficient
          positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
          direction 0 := by
    have curvatureDirectionEq :
        lorentzConnectionAlgebraicCurvatureDirection
            positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
            direction 0 =
          lorentzConnectionAlgebraicCurvatureDirection
            positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
            direction 0 := by
      funext internalPair spacetimePair
      unfold lorentzConnectionAlgebraicCurvatureDirection
        lorentzConnectionAlgebraicCurvatureVariation
      rw [connectionEq]
    unfold lorentzGravityBFAlgebraicCoefficient generatedVolumeDensity
    simp only [toContinuumPointField]
    rw [coframeEq, auxiliaryEq, curvatureDirectionEq]
  have matterSpinEq :
      lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          direction 0 =
        lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
          positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
          direction 0 := by
    have spinCoordinatesEq :
        actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
            positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
            0 =
          actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
            positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
            0 := by
      exact actualMatterSpinActionCoordinates_eq_of_origin_fields
        positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        coframeEq matterEq conjugateMatterEq
    have spinDualEq :
        einsteinCartanMatterSpinActionDual positiveSmoothUnifiedSource
            positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
            0 =
          einsteinCartanMatterSpinActionDual positiveSmoothUnifiedSource
            positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
            0 := by
      apply einsteinCartanLorentzDual_eq_of_coordinate_eq
      intro formDirection internalPair
      exact congrFun (congrFun spinCoordinatesEq formDirection) internalPair
    exact DFunLike.congr_fun spinDualEq direction
  rw [lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    gravityBFEq, matterSpinEq]

/-- The full Lorentz equation on the coherent C3h200r actual is the
same-action producer consistency of the C3h200n connection write. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_lorentzEulerLagrange_origin_producerConsistency
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction 0 = 0 := by
  rw [lorentzConnectionEulerLagrangeCoefficient,
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_algebraicAction_eq_finalActual,
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_fullBFMomentumDivergence_eq_finalActual]
  simpa [lorentzConnectionEulerLagrangeCoefficient] using
    fullLorentzTriangularActual_eulerLagrange_origin direction

/-- Temporal Lorentz Gauss is only the structural temporal projection of the
full producer-consistency equation above. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_temporalGauss_origin_structuralProjection :
    CanonicalLorentzTemporalGaussConstraintAt positiveSmoothUnifiedSource
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual 0 := by
  intro component
  simpa [lorentzTemporalGaussResidual] using
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_lorentzEulerLagrange_origin_producerConsistency
      (canonicalLorentzTemporalBivectorOneForm component)

/-! ## C3h200s checkpoint law -/

structure
    PositiveP506MatterPreContorsionFullLorentzFreshCoherentBFMomentumRegularityLaw :
    Prop where
  coherentActualProducer :
    PositiveP506MatterPreContorsionFullLorentzFreshCoherentActualLaw
  actionCoordinatesContinuous :
    Continuous
      (currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent)
  auxiliaryVelocityContinuous :
    Continuous
      (currentCanonicalFullActionLorentzAuxiliaryVelocity
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent)
  bfMomentumDifferentiable : ∀ direction,
    HasFDerivAt
      (lorentzConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction)
      ((fderiv ℝ
        (lorentzConnectionBFDifferentialMomentum
          preContorsionSpatialProfileActual direction) 0).comp
        canonicalZeroSliceProjection)
      0
  fullDivergenceTransport : ∀ direction,
    lorentzConnectionBFDifferentialMomentumDivergence
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction 0 =
      lorentzConnectionBFDifferentialMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        direction 0
  fullLorentzProducerConsistency : ∀ direction,
    lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction 0 = 0
  temporalGaussStructuralProjection :
    CanonicalLorentzTemporalGaussConstraintAt positiveSmoothUnifiedSource
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual 0

theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentBFMomentumRegularity_realizes_C3h200s :
    PositiveP506MatterPreContorsionFullLorentzFreshCoherentBFMomentumRegularityLaw := by
  exact
    { coherentActualProducer :=
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_realizes_C3h200r
      actionCoordinatesContinuous :=
        preContorsionFullLorentzTriangularCurrent_actionCoordinates_continuous
      auxiliaryVelocityContinuous :=
        preContorsionFullLorentzTriangularCurrent_auxiliaryVelocity_continuous
      bfMomentumDifferentiable :=
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_BFMomentum_hasFDerivAt_origin
      fullDivergenceTransport :=
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_fullBFMomentumDivergence_eq_finalActual
      fullLorentzProducerConsistency :=
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_lorentzEulerLagrange_origin_producerConsistency
      temporalGaussStructuralProjection :=
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_temporalGauss_origin_structuralProjection }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentBFMomentumRegularity
