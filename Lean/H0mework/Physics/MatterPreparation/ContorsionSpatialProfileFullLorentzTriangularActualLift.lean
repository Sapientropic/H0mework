import H0mework.Physics.Lorentz.ChangedBackgroundLorentzOriginCarrierCore
import H0mework.Physics.Dirac.P506MatterSpinCoordinateNormalForm
import H0mework.Physics.MatterPreparation.ContorsionSpatialProfileCoherentBFMomentumRegularity

/-!
# S9-C3h200n: full Lorentz triangular actual lift

The exact P506/L0 source and the actual action first generate a full
24-coordinate Lorentz covector `S`.  The already generated spatial coframe
profile supplies its complete actual BF-divergence output `D`, including the
six temporal coordinates that were not inputs to the spatial inverse.  The
remaining action complement

`C = S - D`

is then sent through the fixed Einstein--Cartan action inverse and installed
as the origin value of a normalized affine Lorentz-connection germ.  This is
the triangular action-native write

`source/action -> S -> generated profile -> D -> C -> fixed Cartan write -> U*`.

Neither a residual value, a zero-fiber witness, a branch choice, an endpoint
certificate, nor a tunable coefficient is accepted by any constructor.  The
final all-direction Euler--Lagrange equality is checked only after the actual
has been generated.  It is producer soundness for this Lorentz update, not an
independent constraint, a flow, or full joint stationarity.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzTriangularActualLift

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineChangedBackgroundLorentzOriginResponseFiber
open StageNineConnectionSectorSourceBalance
open StageNineEinsteinCartanSkewCoframeActualResponseOperator
open StageNineEinsteinCartanSpatialSkewCoframeActualResponseOperator
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzActionCauchySplit
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentBFMomentumRegularity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceGeneratedEinsteinCartanSkewCoframeLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 0 = 0 := by
  rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
  simp

abbrev coherentPreContorsionProfileActual :
    StageNineHolonomicConfiguration :=
  positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual

/-! ## Action-first triangular data -/

/-- Complete 24-coordinate Lorentz action covector generated on the actual
pre-contorsion P286 mouth.  This is a direct action readout, not a table or a
residual supplied to the constructor. -/
def preContorsionFullLorentzActionCovector : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    lorentzConnectionAlgebraicSpinCurrentCoefficient
      positiveSmoothUnifiedSource PreContorsionP286Actual
      (lorentzBivectorOneFormCoordinateDirection
        formDirection internalPair) 0

/-- Complete 24-coordinate divergence produced by the already generated
spatial profile.  Its temporal row is an output of that profile. -/
def preContorsionFullLorentzProfileDivergence : LorentzBivectorOneForm :=
  spatialSkewCoframeActualOnFullBFDivergenceCoordinates
    PreContorsionP286Actual generatedSpatialSkewCoframeJet

/-- The one action complement not already carried by the generated coframe
profile. -/
def preContorsionFullLorentzActionComplement : LorentzBivectorOneForm :=
  preContorsionFullLorentzActionCovector -
    preContorsionFullLorentzProfileDivergence

/-- Fixed action-normalized Cartan image of the complement.  All numerical
normalization is inherited from the already verified gravity action inverse. -/
def preContorsionFullLorentzConnectionCorrection :
    LorentzBivectorOneForm :=
  einsteinCartanSpinContorsionCoordinates
    preContorsionFullLorentzActionComplement

/-- The source/action-generated complete Lorentz actual.  The normalized
affine lift preserves the background curvature at the common contact while
writing the uniquely generated connection value. -/
def positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual :
    StageNineHolonomicConfiguration :=
  changedBackgroundLorentzOriginCarrier coherentPreContorsionProfileActual
    preContorsionFullLorentzConnectionCorrection

/-! ## Exact source/action coordinates -/

theorem preContorsionFullLorentzActionCovector_spatial
    (spatial : Fin 3) (internalPair : Fin 6) :
    preContorsionFullLorentzActionCovector spatial.succ internalPair =
      preContorsionSpatialLorentzActionTarget spatial internalPair :=
  rfl

/-- The full action covector is the actual representation-generated matter
spin covector because the pre-contorsion gravity algebraic leg is zero. -/
theorem preContorsionFullLorentzActionCovector_eq_matterSpin :
    preContorsionFullLorentzActionCovector =
      lorentzMatterSpinCoordinates positiveSmoothUnifiedSource
        PreContorsionP286Actual 0 := by
  funext formDirection internalPair
  unfold preContorsionFullLorentzActionCovector
    lorentzMatterSpinCoordinates
  rw [lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    preContorsionP286Actual_gravityBFAlgebraic_zero]
  ring

/-- Representation restriction and the actual Dirac action determine the
full covector; the displayed normal form is a downstream readout. -/
theorem preContorsionFullLorentzActionCovector_eq_normalForm :
    preContorsionFullLorentzActionCovector =
      positiveMatterSpinCoordinatesNormalForm := by
  rw [preContorsionFullLorentzActionCovector_eq_matterSpin]
  exact positiveMatterSpinCoordinates_eq_normalForm_of_origin
    PreContorsionP286Actual
    (preContorsionP286Actual_coframe_one 0)
    preContorsionP286Actual_matter_origin
    preContorsionP286Actual_conjugateMatter_origin

theorem preContorsionSpatialLorentzActionTarget_one_zero :
    preContorsionSpatialLorentzActionTarget 1 0 = -(1 / 2 : ℝ) := by
  have coordinate := congrFun
    (congrFun preContorsionFullLorentzActionCovector_eq_normalForm 2) 0
  change preContorsionSpatialLorentzActionTarget 1 0 = _ at coordinate
  simpa [positiveMatterSpinCoordinatesNormalForm] using coordinate

theorem preContorsionFullLorentzProfileDivergence_temporal_five :
    preContorsionFullLorentzProfileDivergence 0 5 = -1 := by
  have prediction := congrFun
    preContorsionSpatialProfileActual_temporalPrediction 5
  change preContorsionFullLorentzProfileDivergence 0 5 = _ at prediction
  rw [prediction]
  simp [spatialSkewCoframeTemporalBFDivergencePrediction,
    preContorsionSpatialLorentzActionTarget_one_zero,
    preContorsionSpatialLorentzActionTarget_zero_one]
  norm_num

theorem preContorsionFullLorentzActionCovector_temporal_five :
    preContorsionFullLorentzActionCovector 0 5 = -(1 / 2 : ℝ) := by
  have coordinate := congrFun
    (congrFun preContorsionFullLorentzActionCovector_eq_normalForm 0) 5
  simpa [positiveMatterSpinCoordinatesNormalForm] using coordinate

/-! ## Triangular complement and fixed Cartan inverse -/

theorem preContorsionFullLorentzActionComplement_spatial_zero
    (spatial : Fin 3) (internalPair : Fin 6) :
    preContorsionFullLorentzActionComplement spatial.succ internalPair = 0 := by
  unfold preContorsionFullLorentzActionComplement
  change
    preContorsionFullLorentzActionCovector spatial.succ internalPair -
        preContorsionFullLorentzProfileDivergence spatial.succ internalPair =
      0
  rw [preContorsionFullLorentzActionCovector_spatial]
  change
    preContorsionSpatialLorentzActionTarget spatial internalPair -
      preContorsionSpatialProfileActualBFDivergenceCoordinates spatial
        internalPair = 0
  have reached := congrFun
    (congrFun preContorsionSpatialProfileActual_reaches_actionTarget spatial)
    internalPair
  rw [reached]
  ring

theorem preContorsionFullLorentzActionComplement_temporal_five :
    preContorsionFullLorentzActionComplement 0 5 = 1 / 2 := by
  unfold preContorsionFullLorentzActionComplement
  change
    preContorsionFullLorentzActionCovector 0 5 -
        preContorsionFullLorentzProfileDivergence 0 5 = 1 / 2
  rw [preContorsionFullLorentzActionCovector_temporal_five,
    preContorsionFullLorentzProfileDivergence_temporal_five]
  norm_num

theorem preContorsionFullLorentzActionComplement_nonzero :
    preContorsionFullLorentzActionComplement ≠ 0 := by
  intro complementZero
  have coordinate := congrFun (congrFun complementZero 0) 5
  rw [preContorsionFullLorentzActionComplement_temporal_five] at coordinate
  norm_num at coordinate

theorem preContorsionFullLorentzConnectionCorrection_normalized :
    simpleBEinsteinCartanGravityActionCoordinates
        preContorsionFullLorentzConnectionCorrection =
      preContorsionFullLorentzActionComplement := by
  exact simpleBGravityAction_contorsion _

theorem preContorsionFullLorentzConnectionCorrection_unique
    (candidate : LorentzBivectorOneForm)
    (normalization :
      simpleBEinsteinCartanGravityActionCoordinates candidate =
        preContorsionFullLorentzActionComplement) :
    candidate = preContorsionFullLorentzConnectionCorrection := by
  rw [← contorsion_simpleBGravityAction candidate,
    normalization]
  rfl

theorem preContorsionFullLorentzConnectionCorrection_nonzero :
    preContorsionFullLorentzConnectionCorrection ≠ 0 := by
  intro correctionZero
  apply preContorsionFullLorentzActionComplement_nonzero
  exact
    (einsteinCartanSpinContorsionCoordinates_eq_zero_iff
      preContorsionFullLorentzActionComplement).mp correctionZero

/-! ## Common-contact actual fields -/

private theorem coherentPreContorsionProfileActual_originFields :
    coherentPreContorsionProfileActual.coframe 0 = 1 ∧
      coherentPreContorsionProfileActual.gravityAuxiliary 0 =
        physicalIIPlusBivector 1 ∧
      coherentPreContorsionProfileActual.matter 0 =
        diracSpinTwoMatterProbe ∧
      coherentPreContorsionProfileActual.conjugateMatter 0 =
        diracSpinZeroMatterCoordinate := by
  have coframeOrigin : coherentPreContorsionProfileActual.coframe 0 = 1 := by
    rw [coherentProfileActual_coframe_normalForm,
      canonicalZeroSliceProjection.map_zero,
      preContorsionSpatialProfileActual_coframe_origin]
  have auxiliaryOrigin :
      coherentPreContorsionProfileActual.gravityAuxiliary 0 =
        physicalIIPlusBivector 1 := by
    have timeZero : canonicalTimeProjection (0 : BasePoint) = 0 :=
      map_zero _
    rw [coherentProfileActual_gravityAuxiliary_normalForm,
      canonicalZeroSliceProjection.map_zero, timeZero]
    simp only [zero_smul, add_zero]
    rw [preContorsionSpatialProfileActual_gravityAuxiliary_generated]
    change
      physicalIIPlusBivector
          (preContorsionSpatialProfileActual.coframe 0) =
        physicalIIPlusBivector 1
    rw [preContorsionSpatialProfileActual_coframe_origin]
  have slice :=
    positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual_initialSliceFidelity
      0
  rw [canonicalCauchySlicePoint_zero_zero] at slice
  rcases slice with
    ⟨_coframe, _connection, _auxiliary, _multiplier, _gaugeConnection,
      _gaugeAuxiliary, _scalar, matterSlice, conjugateSlice⟩
  have profileMatter :
      preContorsionSpatialProfileActual.matter 0 =
        diracSpinTwoMatterProbe := by
    rw [congrFun preContorsionSpatialProfileActual_retains_matterFields.1 0,
      preContorsionP286Actual_matter_origin]
  have profileConjugate :
      preContorsionSpatialProfileActual.conjugateMatter 0 =
        diracSpinZeroMatterCoordinate := by
    rw [congrFun preContorsionSpatialProfileActual_retains_matterFields.2 0,
      preContorsionP286Actual_conjugateMatter_origin]
  have matterOrigin :
      coherentPreContorsionProfileActual.matter 0 =
        diracSpinTwoMatterProbe := by
    simpa using matterSlice.trans profileMatter
  have conjugateOrigin :
      coherentPreContorsionProfileActual.conjugateMatter 0 =
        diracSpinZeroMatterCoordinate := by
    simpa using conjugateSlice.trans profileConjugate
  exact ⟨coframeOrigin, auxiliaryOrigin, matterOrigin, conjugateOrigin⟩

theorem fullLorentzTriangularActual_coframe_origin :
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.coframe
        0 = 1 := by
  rw [positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual,
    changedBackgroundLorentzOriginCarrier_coframe]
  exact coherentPreContorsionProfileActual_originFields.1

theorem fullLorentzTriangularActual_gravityAuxiliary_origin :
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.gravityAuxiliary
        0 = physicalIIPlusBivector 1 := by
  rw [positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual,
    changedBackgroundLorentzOriginCarrier_gravityAuxiliary]
  exact coherentPreContorsionProfileActual_originFields.2.1

theorem fullLorentzTriangularActual_connection_origin :
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.gravityConnection
        0 =
      lorentzSkewConnectionOfBivectorOneForm
        preContorsionFullLorentzConnectionCorrection := by
  exact changedBackgroundLorentzOriginCarrier_connection_origin _ _

theorem fullLorentzTriangularActual_matter_origin :
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.matter
        0 = diracSpinTwoMatterProbe := by
  rw [positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual,
    changedBackgroundLorentzOriginCarrier_matter]
  exact coherentPreContorsionProfileActual_originFields.2.2.1

theorem fullLorentzTriangularActual_conjugateMatter_origin :
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.conjugateMatter
        0 = diracSpinZeroMatterCoordinate := by
  rw [positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual,
    changedBackgroundLorentzOriginCarrier_conjugateMatter]
  exact coherentPreContorsionProfileActual_originFields.2.2.2

theorem fullLorentzTriangularActual_nondegenerate :
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.Nondegenerate := by
  intro point
  rw [positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual,
    changedBackgroundLorentzOriginCarrier_coframe,
    coherentProfileActual_coframe_normalForm]
  exact preContorsionSpatialProfileActual_nondegenerate _

/-- The normalized affine write changes the connection origin while retaining
the already generated curvature at the same contact. -/
theorem fullLorentzTriangularActual_curvature_origin :
    holonomicGravityCurvature
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        0 =
      holonomicGravityCurvature coherentPreContorsionProfileActual 0 := by
  exact changedBackgroundLorentzOriginCarrier_curvature_origin _ _

/-! ## Full action and divergence pairings -/

def lorentzCoordinatePairing
    (coordinates direction : LorentzBivectorOneForm) : ℝ :=
  ∑ formDirection : LorentzianIndex,
    ∑ internalPair : Fin 6,
      coordinates formDirection internalPair *
        direction formDirection internalPair

private theorem lorentzCoordinatePairing_coordinateDirection
    (coordinates : LorentzBivectorOneForm)
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    lorentzCoordinatePairing coordinates
        (einsteinCartanLorentzCoordinateDirection
          formDirection internalPair) =
      coordinates formDirection internalPair := by
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [lorentzCoordinatePairing,
      einsteinCartanLorentzCoordinateDirection, Fin.sum_univ_six]

private theorem lorentzCoordinatePairing_sub_left
    (first second direction : LorentzBivectorOneForm) :
    lorentzCoordinatePairing (first - second) direction =
      lorentzCoordinatePairing first direction -
        lorentzCoordinatePairing second direction := by
  simp [lorentzCoordinatePairing, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

private def lorentzCoordinateDual
    (coordinates : LorentzBivectorOneForm) :
    Module.Dual ℝ LorentzBivectorOneForm where
  toFun := lorentzCoordinatePairing coordinates
  map_add' := by
    intro first second
    simp [lorentzCoordinatePairing, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' := by
    intro scalar direction
    change
      (∑ formDirection : LorentzianIndex,
        ∑ internalPair : Fin 6,
          coordinates formDirection internalPair *
            (scalar * direction formDirection internalPair)) =
        scalar *
          ∑ formDirection : LorentzianIndex,
            ∑ internalPair : Fin 6,
              coordinates formDirection internalPair *
                direction formDirection internalPair
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro formDirection _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro internalPair _
    ring

private theorem fullLorentzTriangularActual_matterSpinCoordinates :
    actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        0 =
      preContorsionFullLorentzActionCovector := by
  change
    lorentzMatterSpinCoordinates positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        0 =
      preContorsionFullLorentzActionCovector
  rw [positiveMatterSpinCoordinates_eq_normalForm_of_origin
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
      fullLorentzTriangularActual_coframe_origin
      fullLorentzTriangularActual_matter_origin
      fullLorentzTriangularActual_conjugateMatter_origin,
    preContorsionFullLorentzActionCovector_eq_normalForm]

private theorem fullLorentzTriangularActual_gravityDual :
    -einsteinCartanGravityBFActionDual
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        0 =
      lorentzCoordinateDual preContorsionFullLorentzActionComplement := by
  have coordinates :=
    actualSimpleBContorsion_gravityAction_eq_spin
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
      preContorsionFullLorentzActionComplement
      fullLorentzTriangularActual_coframe_origin
      fullLorentzTriangularActual_gravityAuxiliary_origin
      fullLorentzTriangularActual_connection_origin
  apply einsteinCartanLorentzDual_eq_of_coordinate_eq
  intro formDirection internalPair
  change
    -lorentzGravityBFAlgebraicCoefficient
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        (einsteinCartanLorentzCoordinateDirection
          formDirection internalPair) 0 =
      lorentzCoordinatePairing preContorsionFullLorentzActionComplement
        (einsteinCartanLorentzCoordinateDirection
          formDirection internalPair)
  rw [lorentzCoordinatePairing_coordinateDirection]
  exact congrFun (congrFun coordinates formDirection) internalPair

private theorem fullLorentzTriangularActual_matterDual :
    einsteinCartanMatterSpinActionDual positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        0 =
      lorentzCoordinateDual preContorsionFullLorentzActionCovector := by
  apply einsteinCartanLorentzDual_eq_of_coordinate_eq
  intro formDirection internalPair
  change
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        (einsteinCartanLorentzCoordinateDirection
          formDirection internalPair) 0 =
      lorentzCoordinatePairing preContorsionFullLorentzActionCovector
        (einsteinCartanLorentzCoordinateDirection
          formDirection internalPair)
  rw [lorentzCoordinatePairing_coordinateDirection]
  exact congrFun
    (congrFun fullLorentzTriangularActual_matterSpinCoordinates formDirection)
    internalPair

theorem preContorsionSpatialProfileActual_fullDivergence_eq_pairing
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionBFDifferentialMomentumDivergence
        preContorsionSpatialProfileActual direction 0 =
      lorentzCoordinatePairing
        preContorsionFullLorentzProfileDivergence direction := by
  rw [show preContorsionSpatialProfileActual =
      spatialSkewCoframeActualOn PreContorsionP286Actual
        generatedSpatialSkewCoframeJet by rfl]
  rw [spatialSkewCoframeActualOn_fullBFMomentumDivergence_eq_skew]
  rw [skewCoframeMomentumDivergence_origin]
  unfold preContorsionFullLorentzProfileDivergence
    lorentzCoordinatePairing
  rw [spatialSkewCoframeActualOnFullBFDivergenceCoordinates_eq_actualOperator]
  simp_rw [skewCoframeActualBFDivergenceCoordinates_apply]

theorem fullLorentzTriangularActual_fullDivergence_eq_pairing
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionBFDifferentialMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        direction 0 =
      lorentzCoordinatePairing
        preContorsionFullLorentzProfileDivergence direction := by
  rw [positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual,
    changedBackgroundLorentzCarrier_divergenceResponse_eq_background,
    coherentProfileActual_fullBFMomentumDivergence_eq_profile,
    preContorsionSpatialProfileActual_fullDivergence_eq_pairing]

/-! ## All-direction action closure -/

/-- The one generated actual closes the complete Lorentz response in every
direction.  Since the correction was generated by this same action equation,
this theorem is producer soundness; it is not counted as an independent
Cauchy constraint. -/
theorem fullLorentzTriangularActual_eulerLagrange_origin
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        direction 0 = 0 := by
  have gravityEvaluation := congrArg
    (fun response : Module.Dual ℝ LorentzBivectorOneForm =>
      response direction)
    fullLorentzTriangularActual_gravityDual
  have matterEvaluation := congrArg
    (fun response : Module.Dual ℝ LorentzBivectorOneForm =>
      response direction)
    fullLorentzTriangularActual_matterDual
  change
    -lorentzGravityBFAlgebraicCoefficient
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        direction 0 =
      lorentzCoordinatePairing preContorsionFullLorentzActionComplement
        direction at gravityEvaluation
  change
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        direction 0 =
      lorentzCoordinatePairing preContorsionFullLorentzActionCovector
        direction at matterEvaluation
  have complementEvaluation :
      lorentzCoordinatePairing preContorsionFullLorentzActionComplement
          direction =
        lorentzCoordinatePairing preContorsionFullLorentzActionCovector
            direction -
          lorentzCoordinatePairing
            preContorsionFullLorentzProfileDivergence direction := by
    unfold preContorsionFullLorentzActionComplement
    exact lorentzCoordinatePairing_sub_left _ _ _
  rw [lorentzConnectionEulerLagrangeCoefficient_eq_sectorBalance]
  unfold lorentzGravityBFBalanceCoefficient
  rw [fullLorentzTriangularActual_fullDivergence_eq_pairing]
  linarith

/-- Temporal Lorentz Gauss is the structural temporal projection of the
already closed full response.  It is recorded as primary acceptance, not as
an additional independent equation. -/
theorem fullLorentzTriangularActual_temporalGauss_origin :
    CanonicalLorentzTemporalGaussConstraintAt positiveSmoothUnifiedSource
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
      0 := by
  intro component
  exact fullLorentzTriangularActual_eulerLagrange_origin
    (canonicalLorentzTemporalBivectorOneForm component)

/-! ## C3h200n checkpoint law -/

structure PositiveP506MatterPreContorsionFullLorentzTriangularActualLiftLaw :
    Prop where
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  endpointEleven :
    positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
        canonicalSource_generatedLineage_height_pos = 11
  actionCovectorGenerated : ∀ formDirection internalPair,
    preContorsionFullLorentzActionCovector formDirection internalPair =
      lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource PreContorsionP286Actual
        (lorentzBivectorOneFormCoordinateDirection
          formDirection internalPair) 0
  profileDivergenceGenerated : ∀ formDirection internalPair,
    preContorsionFullLorentzProfileDivergence formDirection internalPair =
      lorentzConnectionBFDifferentialMomentumDivergence
        preContorsionSpatialProfileActual
        (lorentzBivectorOneFormCoordinateDirection
          formDirection internalPair) 0
  spatialComplementZero : ∀ (spatial : Fin 3) (internalPair : Fin 6),
    preContorsionFullLorentzActionComplement spatial.succ internalPair = 0
  nonzeroTemporalComplement :
    preContorsionFullLorentzActionComplement 0 5 = 1 / 2
  correctionNormalized :
    simpleBEinsteinCartanGravityActionCoordinates
        preContorsionFullLorentzConnectionCorrection =
      preContorsionFullLorentzActionComplement
  correctionUnique : ∀ candidate,
    simpleBEinsteinCartanGravityActionCoordinates candidate =
        preContorsionFullLorentzActionComplement →
      candidate = preContorsionFullLorentzConnectionCorrection
  correctionNonzero : preContorsionFullLorentzConnectionCorrection ≠ 0
  actualPath :
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual =
      changedBackgroundLorentzOriginCarrier
        coherentPreContorsionProfileActual
        preContorsionFullLorentzConnectionCorrection
  actualNondegenerate :
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.Nondegenerate
  contactCurvatureRetained :
    holonomicGravityCurvature
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        0 =
      holonomicGravityCurvature coherentPreContorsionProfileActual 0
  fullLorentzResponse : ∀ direction,
    lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        direction 0 = 0
  temporalGaussProjection :
    CanonicalLorentzTemporalGaussConstraintAt positiveSmoothUnifiedSource
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
      0

theorem
    positiveP506MatterPreContorsionFullLorentzTriangularActualLift_realizes_C3h200n :
    PositiveP506MatterPreContorsionFullLorentzTriangularActualLiftLaw := by
  exact
    { exactP506L0Lineage :=
        positiveSmoothUnifiedSource_generates_exactP506L0Lineage
      endpointEleven := positiveSmoothUnifiedSource_generates_endpoint_eleven
      actionCovectorGenerated := fun _ _ => rfl
      profileDivergenceGenerated := fun _ _ => rfl
      spatialComplementZero :=
        preContorsionFullLorentzActionComplement_spatial_zero
      nonzeroTemporalComplement :=
        preContorsionFullLorentzActionComplement_temporal_five
      correctionNormalized :=
        preContorsionFullLorentzConnectionCorrection_normalized
      correctionUnique :=
        preContorsionFullLorentzConnectionCorrection_unique
      correctionNonzero :=
        preContorsionFullLorentzConnectionCorrection_nonzero
      actualPath := rfl
      actualNondegenerate := fullLorentzTriangularActual_nondegenerate
      contactCurvatureRetained :=
        fullLorentzTriangularActual_curvature_origin
      fullLorentzResponse :=
        fullLorentzTriangularActual_eulerLagrange_origin
      temporalGaussProjection :=
        fullLorentzTriangularActual_temporalGauss_origin }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzTriangularActualLift
