import H0mework.Physics.GaugeAction.FullSynchronizedCompleteP286ActionResponseOperator
import H0mework.Physics.MatterCurrent.FullSynchronizedResponseOperator
import H0mework.Physics.MatterCurrent.FullSynchronizedP286ResponseReplay

/-!
# S9-C3h169: actual-first complete-P286 Cauchy path

The external exact P506/L0 seed is the already generated complete-P286
actual `U8`.  The full synchronized operator first generates `U*`; only then
does the current P286 operator recompute and install the complete auxiliary
response:

```text
U8
→ full synchronized action response U*
→ current-action complete P286 response
→ the same whole actual U*
→ canonical Cauchy restriction of that generated actual.
```

The Cauchy path is therefore a readout of one whole action-generated actual,
not a fieldwise endpoint reconstruction.  Its P286 auxiliary coordinate
retains the spatial Gauss profile at every spatial contact and has the
freshly generated BF-Legendre velocity as its physical-time derivative.

The composition is not claimed to preserve the external `U8` seed, to be a
generic fixed point, restart, flow, or semigroup.  Outer origin fidelity is
only relative to the intermediate `U*`.  The P286 connection equation remains
producer consistency, while the same-actual scalar equation remains the
independent constraint.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineFullSynchronizedCompleteP286ActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedP286ResponseReplay
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseOperator
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Exact composed actual and canonical path -/

def positiveP506MatterCurrentFullSynchronizedCompleteP286ActionResponse :
    StageNineHolonomicConfiguration :=
  fullSynchronizedCompleteP286ActionResponseOperator
    positiveSmoothUnifiedSource positiveP506MatterCurrentCompleteBaseActual

/-- The full action first generates `U*`; the outer current P286 response
then exactly replays its complete auxiliary germ. -/
theorem
    positiveP506MatterCurrentFullSynchronizedCompleteP286ActionResponse_eq_UStar :
    positiveP506MatterCurrentFullSynchronizedCompleteP286ActionResponse =
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift := by
  unfold positiveP506MatterCurrentFullSynchronizedCompleteP286ActionResponse
    fullSynchronizedCompleteP286ActionResponseOperator
  rw [
    positiveP506MatterCurrentFullSynchronizedActionResponseOperator_eq_UStar,
    positiveP506MatterCurrentUStarP286CompleteActionResponseOperator_replays]

def positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
    (time : ℝ) :
    StageNineCauchyState :=
  fullSynchronizedCompleteP286CanonicalCauchyPath
    positiveSmoothUnifiedSource positiveP506MatterCurrentCompleteBaseActual
    time

def positiveP506MatterCurrentFullSynchronizedCauchyState :
    StageNineCauchyState :=
  canonicalCauchyRestriction 0
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift

theorem positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath_eq
    (time : ℝ) :
    positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath time =
      canonicalCauchyRestriction time
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift := by
  unfold positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
    fullSynchronizedCompleteP286CanonicalCauchyPath
  exact congrArg (canonicalCauchyRestriction time)
    positiveP506MatterCurrentFullSynchronizedCompleteP286ActionResponse_eq_UStar

/-- Zero fidelity is to the generated `U*` Cauchy state, not to the external
`U8` seed. -/
@[simp] theorem
    positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath_zero :
    positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath 0 =
      positiveP506MatterCurrentFullSynchronizedCauchyState := by
  exact positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath_eq 0

theorem
    positiveP506MatterCurrentFullSynchronizedCompleteP286_outerOriginContact :
    toContinuumPointField
        positiveP506MatterCurrentFullSynchronizedCompleteP286ActionResponse 0 =
      toContinuumPointField
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 := by
  rw [
    positiveP506MatterCurrentFullSynchronizedCompleteP286ActionResponse_eq_UStar]

/-! ## Actual auxiliary coordinate along the canonical path -/

def positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    P286GaugeTwoForm :=
  fun pair =>
    p286CoordinateEquiv
      ((positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath time
        |>.gaugeAuxiliary) space pair)

theorem
    positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_eq_generated
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate
        time space =
      currentP286CompleteResponseAuxiliaryCoordinate
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        (canonicalCauchySlicePoint time space) := by
  funext pair
  unfold
    positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate
    positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
    fullSynchronizedCompleteP286CanonicalCauchyPath
    fullSynchronizedCompleteP286ActionResponseOperator
    canonicalCauchyRestriction
  rw [
    positiveP506MatterCurrentFullSynchronizedActionResponseOperator_eq_UStar]
  change
    holonomicP286GaugeAuxiliaryCoordinate
        (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift)
        (canonicalCauchySlicePoint time space) pair =
      _
  rw [currentP286CompleteActionResponseOperator_auxiliaryCoordinate]

/-- The whole spatial Gauss profile remains in the path; only its temporal
coefficient is constant. -/
theorem
    positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_normalForm
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate
        time space =
      currentP286OriginAuxiliaryCoordinate
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift +
        time •
          p286SpatialAuxiliaryVelocityEmbedding
            (currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift) +
        ∑ axis : Fin 3,
          (canonicalP286EqualAxisCoefficient * space axis) •
            p286GaussAuxiliaryAxisEmbedding
              (currentP286GaussCharge positiveSmoothUnifiedSource
                positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift)
              axis := by
  rw [
    positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_eq_generated,
    currentP286CompleteResponseAuxiliaryCoordinate_canonicalSlice]

/-- Actual-first physical-time jet at every spatial contact and coordinate
pair.  No velocity witness is supplied by the caller. -/
theorem
    positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_hasDerivAt
    (space : StageNineSpatialPoint)
    (pair : Fin 6)
    (time : ℝ) :
    HasDerivAt
      (fun candidate : ℝ =>
        positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate
          candidate space pair)
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift)
        pair)
      time := by
  rw [show
    (fun candidate : ℝ =>
      positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate
        candidate space pair) =
      (fun candidate : ℝ =>
        currentP286CompleteResponseAuxiliaryCoordinate
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          (canonicalCauchySlicePoint candidate space) pair) by
    funext candidate
    exact congrFun
      (positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_eq_generated
        candidate space)
      pair]
  exact
    currentP286CompleteResponseAuxiliaryCoordinate_canonicalSlice_hasDerivAt
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
      space pair time

theorem
    positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_deriv
    (space : StageNineSpatialPoint)
    (pair : Fin 6)
    (time : ℝ) :
    deriv
        (fun candidate : ℝ =>
          positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate
            candidate space pair)
        time =
      p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift)
        pair :=
  (positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_hasDerivAt
    space pair time).deriv

/-! ## No-premise C3h169 path law -/

structure
    PositiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPathLaw :
    Prop where
  sourceGeneratedU8 :
    PositiveP506MatterCurrentP286CompleteResponseProducerSoundnessLaw
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  generatedActual :
    positiveP506MatterCurrentFullSynchronizedCompleteP286ActionResponse =
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
  pathGenerated : ∀ time,
    positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath time =
      canonicalCauchyRestriction time
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
  zeroFaithful :
    positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath 0 =
      positiveP506MatterCurrentFullSynchronizedCauchyState
  outerOriginContact :
    toContinuumPointField
        positiveP506MatterCurrentFullSynchronizedCompleteP286ActionResponse 0 =
      toContinuumPointField
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0
  auxiliaryCoordinateNormalForm : ∀ time space,
    positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate
        time space =
      currentP286OriginAuxiliaryCoordinate
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift +
        time •
          p286SpatialAuxiliaryVelocityEmbedding
            (currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift) +
        ∑ axis : Fin 3,
          (canonicalP286EqualAxisCoefficient * space axis) •
            p286GaussAuxiliaryAxisEmbedding
              (currentP286GaussCharge positiveSmoothUnifiedSource
                positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift)
              axis
  auxiliaryTimeJet : ∀ space pair time,
    HasDerivAt
      (fun candidate : ℝ =>
        positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate
          candidate space pair)
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift)
        pair)
      time
  actualTemporalMomentumResponse : ∀ direction : P286GaugeOneForm,
    p286GaugeConnectionTemporalBFMomentumDerivative
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      currentP286SpatialActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        (fun index => direction index.succ)
  actualSpatialMomentumResponse : ∀ direction : P286GaugeOneForm,
    p286GaugeConnectionSpatialBFMomentumDivergence
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      currentP286TemporalActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        (direction canonicalLorentzianTimeDirection)
  producerP286ConnectionConsistency : ∀ direction : P286GaugeOneForm,
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      0
  independentScalarConstraint : ∀ direction : ScalarCoordinateCarrier,
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      0

theorem
    positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath_realizes_C3h169 :
    PositiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPathLaw := by
  exact
    { sourceGeneratedU8 :=
        positiveP506MatterCurrentFullSynchronizedActionResponseOperator_realizes_C3h167.sourceGeneratedU8
      exactP506L0Lineage :=
        positiveP506MatterCurrentFullSynchronizedActionResponseOperator_realizes_C3h167.exactP506L0Lineage
      generatedActual :=
        positiveP506MatterCurrentFullSynchronizedCompleteP286ActionResponse_eq_UStar
      pathGenerated :=
        positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath_eq
      zeroFaithful :=
        positiveP506MatterCurrentFullSynchronizedCompleteP286CauchyPath_zero
      outerOriginContact :=
        positiveP506MatterCurrentFullSynchronizedCompleteP286_outerOriginContact
      auxiliaryCoordinateNormalForm :=
        positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_normalForm
      auxiliaryTimeJet :=
        positiveP506MatterCurrentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_hasDerivAt
      actualTemporalMomentumResponse :=
        positiveP506MatterCurrentUStarP286TemporalBFMomentumResponse
      actualSpatialMomentumResponse :=
        positiveP506MatterCurrentUStarP286SpatialBFMomentumResponse
      producerP286ConnectionConsistency :=
        positiveP506MatterCurrentUStarP286ConnectionProducerConsistency
      independentScalarConstraint :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_realizes_C3h166.independentScalarConstraint }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
