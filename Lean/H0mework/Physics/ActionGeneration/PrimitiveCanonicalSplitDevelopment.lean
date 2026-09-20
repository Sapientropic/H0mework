import H0mework.Physics.Exterior.JointActionCanonicalPhasePathLaw
import H0mework.Physics.ActionGeneration.JointPrimitiveCauchyDevelopment

/-!
# S9-C3h125: source/action-generated primitive--canonical split development

C3h123/C3h124 generate and differentiate the whole-slice primitive actual
path.  C3h99/C3h100 independently generate and differentiate the native
canonical action path, including Lorentz/P286 BF-momentum evaluations and the
scalar temporal-momentum evaluation that do not occur as fields of
`StageNineCauchyState`.

This module computes both projections from the same `(source, state, time)`:

```text
same proof-free source + primitive state + physical time
       ↙                                  ↘
primitive actual Cauchy U          canonical action U
       ↘ shared coordinates synchronize ↙
canonical-only momenta remain native action outputs
→ later incidence / equation / residual acceptance.
```

The split carrier is a coordination carrier, not a new physical field and
not a full on-shell synchronized development.  Primitive gravity/P286
auxiliaries remain genuine BF fields; canonical momenta are action-dual
evaluations of connection velocities.  This constructor neither identifies
the two types nor decodes momentum into an auxiliary endpoint.  Likewise, it
does not decode scalar momentum force into acceleration.  Matter/dual
synchronization below is an equality of the already generated affine
projection data; its arbitrary-coframe Dirac interpretation still requires
the existing identity-coframe action domain.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedPrimitiveCanonicalSplitDevelopment

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineJointActionCanonicalPhasePathLaw
open StageNineJointActionCanonicalPhaseUpdate
open StageNineJointActionLocalActualLift
open StageNineLorentzActionCanonicalPairUpdate
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineSourceActionGeneratedJointPrimitiveCauchyDevelopment
open StageNineSourceActionGeneratedJointPrimitiveCauchyPath
open StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
open StageNineSourceGeneratedMatterSpinActionUpdate
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Same-source split carrier -/

/-- Computed primitive/canonical projections of one action development.
Neither projection is supplied by a caller. -/
@[ext] structure StageNinePrimitiveCanonicalSplitActionState where
  primitive : StageNineCauchyState
  canonical : StageNineJointCanonicalPhaseState

def sourceActionGeneratedPrimitiveCanonicalSplitUpdate
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState) :
    StageNinePrimitiveCanonicalSplitActionState where
  primitive :=
    sourceActionGeneratedJointPrimitiveCauchyUpdate source time state
  canonical :=
    sourceActionGeneratedJointCanonicalPhaseUpdate source time state

private theorem canonicalCauchySlicePoint_zeroSpace_eq_timeLine
    (time : ℝ) :
    canonicalCauchySlicePoint time 0 =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem actionGeneratedLorentzLocalConnectionJet_time_spatial
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internalPair : Fin 6) :
    actionGeneratedLorentzLocalConnectionJet state space
        canonicalLorentzianTimeDirection direction.succ internalPair =
      actionGeneratedLorentzSpatialConnectionVelocity
        state space direction internalPair := by
  fin_cases direction <;>
    rfl

private theorem actionGeneratedLorentzLocalConnectionJet_time_temporal
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair : Fin 6) :
    actionGeneratedLorentzLocalConnectionJet state space
        canonicalLorentzianTimeDirection
        canonicalLorentzianTimeDirection internalPair =
      0 := by
  rfl

private theorem actionGeneratedLorentzLocalIncrement_coordinateDirection
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection derivativeDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    actionGeneratedLorentzLocalIncrement state space formDirection
        internalPair (coordinateDirection derivativeDirection) =
      actionGeneratedLorentzLocalConnectionJet state space
        derivativeDirection formDirection internalPair := by
  fin_cases derivativeDirection <;>
    simp [actionGeneratedLorentzLocalIncrement, coordinateDirection,
      Fin.sum_univ_four]

private theorem sourceGeneratedP286ActionLocalConnectionJet_time_spatial
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    sourceGeneratedP286ActionLocalConnectionJet source state space
        canonicalLorentzianTimeDirection direction.succ =
      p286CoordinateEquiv
        (sourceGeneratedP286SpatialConnectionVelocity
          source state space direction) := by
  fin_cases direction <;>
    rfl

private theorem sourceGeneratedP286ActionLocalConnectionJet_time_temporal
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    sourceGeneratedP286ActionLocalConnectionJet source state space
        canonicalLorentzianTimeDirection
        canonicalLorentzianTimeDirection =
      0 := by
  rfl

private theorem sourceGeneratedP286ActionLocalIncrement_coordinateDirection
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection derivativeDirection : LorentzianIndex) :
    sourceGeneratedP286ActionLocalIncrement source state space formDirection
        (coordinateDirection derivativeDirection) =
      sourceGeneratedP286ActionLocalConnectionJet source state space
        derivativeDirection formDirection := by
  fin_cases derivativeDirection <;>
    simp [sourceGeneratedP286ActionLocalIncrement, coordinateDirection,
      Fin.sum_univ_four]

private theorem actionGeneratedMatterLocalJetCoordinate_time
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    actionGeneratedMatterLocalJetCoordinate state space
        canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity state space) := by
  rfl

private theorem actionGeneratedMatterLocalIncrement_coordinateDirection
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    actionGeneratedMatterLocalIncrement state space
        (coordinateDirection direction) =
      actionGeneratedMatterLocalJetCoordinate state space direction := by
  fin_cases direction <;>
    simp [actionGeneratedMatterLocalIncrement, coordinateDirection,
      Fin.sum_univ_four]

private theorem actionGeneratedConjugateMatterLocalJet_time
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    actionGeneratedConjugateMatterLocalJet state space
        canonicalLorentzianTimeDirection =
      actionGeneratedConjugateMatterTimeDerivative state space := by
  rfl

/-! ## Exact synchronization of shared projection data -/

theorem sourceActionGeneratedPrimitiveCanonicalSplitUpdate_coframe_sync
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
      source time state).primitive.coframe space =
      (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
        source time state).canonical.frozenCoframeSnapshot space := by
  rfl

theorem sourceActionGeneratedPrimitiveCanonicalSplitUpdate_multiplier_sync
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
      source time state).primitive.gravitySimplicityMultiplier space =
      (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
        source time state).canonical.gravitySimplicityMultiplier space := by
  rfl

theorem
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_temporalLorentz_sync
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair : Fin 6) :
    loweredLorentzConnectionCoefficient
        ((sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source time state).primitive.gravityConnection space)
        canonicalLorentzianTimeDirection internalPair =
      (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
        source time state).canonical.temporalGravityConnection
          space internalPair := by
  simp only [sourceActionGeneratedPrimitiveCanonicalSplitUpdate,
    sourceActionGeneratedJointPrimitiveCauchyUpdate,
    sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction]
  change
    loweredLorentzConnectionCoefficient
        (actionGeneratedLorentzLocalConnection state space
          (canonicalCauchySlicePoint time 0))
        canonicalLorentzianTimeDirection internalPair =
      _
  rw [actionGeneratedLorentzLocalConnection_loweredCoordinate]
  simp only [actionGeneratedLorentzLocalConnectionCoordinate,
    canonicalCauchySlicePoint_zeroSpace_eq_timeLine]
  rw [map_smul,
    actionGeneratedLorentzLocalIncrement_coordinateDirection,
    actionGeneratedLorentzLocalConnectionJet_time_temporal]
  simp [sourceActionGeneratedJointCanonicalPhaseUpdate]

theorem
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_spatialLorentz_sync
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internalPair : Fin 6) :
    loweredLorentzConnectionCoefficient
        ((sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source time state).primitive.gravityConnection space)
        direction.succ internalPair =
      (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
        source time state).canonical.gravityGauge.lorentz.spatialConnection
          space direction internalPair := by
  simp only [sourceActionGeneratedPrimitiveCanonicalSplitUpdate,
    sourceActionGeneratedJointPrimitiveCauchyUpdate,
    sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction]
  change
    loweredLorentzConnectionCoefficient
        (actionGeneratedLorentzLocalConnection state space
          (canonicalCauchySlicePoint time 0))
        direction.succ internalPair =
      _
  rw [actionGeneratedLorentzLocalConnection_loweredCoordinate]
  simp only [actionGeneratedLorentzLocalConnectionCoordinate,
    canonicalCauchySlicePoint_zeroSpace_eq_timeLine]
  rw [map_smul,
    actionGeneratedLorentzLocalIncrement_coordinateDirection,
    actionGeneratedLorentzLocalConnectionJet_time_spatial]
  rfl

theorem
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_temporalP286_sync
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
      source time state).primitive.gaugeConnection
        space canonicalLorentzianTimeDirection =
      (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
        source time state).canonical.temporalGaugeConnection space := by
  apply p286CoordinateEquiv.injective
  simp only [sourceActionGeneratedPrimitiveCanonicalSplitUpdate,
    sourceActionGeneratedJointPrimitiveCauchyUpdate,
    sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction]
  change
    p286CoordinateEquiv
        (sourceGeneratedP286ActionLocalConnection source state space
          (canonicalCauchySlicePoint time 0)
          canonicalLorentzianTimeDirection) =
      _
  simp only [sourceGeneratedP286ActionLocalConnection,
    p286CoordinateEquiv.apply_symm_apply,
    sourceGeneratedP286ActionLocalConnectionCoordinate,
    canonicalCauchySlicePoint_zeroSpace_eq_timeLine]
  rw [map_smul,
    sourceGeneratedP286ActionLocalIncrement_coordinateDirection,
    sourceGeneratedP286ActionLocalConnectionJet_time_temporal]
  simp [sourceActionGeneratedJointCanonicalPhaseUpdate]

theorem
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_spatialP286_sync
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    p286CoordinateEquiv
        ((sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source time state).primitive.gaugeConnection
            space direction.succ) =
      (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
        source time state).canonical.gravityGauge.p286.spatialConnection
          space direction := by
  simp only [sourceActionGeneratedPrimitiveCanonicalSplitUpdate,
    sourceActionGeneratedJointPrimitiveCauchyUpdate,
    sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction]
  change
    p286CoordinateEquiv
        (sourceGeneratedP286ActionLocalConnection source state space
          (canonicalCauchySlicePoint time 0) direction.succ) =
      _
  simp only [sourceGeneratedP286ActionLocalConnection,
    p286CoordinateEquiv.apply_symm_apply,
    sourceGeneratedP286ActionLocalConnectionCoordinate,
    canonicalCauchySlicePoint_zeroSpace_eq_timeLine]
  rw [map_smul,
    sourceGeneratedP286ActionLocalIncrement_coordinateDirection,
    sourceGeneratedP286ActionLocalConnectionJet_time_spatial]
  rfl

theorem sourceActionGeneratedPrimitiveCanonicalSplitUpdate_scalar_sync
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
      source time state).primitive.scalar space =
      (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
        source time state).canonical.scalar.scalarCoordinate space := by
  simp only [sourceActionGeneratedPrimitiveCanonicalSplitUpdate,
    sourceActionGeneratedJointPrimitiveCauchyUpdate,
    sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction]
  change
    actionGeneratedScalarLocalField state space
        (canonicalCauchySlicePoint time 0) =
      _
  simp only [actionGeneratedScalarLocalField,
    canonicalCauchySlicePoint_zeroSpace_eq_timeLine]
  rw [map_smul]
  congr 1
  simp [actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate, coordinateDirection,
    canonicalLorentzianTimeDirection, Fin.sum_univ_four,
    sourceActionGeneratedScalarCanonicalPhaseVelocity]

theorem sourceActionGeneratedPrimitiveCanonicalSplitUpdate_matter_sync
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
      source time state).primitive.matter space =
      (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
        source time state).canonical.matter space := by
  apply matterCoordinateEquiv.injective
  simp only [sourceActionGeneratedPrimitiveCanonicalSplitUpdate,
    sourceActionGeneratedJointPrimitiveCauchyUpdate,
    sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction]
  change
    matterCoordinateEquiv
        (actionGeneratedMatterLocalField state space
          (canonicalCauchySlicePoint time 0)) =
      matterCoordinateEquiv
        (actionGeneratedMatterPhaseUpdate time state space)
  simp only [actionGeneratedMatterLocalField,
    matterCoordinateEquiv.apply_symm_apply,
    actionGeneratedMatterLocalCoordinate,
    canonicalCauchySlicePoint_zeroSpace_eq_timeLine,
    actionGeneratedMatterPhaseUpdate]
  rw [map_smul, actionGeneratedMatterLocalIncrement_coordinateDirection,
    actionGeneratedMatterLocalJetCoordinate_time, map_add]
  have mapRealSmul :
      matterCoordinateEquiv
          (time • actionGeneratedMatterRawTimeVelocity state space) =
        time • matterCoordinateEquiv
          (actionGeneratedMatterRawTimeVelocity state space) :=
    matterCoordinateEquiv.toLinearMap.map_smul_of_tower
      time (actionGeneratedMatterRawTimeVelocity state space)
  rw [mapRealSmul]

theorem
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_conjugateMatter_sync
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
      source time state).primitive.conjugateMatter space =
      (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
        source time state).canonical.conjugateMatter space := by
  apply LinearMap.ext
  intro matter
  simp only [sourceActionGeneratedPrimitiveCanonicalSplitUpdate,
    sourceActionGeneratedJointPrimitiveCauchyUpdate,
    sourceActionGeneratedJointPrimitiveCauchyPath,
    canonicalCauchyRestriction]
  change
    actionGeneratedConjugateMatterLocalField state space
        (canonicalCauchySlicePoint time 0) matter =
      actionGeneratedConjugateMatterPhaseUpdate time state space matter
  rw [actionGeneratedConjugateMatterLocalField_apply,
    canonicalCauchySlicePoint_zeroSpace_eq_timeLine, map_smul,
    actionGeneratedConjugateMatterLocalEvaluationIncrement_coordinateDirection,
    actionGeneratedConjugateMatterLocalJet_time]
  rfl

/-! ## Canonical-only momentum provenance -/

theorem
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_p286Momentum_initial
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : P286SpatialGaugeDirection) :
    (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
      source 0 state).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
        space direction =
      sourceActionGeneratedP286SpatialBFMomentumEvaluation
        source state space direction := by
  simp [sourceActionGeneratedPrimitiveCanonicalSplitUpdate,
    sourceActionGeneratedJointCanonicalPhaseUpdate,
    sourceActionGeneratedGravityGaugeCanonicalPhaseState,
    sourceActionGeneratedP286CanonicalPhaseState]

theorem
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_lorentzMomentum_initial
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
      source 0 state).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
        space direction =
      sourceActionGeneratedLorentzSpatialBFMomentumEvaluation
        source state space direction := by
  simp [sourceActionGeneratedPrimitiveCanonicalSplitUpdate,
    sourceActionGeneratedJointCanonicalPhaseUpdate,
    sourceActionGeneratedGravityGaugeCanonicalPhaseState,
    sourceActionGeneratedLorentzCanonicalPhaseState]

theorem
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_scalarMomentum_initial
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
      source 0 state).canonical.scalar.temporalMomentumEvaluation
        space direction =
      sourceActionGeneratedScalarTemporalMomentumEvaluation
        source state space direction := by
  simp [sourceActionGeneratedPrimitiveCanonicalSplitUpdate,
    sourceActionGeneratedJointCanonicalPhaseUpdate,
    sourceActionGeneratedScalarCanonicalPhaseState]

/-! ## Bundled split-development law -/

/-- Same-source coordination law for the primitive actual and native
canonical action projections.  It deliberately omits every
auxiliary--momentum, constitutive, scalar-acceleration, shell, and stationarity
acceptance predicate. -/
structure StageNinePrimitiveCanonicalSplitActionDevelopmentLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (update : ℝ → StageNinePrimitiveCanonicalSplitActionState) : Prop where
  updateGenerated :
    update =
      fun time =>
        sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source time state
  primitiveDevelopment :
    StageNineJointPrimitiveFrozenInputActionCauchyDevelopmentLaw
      source state (fun time => (update time).primitive)
  canonicalDerivative :
    ∀ time,
      StageNineJointCanonicalPathDerivativeLaw source state time
  coframeSync :
    ∀ time space,
      (update time).primitive.coframe space =
        (update time).canonical.frozenCoframeSnapshot space
  multiplierSync :
    ∀ time space,
      (update time).primitive.gravitySimplicityMultiplier space =
        (update time).canonical.gravitySimplicityMultiplier space
  temporalLorentzSync :
    ∀ time space internalPair,
      loweredLorentzConnectionCoefficient
          ((update time).primitive.gravityConnection space)
          canonicalLorentzianTimeDirection internalPair =
        (update time).canonical.temporalGravityConnection
          space internalPair
  spatialLorentzSync :
    ∀ time space direction internalPair,
      loweredLorentzConnectionCoefficient
          ((update time).primitive.gravityConnection space)
          direction.succ internalPair =
        (update time).canonical.gravityGauge.lorentz.spatialConnection
          space direction internalPair
  temporalP286Sync :
    ∀ time space,
      (update time).primitive.gaugeConnection
          space canonicalLorentzianTimeDirection =
        (update time).canonical.temporalGaugeConnection space
  spatialP286Sync :
    ∀ time space direction,
      p286CoordinateEquiv
          ((update time).primitive.gaugeConnection
            space direction.succ) =
        (update time).canonical.gravityGauge.p286.spatialConnection
          space direction
  scalarSync :
    ∀ time space,
      (update time).primitive.scalar space =
        (update time).canonical.scalar.scalarCoordinate space
  matterSync :
    ∀ time space,
      (update time).primitive.matter space =
        (update time).canonical.matter space
  conjugateMatterSync :
    ∀ time space,
      (update time).primitive.conjugateMatter space =
        (update time).canonical.conjugateMatter space
  p286MomentumInitial :
    ∀ space direction,
      (update 0).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
          space direction =
        sourceActionGeneratedP286SpatialBFMomentumEvaluation
          source state space direction
  lorentzMomentumInitial :
    ∀ space direction,
      (update 0).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
          space direction =
        sourceActionGeneratedLorentzSpatialBFMomentumEvaluation
          source state space direction
  scalarMomentumInitial :
    ∀ space direction,
      (update 0).canonical.scalar.temporalMomentumEvaluation
          space direction =
        sourceActionGeneratedScalarTemporalMomentumEvaluation
          source state space direction

theorem sourceActionGeneratedPrimitiveCanonicalSplitUpdate_realizes
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNinePrimitiveCanonicalSplitActionDevelopmentLaw
      source state
      (fun time =>
        sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source time state) := by
  exact
    { updateGenerated := rfl
      primitiveDevelopment :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_hasFrozenInputDevelopment
          source state
      canonicalDerivative :=
        sourceActionGeneratedJointCanonicalPhasePath_hasGeneratedDerivative
          source state
      coframeSync :=
        fun time space =>
          sourceActionGeneratedPrimitiveCanonicalSplitUpdate_coframe_sync
            source time state space
      multiplierSync :=
        fun time space =>
          sourceActionGeneratedPrimitiveCanonicalSplitUpdate_multiplier_sync
            source time state space
      temporalLorentzSync :=
        fun time space internalPair =>
          sourceActionGeneratedPrimitiveCanonicalSplitUpdate_temporalLorentz_sync
            source time state space internalPair
      spatialLorentzSync :=
        fun time space direction internalPair =>
          sourceActionGeneratedPrimitiveCanonicalSplitUpdate_spatialLorentz_sync
            source time state space direction internalPair
      temporalP286Sync :=
        fun time space =>
          sourceActionGeneratedPrimitiveCanonicalSplitUpdate_temporalP286_sync
            source time state space
      spatialP286Sync :=
        fun time space direction =>
          sourceActionGeneratedPrimitiveCanonicalSplitUpdate_spatialP286_sync
            source time state space direction
      scalarSync :=
        fun time space =>
          sourceActionGeneratedPrimitiveCanonicalSplitUpdate_scalar_sync
            source time state space
      matterSync :=
        fun time space =>
          sourceActionGeneratedPrimitiveCanonicalSplitUpdate_matter_sync
            source time state space
      conjugateMatterSync :=
        fun time space =>
          sourceActionGeneratedPrimitiveCanonicalSplitUpdate_conjugateMatter_sync
            source time state space
      p286MomentumInitial :=
        sourceActionGeneratedPrimitiveCanonicalSplitUpdate_p286Momentum_initial
          source state
      lorentzMomentumInitial :=
        sourceActionGeneratedPrimitiveCanonicalSplitUpdate_lorentzMomentum_initial
          source state
      scalarMomentumInitial :=
        sourceActionGeneratedPrimitiveCanonicalSplitUpdate_scalarMomentum_initial
          source state }

def positiveSourceActionGeneratedPrimitiveCanonicalSplitUpdate
    (time : ℝ) :
    StageNinePrimitiveCanonicalSplitActionState :=
  sourceActionGeneratedPrimitiveCanonicalSplitUpdate
    positiveSmoothUnifiedSource time positiveSourceTargetMatterCauchyState

theorem
    positiveSourceActionGeneratedPrimitiveCanonicalSplitUpdate_realizes :
    StageNinePrimitiveCanonicalSplitActionDevelopmentLaw
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
      positiveSourceActionGeneratedPrimitiveCanonicalSplitUpdate := by
  exact
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_realizes
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedPrimitiveCanonicalSplitDevelopment
