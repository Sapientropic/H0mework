import H0mework.Physics.Exterior.JointActionCanonicalPhasePathLaw
import H0mework.Physics.ActionGeneration.JointPrimitiveCauchyUpdate

/-!
# S9-C3h124: source/action-generated joint primitive Cauchy development

C3h123 first assembles one whole-slice update `U` from the actual local action
germ generated at every matching spatial contact.  This module proves the
arbitrary-time derivative law of that same `U`:

```text
proof-free source + primitive Cauchy state
→ matching actual local action germs
→ whole-slice update U
→ dU/dt = V(source, input state) at every time
→ later equation/residual acceptance.
```

The right-hand side is the action velocity generated from the fixed input
state.  Thus this is a frozen-input affine action development.  It does not
yet prove `dU/dt = V(source, U(t))`, restart compatibility, a semigroup law,
global holonomicity, or simultaneous on-shell stationarity.  No residual,
response coordinate, endpoint, preimage, range witness, quotient
representative, equation receipt, or branch selector is used to generate or
differentiate `U`.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedJointPrimitiveCauchyDevelopment

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineJointActionCanonicalPhasePathLaw
open StageNineJointActionLocalActualLift
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineScalarActionCanonicalMomentumUpdate
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

/-! ## Canonical time-line normal forms -/

private theorem canonicalCauchySlicePoint_zeroSpace_eq_timeLine
    (time : ℝ) :
    canonicalCauchySlicePoint time 0 =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem actionGeneratedScalarLocalField_timeDerivative_at
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    fieldDirectionalDerivative
        (actionGeneratedScalarLocalField state space)
        point canonicalLorentzianTimeDirection =
      state.scalarVelocity space := by
  unfold fieldDirectionalDerivative actionGeneratedScalarLocalField
  rw [fderiv_const_add]
  rw [(actionGeneratedScalarLocalIncrement state space).hasFDerivAt.fderiv]
  simp [actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate, localBaseCoordinate,
    coordinateDirection, canonicalLorentzianTimeDirection,
    Fin.sum_univ_four]

/-! ## Arbitrary-time derivatives of the generated whole-slice update -/

theorem sourceActionGeneratedJointPrimitiveCauchyUpdate_coframeHasDerivAt
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (internal coordinate : LorentzianIndex) :
    HasDerivAt
        (fun candidate : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source candidate state).coframe space internal coordinate)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).coframe internal coordinate)
        time := by
  change HasDerivAt
    (fun _ : ℝ => state.coframe space internal coordinate) 0 time
  exact hasDerivAt_const time _

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_gravityConnectionHasDerivAt
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    HasDerivAt
        (fun candidate : ℝ =>
          loweredLorentzConnectionCoefficient
            ((sourceActionGeneratedJointPrimitiveCauchyUpdate
              source candidate state).gravityConnection space)
            formDirection internalPair)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).gravityConnection
            formDirection internalPair)
        time := by
  rw [show
    (fun candidate : ℝ =>
      loweredLorentzConnectionCoefficient
        ((sourceActionGeneratedJointPrimitiveCauchyUpdate
          source candidate state).gravityConnection space)
        formDirection internalPair) =
      fun candidate : ℝ =>
        loweredLorentzConnectionCoefficient
            (state.gravityConnection space) formDirection internalPair +
          candidate •
            actionGeneratedLorentzLocalConnectionJet state space
              canonicalLorentzianTimeDirection formDirection internalPair by
    funext candidate
    simp only [sourceActionGeneratedJointPrimitiveCauchyUpdate,
      sourceActionGeneratedJointPrimitiveCauchyPath,
      canonicalCauchyRestriction]
    change
      loweredLorentzConnectionCoefficient
          (actionGeneratedLorentzLocalConnection state space
            (canonicalCauchySlicePoint candidate 0))
          formDirection internalPair =
        _
    rw [actionGeneratedLorentzLocalConnection_loweredCoordinate]
    simp only [actionGeneratedLorentzLocalConnectionCoordinate,
      canonicalCauchySlicePoint_zeroSpace_eq_timeLine]
    rw [map_smul]
    congr 1
    simp [actionGeneratedLorentzLocalIncrement, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_four]]
  exact hasDerivAt_const_add_time_smul _ _ time

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_gravityAuxiliaryHasDerivAt
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    HasDerivAt
        (fun candidate : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source candidate state).gravityAuxiliary
              space internalPair spacetimePair)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).gravityAuxiliary
            internalPair spacetimePair)
        time := by
  change HasDerivAt
    (fun _ : ℝ =>
      actionGeneratedGravityAuxiliary state space
        internalPair spacetimePair)
    0 time
  exact hasDerivAt_const time _

theorem sourceActionGeneratedJointPrimitiveCauchyUpdate_multiplierHasDerivAt
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    HasDerivAt
        (fun candidate : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source candidate state).gravitySimplicityMultiplier
              space internalPair spacetimePair)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).gravitySimplicityMultiplier
            internalPair spacetimePair)
        time := by
  change HasDerivAt
    (fun _ : ℝ =>
      state.gravitySimplicityMultiplier space internalPair spacetimePair)
    0 time
  exact hasDerivAt_const time _

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_p286ConnectionHasDerivAt
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) :
    HasDerivAt
        (fun candidate : ℝ =>
          p286CoordinateEquiv
            ((sourceActionGeneratedJointPrimitiveCauchyUpdate
              source candidate state).gaugeConnection
                space formDirection))
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).p286Connection formDirection)
        time := by
  rw [show
    (fun candidate : ℝ =>
      p286CoordinateEquiv
        ((sourceActionGeneratedJointPrimitiveCauchyUpdate
          source candidate state).gaugeConnection space formDirection)) =
      fun candidate : ℝ =>
        p286CoordinateEquiv
            (state.gaugeConnection space formDirection) +
          candidate •
            sourceGeneratedP286ActionLocalConnectionJet source state space
              canonicalLorentzianTimeDirection formDirection by
    funext candidate
    simp only [sourceActionGeneratedJointPrimitiveCauchyUpdate,
      sourceActionGeneratedJointPrimitiveCauchyPath,
      canonicalCauchyRestriction]
    change
      p286CoordinateEquiv
          (sourceGeneratedP286ActionLocalConnection source state space
            (canonicalCauchySlicePoint candidate 0) formDirection) =
        _
    simp only [sourceGeneratedP286ActionLocalConnection,
      p286CoordinateEquiv.apply_symm_apply,
      sourceGeneratedP286ActionLocalConnectionCoordinate,
      canonicalCauchySlicePoint_zeroSpace_eq_timeLine]
    rw [map_smul]
    congr 1
    simp [sourceGeneratedP286ActionLocalIncrement, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_four]]
  exact hasDerivAt_const_add_time_smul _ _ time

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_p286AuxiliaryHasDerivAt
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (pair : Fin 6) :
    HasDerivAt
        (fun candidate : ℝ =>
          p286CoordinateEquiv
            ((sourceActionGeneratedJointPrimitiveCauchyUpdate
              source candidate state).gaugeAuxiliary space pair))
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).p286Auxiliary pair)
        time := by
  change HasDerivAt
    (fun _ : ℝ =>
      p286CoordinateEquiv (state.gaugeAuxiliary space pair))
    0 time
  exact hasDerivAt_const time _

theorem sourceActionGeneratedJointPrimitiveCauchyUpdate_scalarHasDerivAt
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    HasDerivAt
        (fun candidate : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source candidate state).scalar space)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).scalar)
        time := by
  rw [show
    (fun candidate : ℝ =>
      (sourceActionGeneratedJointPrimitiveCauchyUpdate
        source candidate state).scalar space) =
      fun candidate : ℝ =>
        state.scalar space +
          candidate • state.scalarVelocity space by
    funext candidate
    simp only [sourceActionGeneratedJointPrimitiveCauchyUpdate,
      sourceActionGeneratedJointPrimitiveCauchyPath,
      canonicalCauchyRestriction]
    change
      actionGeneratedScalarLocalField state space
          (canonicalCauchySlicePoint candidate 0) =
        _
    simp only [actionGeneratedScalarLocalField,
      canonicalCauchySlicePoint_zeroSpace_eq_timeLine]
    rw [map_smul]
    congr 1
    simp [actionGeneratedScalarLocalIncrement,
      actionGeneratedScalarLocalJetCoordinate, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_four]]
  exact hasDerivAt_const_add_time_smul _ _ time

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_scalarVelocityHasDerivAt
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    HasDerivAt
        (fun candidate : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source candidate state).scalarVelocity space)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).scalarVelocity)
        time := by
  rw [show
    (fun candidate : ℝ =>
      (sourceActionGeneratedJointPrimitiveCauchyUpdate
        source candidate state).scalarVelocity space) =
      fun _ : ℝ => state.scalarVelocity space by
    funext candidate
    change
      fieldDirectionalDerivative
          (actionGeneratedScalarLocalField state space)
          (canonicalCauchySlicePoint candidate 0)
          canonicalLorentzianTimeDirection =
        state.scalarVelocity space
    exact actionGeneratedScalarLocalField_timeDerivative_at
      state space (canonicalCauchySlicePoint candidate 0)]
  exact hasDerivAt_const time _

theorem sourceActionGeneratedJointPrimitiveCauchyUpdate_matterHasDerivAt
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    HasDerivAt
        (fun candidate : ℝ =>
          matterCoordinateEquiv
            ((sourceActionGeneratedJointPrimitiveCauchyUpdate
              source candidate state).matter space))
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).matter)
        time := by
  rw [show
    (fun candidate : ℝ =>
      matterCoordinateEquiv
        ((sourceActionGeneratedJointPrimitiveCauchyUpdate
          source candidate state).matter space)) =
      fun candidate : ℝ =>
        matterCoordinateEquiv (state.matter space) +
          candidate •
            actionGeneratedMatterLocalJetCoordinate state space
              canonicalLorentzianTimeDirection by
    funext candidate
    simp only [sourceActionGeneratedJointPrimitiveCauchyUpdate,
      sourceActionGeneratedJointPrimitiveCauchyPath,
      canonicalCauchyRestriction]
    change
      matterCoordinateEquiv
          (actionGeneratedMatterLocalField state space
            (canonicalCauchySlicePoint candidate 0)) =
        _
    simp only [actionGeneratedMatterLocalField,
      matterCoordinateEquiv.apply_symm_apply,
      actionGeneratedMatterLocalCoordinate,
      canonicalCauchySlicePoint_zeroSpace_eq_timeLine]
    rw [map_smul]
    congr 1
    simp [actionGeneratedMatterLocalIncrement, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_four]]
  exact hasDerivAt_const_add_time_smul _ _ time

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_conjugateMatterHasDerivAt
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier) :
    HasDerivAt
        (fun candidate : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source candidate state).conjugateMatter space matter)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).conjugateMatter matter)
        time := by
  rw [show
    (fun candidate : ℝ =>
      (sourceActionGeneratedJointPrimitiveCauchyUpdate
        source candidate state).conjugateMatter space matter) =
      fun candidate : ℝ =>
        state.conjugateMatter space matter +
          candidate •
            actionGeneratedConjugateMatterLocalJet state space
              canonicalLorentzianTimeDirection matter by
    funext candidate
    simp only [sourceActionGeneratedJointPrimitiveCauchyUpdate,
      sourceActionGeneratedJointPrimitiveCauchyPath,
      canonicalCauchyRestriction]
    change
      actionGeneratedConjugateMatterLocalField state space
          (canonicalCauchySlicePoint candidate 0) matter =
        _
    rw [actionGeneratedConjugateMatterLocalField_apply,
      canonicalCauchySlicePoint_zeroSpace_eq_timeLine, map_smul,
      actionGeneratedConjugateMatterLocalEvaluationIncrement_coordinateDirection]]
  exact hasDerivAt_const_add_time_smul _ _ time

/-! ## Bundled actual-first development law -/

/-- One whole-slice update is generated from matching local actual action
germs, and every primitive coordinate has its generated frozen-input action
derivative at every time.  Equation and residual acceptance remain
downstream. -/
structure StageNineJointPrimitiveFrozenInputActionCauchyDevelopmentLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (update : ℝ → StageNineCauchyState) : Prop where
  producer :
    StageNineJointPrimitiveActionCauchyUpdateLaw source state update
  coframeDerivative :
    ∀ time space internal coordinate,
      HasDerivAt
        (fun candidate : ℝ =>
          (update candidate).coframe space internal coordinate)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).coframe internal coordinate)
        time
  gravityConnectionDerivative :
    ∀ time space formDirection internalPair,
      HasDerivAt
        (fun candidate : ℝ =>
          loweredLorentzConnectionCoefficient
            ((update candidate).gravityConnection space)
            formDirection internalPair)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).gravityConnection
            formDirection internalPair)
        time
  gravityAuxiliaryDerivative :
    ∀ time space internalPair spacetimePair,
      HasDerivAt
        (fun candidate : ℝ =>
          (update candidate).gravityAuxiliary
            space internalPair spacetimePair)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).gravityAuxiliary
            internalPair spacetimePair)
        time
  multiplierDerivative :
    ∀ time space internalPair spacetimePair,
      HasDerivAt
        (fun candidate : ℝ =>
          (update candidate).gravitySimplicityMultiplier
            space internalPair spacetimePair)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).gravitySimplicityMultiplier
            internalPair spacetimePair)
        time
  p286ConnectionDerivative :
    ∀ time space formDirection,
      HasDerivAt
        (fun candidate : ℝ =>
          p286CoordinateEquiv
            ((update candidate).gaugeConnection space formDirection))
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).p286Connection formDirection)
        time
  p286AuxiliaryDerivative :
    ∀ time space pair,
      HasDerivAt
        (fun candidate : ℝ =>
          p286CoordinateEquiv
            ((update candidate).gaugeAuxiliary space pair))
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).p286Auxiliary pair)
        time
  scalarDerivative :
    ∀ time space,
      HasDerivAt
        (fun candidate : ℝ => (update candidate).scalar space)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).scalar)
        time
  scalarVelocityDerivative :
    ∀ time space,
      HasDerivAt
        (fun candidate : ℝ => (update candidate).scalarVelocity space)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).scalarVelocity)
        time
  matterDerivative :
    ∀ time space,
      HasDerivAt
        (fun candidate : ℝ =>
          matterCoordinateEquiv ((update candidate).matter space))
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).matter)
        time
  conjugateMatterDerivative :
    ∀ time space matter,
      HasDerivAt
        (fun candidate : ℝ =>
          (update candidate).conjugateMatter space matter)
        ((sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).conjugateMatter matter)
        time

/-- Frontier theorem: the source/action-generated whole-slice `U` carries
its complete frozen-input action derivative at every physical time. -/
theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_hasFrozenInputDevelopment
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineJointPrimitiveFrozenInputActionCauchyDevelopmentLaw
      source state
      (fun time =>
        sourceActionGeneratedJointPrimitiveCauchyUpdate
          source time state) := by
  exact
    { producer :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_realizes
          source state
      coframeDerivative :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_coframeHasDerivAt
          source state
      gravityConnectionDerivative :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_gravityConnectionHasDerivAt
          source state
      gravityAuxiliaryDerivative :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_gravityAuxiliaryHasDerivAt
          source state
      multiplierDerivative :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_multiplierHasDerivAt
          source state
      p286ConnectionDerivative :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_p286ConnectionHasDerivAt
          source state
      p286AuxiliaryDerivative :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_p286AuxiliaryHasDerivAt
          source state
      scalarDerivative :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_scalarHasDerivAt
          source state
      scalarVelocityDerivative :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_scalarVelocityHasDerivAt
          source state
      matterDerivative :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_matterHasDerivAt
          source state
      conjugateMatterDerivative :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_conjugateMatterHasDerivAt
          source state }

theorem
    positiveSourceActionGeneratedJointPrimitiveCauchyUpdate_hasFrozenInputDevelopment :
    StageNineJointPrimitiveFrozenInputActionCauchyDevelopmentLaw
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
      positiveSourceActionGeneratedJointPrimitiveCauchyUpdate := by
  exact
    sourceActionGeneratedJointPrimitiveCauchyUpdate_hasFrozenInputDevelopment
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedJointPrimitiveCauchyDevelopment
