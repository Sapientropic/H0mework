import H0mework.Physics.ActionGeneration.JointPrimitiveCauchyPath

/-!
# S9-C3h123: source/action-generated joint primitive Cauchy update

C3h121 generates a complete local actual `U` at every selected spatial
contact and then restricts that actual to a physical-time Cauchy path.  This
module assembles those already generated pointwise actual paths into one
configuration-dependent update of the full instantaneous carrier:

```text
source + primitive Cauchy state
→ at every spatial contact: actual local action germ Uₓ
→ at every contact: canonical path t ↦ Uₓ|Σₜ
→ one full StageNineCauchyState update
→ complete all-space primitive tangent law
→ later equation/residual acceptance.
```

The update does not decode a residual, response coordinate, target endpoint,
preimage, range witness, quotient representative, or branch receipt.  Its
zero-time value is the action-prepared initial state: the gravity auxiliary
is generated as `B = II⁺(e)` while every other primitive field is retained.

This is a state-dependent pointwise local-action update.  It is not yet a
global holonomic development, an integral curve satisfying
`dU/dt = V(U(t))`, a semigroup, or a simultaneous on-shell solution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedJointPrimitiveCauchyPath
open StageNineSourceGeneratedMatterSpinActionUpdate
open DiracExteriorMatterAction

noncomputable section

set_option autoImplicit false

/-! ## Action-prepared initial state -/

/-- The algebraic gravity action generates `B = II⁺(e)` before the local
physical-time path starts.  No equation receipt is stored in this state. -/
def sourceActionGeneratedJointPrimitiveActionInitialState
    (state : StageNineCauchyState) :
    StageNineCauchyState :=
  { state with
    gravityAuxiliary :=
      fun space => actionGeneratedGravityAuxiliary state space }

/-- Assemble one full Cauchy update by reading, at each spatial point, the
origin of the local actual path generated at that same point. -/
def sourceActionGeneratedJointPrimitiveCauchyUpdate
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState) :
    StageNineCauchyState where
  coframe := fun space =>
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space time).coframe 0
  gravityConnection := fun space =>
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space time).gravityConnection 0
  gravityAuxiliary := fun space =>
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space time).gravityAuxiliary 0
  gravitySimplicityMultiplier := fun space =>
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space time).gravitySimplicityMultiplier 0
  gaugeConnection := fun space =>
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space time).gaugeConnection 0
  gaugeAuxiliary := fun space =>
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space time).gaugeAuxiliary 0
  scalar := fun space =>
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space time).scalar 0
  scalarVelocity := fun space =>
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space time).scalarVelocity 0
  matter := fun space =>
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space time).matter 0
  conjugateMatter := fun space =>
    (sourceActionGeneratedJointPrimitiveCauchyPath
      source state space time).conjugateMatter 0

/-- The all-space action velocity carried by the update. -/
def sourceActionGeneratedJointPrimitiveCauchyVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineJointPrimitiveActionVelocity :=
  sourceActionGeneratedJointPrimitiveActionVelocity source state space

/-! ## Zero-time and complete tangent laws -/

theorem sourceActionGeneratedJointPrimitiveCauchyUpdate_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    sourceActionGeneratedJointPrimitiveCauchyUpdate source 0 state =
      sourceActionGeneratedJointPrimitiveActionInitialState state := by
  apply StageNineCauchyState.ext
  · funext space
    exact
      sourceActionGeneratedJointPrimitiveCauchyPath_initialCoframe
        source state space
  · funext space
    exact
      sourceActionGeneratedJointPrimitiveCauchyPath_initialGravityConnection
        source state space
  · funext space
    exact
      sourceActionGeneratedJointPrimitiveCauchyPath_initialGravityAuxiliary
        source state space
  · funext space
    exact
      sourceActionGeneratedJointPrimitiveCauchyPath_initialMultiplier
        source state space
  · funext space
    exact
      sourceActionGeneratedJointPrimitiveCauchyPath_initialP286Connection
        source state space
  · funext space
    exact
      sourceActionGeneratedJointPrimitiveCauchyPath_initialP286Auxiliary
        source state space
  · funext space
    exact
      sourceActionGeneratedJointPrimitiveCauchyPath_initialScalar
        source state space
  · funext space
    exact
      sourceActionGeneratedJointPrimitiveCauchyPath_initialScalarVelocity
        source state space
  · funext space
    exact
      sourceActionGeneratedJointPrimitiveCauchyPath_initialMatter
        source state space
  · funext space
    exact
      sourceActionGeneratedJointPrimitiveCauchyPath_initialConjugateMatter
        source state space

theorem sourceActionGeneratedJointPrimitiveCauchyUpdate_coframeTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internal coordinate : LorentzianIndex) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source time state).coframe space internal coordinate)
        0 =
      (sourceActionGeneratedJointPrimitiveCauchyVelocity
        source state space).coframe internal coordinate :=
  sourceActionGeneratedJointPrimitiveCauchyPath_coframeTangent
    source state space internal coordinate

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_gravityConnectionTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    deriv
        (fun time : ℝ =>
          loweredLorentzConnectionCoefficient
            ((sourceActionGeneratedJointPrimitiveCauchyUpdate
              source time state).gravityConnection space)
            formDirection internalPair)
        0 =
      (sourceActionGeneratedJointPrimitiveCauchyVelocity
        source state space).gravityConnection
          formDirection internalPair :=
  sourceActionGeneratedJointPrimitiveCauchyPath_gravityConnectionTangent
    source state space formDirection internalPair

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_gravityAuxiliaryTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source time state).gravityAuxiliary
              space internalPair spacetimePair)
        0 =
      (sourceActionGeneratedJointPrimitiveCauchyVelocity
        source state space).gravityAuxiliary
          internalPair spacetimePair :=
  sourceActionGeneratedJointPrimitiveCauchyPath_gravityAuxiliaryTangent
    source state space internalPair spacetimePair

theorem sourceActionGeneratedJointPrimitiveCauchyUpdate_multiplierTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source time state).gravitySimplicityMultiplier
              space internalPair spacetimePair)
        0 =
      (sourceActionGeneratedJointPrimitiveCauchyVelocity
        source state space).gravitySimplicityMultiplier
          internalPair spacetimePair :=
  sourceActionGeneratedJointPrimitiveCauchyPath_multiplierTangent
    source state space internalPair spacetimePair

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_p286ConnectionTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) :
    deriv
        (fun time : ℝ =>
          p286CoordinateEquiv
            ((sourceActionGeneratedJointPrimitiveCauchyUpdate
              source time state).gaugeConnection space formDirection))
        0 =
      (sourceActionGeneratedJointPrimitiveCauchyVelocity
        source state space).p286Connection formDirection :=
  sourceActionGeneratedJointPrimitiveCauchyPath_p286ConnectionTangent
    source state space formDirection

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_p286AuxiliaryTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (pair : Fin 6) :
    deriv
        (fun time : ℝ =>
          p286CoordinateEquiv
            ((sourceActionGeneratedJointPrimitiveCauchyUpdate
              source time state).gaugeAuxiliary space pair))
        0 =
      (sourceActionGeneratedJointPrimitiveCauchyVelocity
        source state space).p286Auxiliary pair :=
  sourceActionGeneratedJointPrimitiveCauchyPath_p286AuxiliaryTangent
    source state space pair

theorem sourceActionGeneratedJointPrimitiveCauchyUpdate_scalarTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source time state).scalar space)
        0 =
      (sourceActionGeneratedJointPrimitiveCauchyVelocity
        source state space).scalar :=
  sourceActionGeneratedJointPrimitiveCauchyPath_scalarTangent
    source state space

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_scalarVelocityTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source time state).scalarVelocity space)
        0 =
      (sourceActionGeneratedJointPrimitiveCauchyVelocity
        source state space).scalarVelocity :=
  sourceActionGeneratedJointPrimitiveCauchyPath_scalarVelocityTangent
    source state space

theorem sourceActionGeneratedJointPrimitiveCauchyUpdate_matterTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    deriv
        (fun time : ℝ =>
          matterCoordinateEquiv
            ((sourceActionGeneratedJointPrimitiveCauchyUpdate
              source time state).matter space))
        0 =
      (sourceActionGeneratedJointPrimitiveCauchyVelocity
        source state space).matter :=
  sourceActionGeneratedJointPrimitiveCauchyPath_matterTangent
    source state space

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_conjugateMatterTangent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier) :
    deriv
        (fun time : ℝ =>
          (sourceActionGeneratedJointPrimitiveCauchyUpdate
            source time state).conjugateMatter space matter)
        0 =
      (sourceActionGeneratedJointPrimitiveCauchyVelocity
        source state space).conjugateMatter matter :=
  sourceActionGeneratedJointPrimitiveCauchyPath_conjugateMatterTangent
    source state space matter

/-! ## Bundled full-state update law -/

/-- One full instantaneous-carrier update generated by the family of local
actual action germs.  Equation and residual acceptance remain downstream. -/
structure StageNineJointPrimitiveActionCauchyUpdateLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (update : ℝ → StageNineCauchyState) : Prop where
  updateGenerated :
    update =
      fun time =>
        sourceActionGeneratedJointPrimitiveCauchyUpdate source time state
  pointwiseActualGenerated :
    ∀ space,
      StageNineJointPrimitiveActionCauchyPathLaw
        source state space
        (sourceActionGeneratedJointLocalActualLift source state space)
        (sourceActionGeneratedJointPrimitiveCauchyPath
          source state space)
  initial :
    update 0 =
      sourceActionGeneratedJointPrimitiveActionInitialState state
  coframeTangent :
    ∀ space internal coordinate,
      deriv
          (fun time : ℝ =>
            (update time).coframe space internal coordinate)
          0 =
        (sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).coframe internal coordinate
  gravityConnectionTangent :
    ∀ space formDirection internalPair,
      deriv
          (fun time : ℝ =>
            loweredLorentzConnectionCoefficient
              ((update time).gravityConnection space)
              formDirection internalPair)
          0 =
        (sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).gravityConnection
            formDirection internalPair
  gravityAuxiliaryTangent :
    ∀ space internalPair spacetimePair,
      deriv
          (fun time : ℝ =>
            (update time).gravityAuxiliary
              space internalPair spacetimePair)
          0 =
        (sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).gravityAuxiliary
            internalPair spacetimePair
  multiplierTangent :
    ∀ space internalPair spacetimePair,
      deriv
          (fun time : ℝ =>
            (update time).gravitySimplicityMultiplier
              space internalPair spacetimePair)
          0 =
        (sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).gravitySimplicityMultiplier
            internalPair spacetimePair
  p286ConnectionTangent :
    ∀ space formDirection,
      deriv
          (fun time : ℝ =>
            p286CoordinateEquiv
              ((update time).gaugeConnection space formDirection))
          0 =
        (sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).p286Connection formDirection
  p286AuxiliaryTangent :
    ∀ space pair,
      deriv
          (fun time : ℝ =>
            p286CoordinateEquiv
              ((update time).gaugeAuxiliary space pair))
          0 =
        (sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).p286Auxiliary pair
  scalarTangent :
    ∀ space,
      deriv (fun time : ℝ => (update time).scalar space) 0 =
        (sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).scalar
  scalarVelocityTangent :
    ∀ space,
      deriv (fun time : ℝ => (update time).scalarVelocity space) 0 =
        (sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).scalarVelocity
  matterTangent :
    ∀ space,
      deriv
          (fun time : ℝ =>
            matterCoordinateEquiv ((update time).matter space))
          0 =
        (sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).matter
  conjugateMatterTangent :
    ∀ space matter,
      deriv
          (fun time : ℝ =>
            (update time).conjugateMatter space matter)
          0 =
        (sourceActionGeneratedJointPrimitiveCauchyVelocity
          source state space).conjugateMatter matter

/-- Frontier theorem: every point of one full Cauchy update is generated by
its matching local actual action germ before any residual is read. -/
theorem sourceActionGeneratedJointPrimitiveCauchyUpdate_realizes
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineJointPrimitiveActionCauchyUpdateLaw
      source state
      (fun time =>
        sourceActionGeneratedJointPrimitiveCauchyUpdate source time state) := by
  exact
    { updateGenerated := rfl
      pointwiseActualGenerated :=
        sourceActionGeneratedJointPrimitiveCauchyPath_realizes source state
      initial :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_zero source state
      coframeTangent :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_coframeTangent
          source state
      gravityConnectionTangent :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_gravityConnectionTangent
          source state
      gravityAuxiliaryTangent :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_gravityAuxiliaryTangent
          source state
      multiplierTangent :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_multiplierTangent
          source state
      p286ConnectionTangent :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_p286ConnectionTangent
          source state
      p286AuxiliaryTangent :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_p286AuxiliaryTangent
          source state
      scalarTangent :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_scalarTangent
          source state
      scalarVelocityTangent :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_scalarVelocityTangent
          source state
      matterTangent :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_matterTangent
          source state
      conjugateMatterTangent :=
        sourceActionGeneratedJointPrimitiveCauchyUpdate_conjugateMatterTangent
          source state }

/-! ## P506/L0 positive specialization -/

def positiveSourceActionGeneratedJointPrimitiveCauchyUpdate
    (time : ℝ) :
    StageNineCauchyState :=
  sourceActionGeneratedJointPrimitiveCauchyUpdate
    positiveSmoothUnifiedSource time positiveSourceTargetMatterCauchyState

theorem positiveSourceActionGeneratedJointPrimitiveCauchyUpdate_realizes :
    StageNineJointPrimitiveActionCauchyUpdateLaw
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
      positiveSourceActionGeneratedJointPrimitiveCauchyUpdate := by
  exact sourceActionGeneratedJointPrimitiveCauchyUpdate_realizes
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
