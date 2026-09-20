import H0mework.Physics.CurrentAction.LorentzActualFirstJetLift
import H0mework.Physics.MatterCurrent.LinearPlebanskiPrimitiveCauchyUpdate

/-!
# Stage-9 current-state full-action Lorentz response germ

This module removes the frozen-input ambiguity exposed by C3h197 at the
infinitesimal producer boundary.  The underlying operators are defined for
every proof-free source and primitive Cauchy state.  Their full-action
authority is deliberately restricted to the identity-coframe carrier already
supported by the canonical Lorentz BF Legendre section and the
Dirac--Yukawa action laws.  At each spatial contact the existing action graph
first generates one local actual and then reads all ten canonical
time-response coordinates from that same actual:

```text
(source, current state, contact)
-> linear-Plebanski local actual
-> direct complete P286 response
-> temporal and complete primal-matter response
-> complete Lorentz BF response
-> one action-prepared origin and one complete current-state tangent.
```

The tangent is a function of the current state.  It is not frozen along a
finite-time path and it is not reconstructed from a residual.  This module
does not yet assert the existence of an integral curve `U'(t) = V(U(t))`.
For a raw state in this carrier the generated origin is action-prepared (in
particular its gravity auxiliary is normalized by the action), so no
unconditional `generated origin = input state` claim is made.

Semantically this is the complete full-action upgrade of the C3h131/C3h132
restart/origin-consistency architecture.  It does not introduce a second
notion of trajectory: zero-step identity is available only on the same
action-prepared carrier, and no positive-time iteration is claimed here.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzStateResponse

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGravityAuxiliaryVariation
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineJointActionCanonicalPhasePathLaw
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTimeVelocity
open StageNineMatterActionTemporalFirstGermResponse
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceActionGeneratedJointPrimitiveCauchyPath
open StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance stateResponseP286ModuleFinite :
    Module.Finite Real P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance stateResponseP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance stateResponseP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private theorem deriv_along_canonicalCauchyOrigin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (field : BasePoint -> V)
    (differentiable : DifferentiableAt Real field 0) :
    deriv
        (fun time : Real =>
          field (canonicalCauchySlicePoint time 0))
        0 =
      fieldDirectionalDerivative field 0
        canonicalLorentzianTimeDirection := by
  let line := fun time : Real =>
    time • coordinateDirection canonicalLorentzianTimeDirection
  have lineDerivative :
      HasDerivAt line
        (coordinateDirection canonicalLorentzianTimeDirection) 0 := by
    simpa [line] using
      (hasDerivAt_id (𝕜 := Real) 0).smul_const
        (coordinateDirection canonicalLorentzianTimeDirection)
  have outerDerivative :
      HasFDerivAt field (fderiv Real field 0) (line 0) := by
    simpa [line] using differentiable.hasFDerivAt
  have composed := outerDerivative.comp_hasDerivAt 0 lineDerivative
  unfold fieldDirectionalDerivative
  rw [show
    (fun time : Real =>
      field (canonicalCauchySlicePoint time 0)) =
        field ∘ line by
    funext time
    apply congrArg field
    ext direction
    fin_cases direction <;>
      simp [line, canonicalCauchySlicePoint, coordinateDirection,
        canonicalLorentzianTimeDirection, Fin.sum_univ_three]]
  exact composed.deriv

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 0 = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-! ## Same-actual path, prepared origin, and state-dependent tangent -/

/-- The canonical time path of the already generated complete Lorentz local
actual at one contact. -/
def currentCanonicalFullActionLorentzStateResponseLocalPath
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : Real) : StageNineCauchyState :=
  canonicalCauchyRestriction time
    (currentCanonicalFullActionLorentzActualFirstJetLift source current space)

/-- Assemble the local origins at all matching spatial contacts.  This is a
current-state action germ, not a finite-time flow. -/
def currentCanonicalFullActionLorentzStateResponseUpdate
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real) : StageNineCauchyState where
  coframe := fun space =>
    (currentCanonicalFullActionLorentzStateResponseLocalPath
      source current space time).coframe 0
  gravityConnection := fun space =>
    (currentCanonicalFullActionLorentzStateResponseLocalPath
      source current space time).gravityConnection 0
  gravityAuxiliary := fun space =>
    (currentCanonicalFullActionLorentzStateResponseLocalPath
      source current space time).gravityAuxiliary 0
  gravitySimplicityMultiplier := fun space =>
    (currentCanonicalFullActionLorentzStateResponseLocalPath
      source current space time).gravitySimplicityMultiplier 0
  gaugeConnection := fun space =>
    (currentCanonicalFullActionLorentzStateResponseLocalPath
      source current space time).gaugeConnection 0
  gaugeAuxiliary := fun space =>
    (currentCanonicalFullActionLorentzStateResponseLocalPath
      source current space time).gaugeAuxiliary 0
  scalar := fun space =>
    (currentCanonicalFullActionLorentzStateResponseLocalPath
      source current space time).scalar 0
  scalarVelocity := fun space =>
    (currentCanonicalFullActionLorentzStateResponseLocalPath
      source current space time).scalarVelocity 0
  matter := fun space =>
    (currentCanonicalFullActionLorentzStateResponseLocalPath
      source current space time).matter 0
  conjugateMatter := fun space =>
    (currentCanonicalFullActionLorentzStateResponseLocalPath
      source current space time).conjugateMatter 0

/-- The origin generated by the same action graph.  It is deliberately not
definitionally identified with an arbitrary raw input state. -/
def currentCanonicalFullActionLorentzPreparedOrigin
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) : StageNineCauchyState :=
  currentCanonicalFullActionLorentzStateResponseUpdate source current 0

/-- The complete current-state tangent.  Eight components are inherited from
the linear-Plebanski joint action germ.  The P286 and Lorentz auxiliary legs
are replaced by the two complete finite action-dual responses installed on
the same local actual. -/
def currentCanonicalFullActionLorentzStateResponse
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineJointPrimitiveActionVelocity :=
  { sourceActionGeneratedLinearPlebanskiJointPrimitiveActionVelocity
      source current space with
    gravityAuxiliary :=
      currentCanonicalFullActionLorentzAuxiliaryVelocity source current space
    p286Auxiliary :=
      p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentCanonicalFullActionBaseActual source current space)) }

/-- Linear-dual form of the adjoint component.  The primitive velocity record
stores only its underlying function, while the action law needs the linear
map itself. -/
def currentCanonicalFullActionLorentzStateAdjointResponse
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    Module.Dual Complex DiracExteriorMatterCarrier :=
  actionGeneratedConjugateMatterTimeDerivative current space

/-- Covariant primal-matter response selected by the same current state.
The primitive velocity record stores the corresponding raw derivative after
the temporal connection action is removed. -/
def currentCanonicalFullActionLorentzStateMatterCovariantResponse
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) : DiracExteriorMatterCarrier :=
  actionGeneratedMatterTimeCovariantDerivative current space

@[simp] theorem currentCanonicalFullActionLorentzStateResponseUpdate_zero
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    currentCanonicalFullActionLorentzStateResponseUpdate source current 0 =
      currentCanonicalFullActionLorentzPreparedOrigin source current :=
  rfl

/-- A state is action-prepared as soon as its only action-normalized field,
the gravity auxiliary, already agrees with the algebraic action image.  This
small abstract-state lemma avoids unfolding a large exact generated current
when establishing preparedness. -/
theorem actionInitialState_eq_self_of_gravityAuxiliaryPrepared
    (current : StageNineCauchyState)
    (gravityAuxiliaryPrepared :
      (fun space => actionGeneratedGravityAuxiliary current space) =
        current.gravityAuxiliary) :
    sourceActionGeneratedJointPrimitiveActionInitialState current =
      current := by
  apply StageNineCauchyState.ext
  · rfl
  · rfl
  · exact gravityAuxiliaryPrepared
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The zero-step image is exactly the established C3h126 action-preparation
map.  This is the typed bridge to the existing restart architecture. -/
theorem currentCanonicalFullActionLorentzPreparedOrigin_eq_actionInitialState
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    currentCanonicalFullActionLorentzPreparedOrigin source current =
      sourceActionGeneratedJointPrimitiveActionInitialState current := by
  apply StageNineCauchyState.ext
  · funext space
    change
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
        source current space 0).coframe 0 =
      current.coframe space
    exact
      sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_initialCoframe
        source current space
  · funext space
    change
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
        source current space 0).gravityConnection 0 =
      current.gravityConnection space
    exact
      sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_initialGravityConnection
        source current space
  · funext space
    change
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).gravityAuxiliary (canonicalCauchySlicePoint 0 0) =
      actionGeneratedGravityAuxiliary current space
    simpa using
      (currentCanonicalFullActionLorentzActualFirstJetLift_gravityAuxiliary_timeAxis
        source current space 0)
  · funext space
    change
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
        source current space 0).gravitySimplicityMultiplier 0 =
      current.gravitySimplicityMultiplier space
    exact
      sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_initialMultiplier
        source current space
  · funext space
    change
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
        source current space 0).gaugeConnection 0 =
      current.gaugeConnection space
    exact
      sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_initialP286Connection
        source current space
  · funext space pair
    change
      (currentP286CompleteActionResponseOperator source
        (currentCanonicalFullActionBaseActual source current space)
        |>.gaugeAuxiliary) (canonicalCauchySlicePoint 0 0) pair =
      current.gaugeAuxiliary space pair
    rw [canonicalCauchySlicePoint_zero_zero,
      currentP286CompleteActionResponseOperator_gaugeAuxiliary_origin]
    have initial :=
      sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_initialP286Auxiliary
        source current space
    exact congrFun initial pair
  · funext space
    change
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
        source current space 0).scalar 0 =
      current.scalar space
    exact
      sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_initialScalar
        source current space
  · funext space
    change
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
        source current space 0).scalarVelocity 0 =
      current.scalarVelocity space
    exact
      sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_initialScalarVelocity
        source current space
  · funext space
    change
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).matter (canonicalCauchySlicePoint 0 0) =
      current.matter space
    rw [canonicalCauchySlicePoint_zero_zero]
    change
      (actionGeneratedMatterCompleteFirstGermActual source
        (currentCanonicalGravityPreservingTemporalMatterActual source current
          space)).matter 0 =
      current.matter space
    rw [actionGeneratedMatterCompleteFirstGermActual_matter_origin]
    unfold currentCanonicalGravityPreservingTemporalMatterActual
    rw [actionGeneratedMatterTemporalFirstGermActual_matter_origin]
    unfold currentCanonicalGravityPreservingP286Actual
    rw [currentP286CompleteActionResponseOperator_matter]
    unfold currentCanonicalFullActionBaseActual
    exact currentFullSynchronizedCompleteP286BaseActual_matter_origin
      source current space
  · funext space
    change
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
        source current space 0).conjugateMatter 0 =
      current.conjugateMatter space
    exact
      sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_initialConjugateMatter
        source current space

/-- The complete C3h198 germ and the established C3h126 current-state Euler
update share exactly the same action-prepared origin.  No positive-time
equality is asserted: their actual paths and complete response coordinates
are not the same away from this common origin. -/
theorem
    currentCanonicalFullActionLorentzStateResponseUpdate_zero_eq_jointPrimitiveCauchyUpdate_zero
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    currentCanonicalFullActionLorentzStateResponseUpdate source current 0 =
      sourceActionGeneratedJointPrimitiveCauchyUpdate source 0 current := by
  rw [currentCanonicalFullActionLorentzStateResponseUpdate_zero,
    currentCanonicalFullActionLorentzPreparedOrigin_eq_actionInitialState,
    sourceActionGeneratedJointPrimitiveCauchyUpdate_zero]

/-- Exactly as in C3h131, zero-step identity holds only on the
action-prepared carrier. -/
theorem currentCanonicalFullActionLorentzStateResponseUpdate_zero_of_actionPrepared
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (actionPrepared :
      sourceActionGeneratedJointPrimitiveActionInitialState current =
        current) :
    currentCanonicalFullActionLorentzStateResponseUpdate source current 0 =
      current := by
  rw [currentCanonicalFullActionLorentzStateResponseUpdate_zero,
    currentCanonicalFullActionLorentzPreparedOrigin_eq_actionInitialState,
    actionPrepared]

@[simp] theorem currentCanonicalFullActionLorentzStateResponse_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzStateResponse source current
      space).gravityAuxiliary =
      currentCanonicalFullActionLorentzAuxiliaryVelocity source current
        space :=
  rfl

@[simp] theorem currentCanonicalFullActionLorentzStateResponse_p286Auxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzStateResponse source current
      space).p286Auxiliary =
      p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentCanonicalFullActionBaseActual source current space)) :=
  rfl

@[simp] theorem currentCanonicalFullActionLorentzStateResponse_matter
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzStateResponse source current
      space).matter =
      matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity current space) := by
  rfl

@[simp] theorem currentCanonicalFullActionLorentzStateResponse_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzStateResponse source current
      space).conjugateMatter =
      currentCanonicalFullActionLorentzStateAdjointResponse current space := by
  rfl

/-! ## Complete same-actual canonical time jet -/

theorem currentCanonicalFullActionLorentzStateResponseUpdate_coframeTangent
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internal coordinate : LorentzianIndex) :
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).coframe space internal coordinate)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).coframe internal coordinate := by
  change
    deriv
        (fun time : Real =>
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
            source current space time).coframe 0 internal coordinate)
        0 =
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveActionVelocity
        source current space).coframe internal coordinate
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_coframeTangent
      source current space internal coordinate

theorem
    currentCanonicalFullActionLorentzStateResponseUpdate_gravityConnectionTangent
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    deriv
        (fun time : Real =>
          loweredLorentzConnectionCoefficient
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).gravityConnection space)
            formDirection internalPair)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).gravityConnection formDirection internalPair := by
  change
    deriv
        (fun time : Real =>
          loweredLorentzConnectionCoefficient
            ((sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
              source current space time).gravityConnection 0)
            formDirection internalPair)
        0 =
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveActionVelocity
        source current space).gravityConnection formDirection internalPair
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_gravityConnectionTangent
      source current space formDirection internalPair

theorem currentCanonicalFullActionLorentzStateResponseUpdate_multiplierTangent
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).gravitySimplicityMultiplier
              space internalPair spacetimePair)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).gravitySimplicityMultiplier internalPair spacetimePair := by
  change
    deriv
        (fun time : Real =>
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
            source current space time).gravitySimplicityMultiplier
              0 internalPair spacetimePair)
        0 =
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveActionVelocity
        source current space).gravitySimplicityMultiplier
          internalPair spacetimePair
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_multiplierTangent
      source current space internalPair spacetimePair

theorem
    currentCanonicalFullActionLorentzStateResponseUpdate_p286ConnectionTangent
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) :
    deriv
        (fun time : Real =>
          p286CoordinateEquiv
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).gaugeConnection space formDirection))
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).p286Connection formDirection := by
  change
    deriv
        (fun time : Real =>
          p286CoordinateEquiv
            ((sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
              source current space time).gaugeConnection 0 formDirection))
        0 =
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveActionVelocity
        source current space).p286Connection formDirection
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_p286ConnectionTangent
      source current space formDirection

theorem currentCanonicalFullActionLorentzStateResponseUpdate_scalarTangent
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).scalar space)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).scalar := by
  change
    deriv
        (fun time : Real =>
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
            source current space time).scalar 0)
        0 =
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveActionVelocity
        source current space).scalar
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_scalarTangent
      source current space

theorem
    currentCanonicalFullActionLorentzStateResponseUpdate_scalarVelocityTangent
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).scalarVelocity space)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).scalarVelocity := by
  change
    deriv
        (fun time : Real =>
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
            source current space time).scalarVelocity 0)
        0 =
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveActionVelocity
        source current space).scalarVelocity
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_scalarVelocityTangent
      source current space

theorem
    currentCanonicalFullActionLorentzStateResponseUpdate_conjugateMatterTangent
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier) :
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).conjugateMatter space matter)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).conjugateMatter matter := by
  change
    deriv
        (fun time : Real =>
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
            source current space time).conjugateMatter 0 matter)
        0 =
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveActionVelocity
        source current space).conjugateMatter matter
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_conjugateMatterTangent
      source current space matter

theorem
    currentCanonicalFullActionLorentzStateResponseUpdate_gravityAuxiliaryTangent
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).gravityAuxiliary
              space internalPair spacetimePair)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).gravityAuxiliary internalPair spacetimePair := by
  rw [show
    (fun time : Real =>
      (currentCanonicalFullActionLorentzStateResponseUpdate source current
        time).gravityAuxiliary space internalPair spacetimePair) =
      fun time : Real =>
        (actionGeneratedGravityAuxiliary current space +
          time • currentCanonicalFullActionLorentzAuxiliaryVelocity source
            current space) internalPair spacetimePair by
    funext time
    exact congrFun
      (congrFun
        (currentCanonicalFullActionLorentzActualFirstJetLift_gravityAuxiliary_timeAxis
          source current space time)
        internalPair)
      spacetimePair]
  change
    deriv
        (fun time : Real =>
          actionGeneratedGravityAuxiliary current space internalPair
              spacetimePair +
            time •
              currentCanonicalFullActionLorentzAuxiliaryVelocity source
                current space internalPair spacetimePair)
        0 =
      currentCanonicalFullActionLorentzAuxiliaryVelocity source current
        space internalPair spacetimePair
  exact
    (hasDerivAt_const_add_time_smul
      (actionGeneratedGravityAuxiliary current space internalPair
        spacetimePair)
      (currentCanonicalFullActionLorentzAuxiliaryVelocity source current
        space internalPair spacetimePair)
      (0 : Real)).deriv

theorem
    currentCanonicalFullActionLorentzStateResponseUpdate_p286Auxiliary_normalForm
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : Real)
    (pair : Fin 6) :
    p286CoordinateEquiv
        ((currentCanonicalFullActionLorentzStateResponseUpdate source current
          time).gaugeAuxiliary space pair) =
      currentP286OriginAuxiliaryCoordinate
          (currentCanonicalFullActionBaseActual source current space) pair +
        time •
          p286SpatialAuxiliaryVelocityEmbedding
            (currentP286SpatialAuxiliaryVelocity source
              (currentCanonicalFullActionBaseActual source current space))
            pair := by
  change
    p286CoordinateEquiv
        ((currentP286CompleteActionResponseOperator source
          (currentCanonicalFullActionBaseActual source current space)
          |>.gaugeAuxiliary)
          (canonicalCauchySlicePoint time 0) pair) =
      _
  rw [show
    p286CoordinateEquiv
        ((currentP286CompleteActionResponseOperator source
          (currentCanonicalFullActionBaseActual source current space)
          |>.gaugeAuxiliary)
          (canonicalCauchySlicePoint time 0) pair) =
      currentP286CompleteResponseAuxiliaryCoordinate source
          (currentCanonicalFullActionBaseActual source current space)
          (canonicalCauchySlicePoint time 0) pair by
    exact congrFun
      (currentP286CompleteActionResponseOperator_auxiliaryCoordinate source
        (currentCanonicalFullActionBaseActual source current space)
        (canonicalCauchySlicePoint time 0))
      pair]
  simp [currentP286CompleteResponseAuxiliaryCoordinate,
    currentP286CanonicalGaussRadialAuxiliaryProfile,
    symmetricP286GaussRadialAuxiliaryProfile,
    canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
    Fin.sum_univ_three]

theorem
    currentCanonicalFullActionLorentzStateResponseUpdate_p286AuxiliaryTangent
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (pair : Fin 6) :
    deriv
        (fun time : Real =>
          p286CoordinateEquiv
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).gaugeAuxiliary space pair))
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).p286Auxiliary pair := by
  rw [show
    (fun time : Real =>
      p286CoordinateEquiv
        ((currentCanonicalFullActionLorentzStateResponseUpdate source current
          time).gaugeAuxiliary space pair)) =
      fun time : Real =>
        currentP286OriginAuxiliaryCoordinate
            (currentCanonicalFullActionBaseActual source current space) pair +
          time •
            p286SpatialAuxiliaryVelocityEmbedding
              (currentP286SpatialAuxiliaryVelocity source
                (currentCanonicalFullActionBaseActual source current space))
              pair by
    funext time
    exact
      currentCanonicalFullActionLorentzStateResponseUpdate_p286Auxiliary_normalForm
        source current space time pair]
  change
    deriv
        (fun time : Real =>
          currentP286OriginAuxiliaryCoordinate
              (currentCanonicalFullActionBaseActual source current space)
              pair +
            time •
              p286SpatialAuxiliaryVelocityEmbedding
                (currentP286SpatialAuxiliaryVelocity source
                  (currentCanonicalFullActionBaseActual source current space))
                pair)
        0 =
      p286SpatialAuxiliaryVelocityEmbedding
          (currentP286SpatialAuxiliaryVelocity source
            (currentCanonicalFullActionBaseActual source current space))
          pair
  exact
    (hasDerivAt_const_add_time_smul
      (currentP286OriginAuxiliaryCoordinate
        (currentCanonicalFullActionBaseActual source current space) pair :
          P286CoordinateCarrier)
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentCanonicalFullActionBaseActual source current space)) pair)
      (0 : Real)).deriv

theorem currentCanonicalFullActionLorentzStateResponseUpdate_matterTangent
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    deriv
        (fun time : Real =>
          matterCoordinateEquiv
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).matter space))
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).matter := by
  let base := currentCanonicalFullActionBaseActual source current space
  let p286 := currentCanonicalGravityPreservingP286Actual source current space
  let temporal :=
    currentCanonicalGravityPreservingTemporalMatterActual source current space
  let complete := currentCanonicalGravityPreservingActual source current space
  let final :=
    currentCanonicalFullActionLorentzActualFirstJetLift source current space
  have baseSmooth : base.Smooth := by
    exact
      sourceActionGeneratedLinearPlebanskiJointLocalActualLift_smooth
        source current space
  have p286Smooth : p286.Smooth := by
    exact currentP286CompleteActionResponseOperator_smooth source base
      baseSmooth
  have temporalSmooth : temporal.Smooth := by
    exact actionGeneratedMatterTemporalFirstGermActual_smooth source p286
      p286Smooth
  have finalSmooth : final.Smooth :=
    currentCanonicalFullActionLorentzActualFirstJetLift_smooth source current
      space
  have finalDifferentiable : DifferentiableAt Real
      (fun point => matterCoordinateEquiv (final.matter point)) 0 :=
    (finalSmooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt
  have baseDifferentiable : DifferentiableAt Real
      (fun point => matterCoordinateEquiv (base.matter point)) 0 :=
    (baseSmooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt
  calc
    deriv
        (fun time : Real =>
          matterCoordinateEquiv
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).matter space))
        0 =
        deriv
          (fun time : Real =>
            matterCoordinateEquiv
              (final.matter (canonicalCauchySlicePoint time 0)))
          0 := by rfl
    _ = fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (final.matter point)) 0
          canonicalLorentzianTimeDirection :=
      deriv_along_canonicalCauchyOrigin _ finalDifferentiable
    _ = fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (complete.matter point)) 0
          canonicalLorentzianTimeDirection := by
      rfl
    _ = fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (temporal.matter point)) 0
          canonicalLorentzianTimeDirection := by
      exact actionGeneratedMatterCompleteFirstGermActual_matter_firstJet_origin
        source temporal temporalSmooth canonicalLorentzianTimeDirection
    _ = fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (p286.matter point)) 0
          canonicalLorentzianTimeDirection := by
      exact actionGeneratedMatterTemporalFirstGermActual_matter_firstJet_origin
        source p286 p286Smooth canonicalLorentzianTimeDirection
    _ = fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (base.matter point)) 0
          canonicalLorentzianTimeDirection := by
      rfl
    _ = deriv
          (fun time : Real =>
            matterCoordinateEquiv
              (base.matter (canonicalCauchySlicePoint time 0)))
          0 :=
      (deriv_along_canonicalCauchyOrigin _ baseDifferentiable).symm
    _ = (currentCanonicalFullActionLorentzStateResponse source current
          space).matter := by
      change
        deriv
            (fun time : Real =>
              matterCoordinateEquiv
                ((sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
                  source current space time).matter 0))
            0 =
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveActionVelocity
            source current space).matter
      exact
        sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_matterTangent
          source current space

/-! ## Action provenance and uniqueness -/

/-- The Lorentz auxiliary component is the fixed BF-Legendre realization of
the complete 18-coordinate action dual. -/
theorem currentCanonicalFullActionLorentzStateResponse_lorentzPairing
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    gravityAuxiliaryHodgePairingPolynomial 1
        ((currentCanonicalFullActionLorentzStateResponse source current
          space).gravityAuxiliary)
        (lorentzConnectionExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalLorentzSpatialBivectorOneForm direction)) =
      currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source
        current space direction := by
  rw [currentCanonicalFullActionLorentzStateResponse_gravityAuxiliary]
  exact currentCanonicalFullActionLorentzAuxiliaryVelocity_pairing
    source current space direction

/-- The P286 auxiliary component solves the direct action dual generated by
the same action-prepared base actual. -/
theorem currentCanonicalFullActionLorentzStateResponse_p286Response
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    p286SpatialBFLegendreDualOperator
        (currentP286SpatialAuxiliaryVelocity source
          (currentCanonicalFullActionBaseActual source current space)) =
      currentP286SpatialActionTarget source
        (currentCanonicalFullActionBaseActual source current space) :=
  currentP286SpatialAuxiliaryVelocity_response _ _

/-- The adjoint component is the unique temporal response of the current
state; no branch selector or residual witness is accepted. -/
theorem currentCanonicalFullActionLorentzStateResponse_adjointLaw
    (_source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    IdentityCoframeConjugateMatterTimeActionLaw current space
      (currentCanonicalFullActionLorentzStateAdjointResponse current
        space) := by
  unfold currentCanonicalFullActionLorentzStateAdjointResponse
  exact actionGeneratedConjugateMatterTimeDerivative_satisfies_actionLaw
    current space

theorem currentCanonicalFullActionLorentzStateResponse_primalLaw
    (_source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    IdentityCoframeMatterTimeActionLaw current space
      (currentCanonicalFullActionLorentzStateMatterCovariantResponse current
        space) := by
  unfold currentCanonicalFullActionLorentzStateMatterCovariantResponse
  exact actionGeneratedMatterTimeCovariantDerivative_satisfies_actionLaw
    current space

theorem currentCanonicalFullActionLorentzStateResponse_primalUnique
    (_source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (candidate : DiracExteriorMatterCarrier)
    (candidateLaw :
      IdentityCoframeMatterTimeActionLaw current space candidate) :
    candidate =
      currentCanonicalFullActionLorentzStateMatterCovariantResponse current
        space := by
  unfold currentCanonicalFullActionLorentzStateMatterCovariantResponse
  exact identityCoframeMatterTimeActionLaw_unique
    current space candidate _ candidateLaw
    (actionGeneratedMatterTimeCovariantDerivative_satisfies_actionLaw
      current space)

theorem currentCanonicalFullActionLorentzStateResponse_adjointUnique
    (_source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (candidate : Module.Dual Complex DiracExteriorMatterCarrier)
    (candidateLaw :
      IdentityCoframeConjugateMatterTimeActionLaw current space candidate) :
    candidate =
      currentCanonicalFullActionLorentzStateAdjointResponse current
        space := by
  unfold currentCanonicalFullActionLorentzStateAdjointResponse
  exact identityCoframeConjugateMatterTimeActionLaw_unique
    current space candidate _ candidateLaw
    (actionGeneratedConjugateMatterTimeDerivative_satisfies_actionLaw
      current space)

/-! ## Bundled positive current-state response law -/

/-- Role-separated authority for the positive infinitesimal step on the
identity-coframe carrier.  This is an update law, not an integral-curve or
constraint-propagation receipt. -/
structure StageNineCurrentCanonicalFullActionLorentzStateResponseLaw
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) : Prop where
  identityCoframeCarrier : forall space, current.coframe space = 1
  localActualGenerated : forall space,
    currentCanonicalFullActionLorentzActualFirstJetLift source current space =
      { currentCanonicalGravityPreservingActual source current space with
        gravityAuxiliary := fun point =>
          (currentCanonicalGravityPreservingActual source current
            space).gravityAuxiliary point +
          localBaseCoordinate canonicalLorentzianTimeDirection point •
            currentCanonicalFullActionLorentzAuxiliaryVelocity source current
              space }
  localActualSmooth : forall space,
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
      space).Smooth
  localActualNondegenerate : forall space,
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
      space).Nondegenerate
  localPathGenerated : forall space time,
    currentCanonicalFullActionLorentzStateResponseLocalPath source current
        space time =
      canonicalCauchyRestriction time
        (currentCanonicalFullActionLorentzActualFirstJetLift source current
          space)
  updateGenerated :
    currentCanonicalFullActionLorentzStateResponseUpdate source current =
      fun time =>
        { coframe := fun space =>
            (currentCanonicalFullActionLorentzStateResponseLocalPath
              source current space time).coframe 0
          gravityConnection := fun space =>
            (currentCanonicalFullActionLorentzStateResponseLocalPath
              source current space time).gravityConnection 0
          gravityAuxiliary := fun space =>
            (currentCanonicalFullActionLorentzStateResponseLocalPath
              source current space time).gravityAuxiliary 0
          gravitySimplicityMultiplier := fun space =>
            (currentCanonicalFullActionLorentzStateResponseLocalPath
              source current space time).gravitySimplicityMultiplier 0
          gaugeConnection := fun space =>
            (currentCanonicalFullActionLorentzStateResponseLocalPath
              source current space time).gaugeConnection 0
          gaugeAuxiliary := fun space =>
            (currentCanonicalFullActionLorentzStateResponseLocalPath
              source current space time).gaugeAuxiliary 0
          scalar := fun space =>
            (currentCanonicalFullActionLorentzStateResponseLocalPath
              source current space time).scalar 0
          scalarVelocity := fun space =>
            (currentCanonicalFullActionLorentzStateResponseLocalPath
              source current space time).scalarVelocity 0
          matter := fun space =>
            (currentCanonicalFullActionLorentzStateResponseLocalPath
              source current space time).matter 0
          conjugateMatter := fun space =>
            (currentCanonicalFullActionLorentzStateResponseLocalPath
              source current space time).conjugateMatter 0 }
  preparedOriginGenerated :
    currentCanonicalFullActionLorentzStateResponseUpdate source current 0 =
      currentCanonicalFullActionLorentzPreparedOrigin source current
  preparedOriginIsEstablishedActionInitial :
    currentCanonicalFullActionLorentzPreparedOrigin source current =
      sourceActionGeneratedJointPrimitiveActionInitialState current
  zeroStepIdentityOnActionPrepared :
    sourceActionGeneratedJointPrimitiveActionInitialState current =
        current ->
      currentCanonicalFullActionLorentzStateResponseUpdate source current 0 =
        current
  coframeTimeJet : forall space internal coordinate,
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).coframe space internal coordinate)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).coframe internal coordinate
  gravityConnectionTimeJet : forall space formDirection internalPair,
    deriv
        (fun time : Real =>
          loweredLorentzConnectionCoefficient
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).gravityConnection space)
            formDirection internalPair)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).gravityConnection formDirection internalPair
  gravityAuxiliaryTimeJet : forall space internalPair spacetimePair,
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).gravityAuxiliary
              space internalPair spacetimePair)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).gravityAuxiliary internalPair spacetimePair
  multiplierTimeJet : forall space internalPair spacetimePair,
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).gravitySimplicityMultiplier
              space internalPair spacetimePair)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).gravitySimplicityMultiplier internalPair spacetimePair
  p286ConnectionTimeJet : forall space formDirection,
    deriv
        (fun time : Real =>
          p286CoordinateEquiv
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).gaugeConnection space formDirection))
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).p286Connection formDirection
  p286AuxiliaryTimeJet : forall space pair,
    deriv
        (fun time : Real =>
          p286CoordinateEquiv
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).gaugeAuxiliary space pair))
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).p286Auxiliary pair
  scalarTimeJet : forall space,
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).scalar space)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).scalar
  scalarVelocityTimeJet : forall space,
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).scalarVelocity space)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).scalarVelocity
  matterTimeJet : forall space,
    deriv
        (fun time : Real =>
          matterCoordinateEquiv
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).matter space))
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).matter
  conjugateMatterTimeJet : forall space matter,
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source
            current time).conjugateMatter space matter)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).conjugateMatter matter
  lorentzResponse : forall space direction,
    gravityAuxiliaryHodgePairingPolynomial 1
        ((currentCanonicalFullActionLorentzStateResponse source current
          space).gravityAuxiliary)
        (lorentzConnectionExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalLorentzSpatialBivectorOneForm direction)) =
      currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source
        current space direction
  p286Response : forall space,
    p286SpatialBFLegendreDualOperator
        (currentP286SpatialAuxiliaryVelocity source
          (currentCanonicalFullActionBaseActual source current space)) =
      currentP286SpatialActionTarget source
        (currentCanonicalFullActionBaseActual source current space)
  primalProjection : forall space,
    (currentCanonicalFullActionLorentzStateResponse source current
      space).matter =
      matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity current space)
  primalResponse : forall space,
    IdentityCoframeMatterTimeActionLaw current space
      (currentCanonicalFullActionLorentzStateMatterCovariantResponse current
        space)
  primalUnique : forall space candidate,
    IdentityCoframeMatterTimeActionLaw current space candidate ->
      candidate =
        currentCanonicalFullActionLorentzStateMatterCovariantResponse current
          space
  adjointProjection : forall space,
    (currentCanonicalFullActionLorentzStateResponse source current
      space).conjugateMatter =
      currentCanonicalFullActionLorentzStateAdjointResponse current space
  adjointResponse : forall space,
    IdentityCoframeConjugateMatterTimeActionLaw current space
      (currentCanonicalFullActionLorentzStateAdjointResponse current space)
  adjointUnique : forall space candidate,
    IdentityCoframeConjugateMatterTimeActionLaw current space candidate ->
      candidate =
        currentCanonicalFullActionLorentzStateAdjointResponse current space

/-- First C3h198 frontier theorem: identity-coframe current data generate an
action-prepared local actual and a branch-free complete response function of
that current state.  No finite-time trajectory is claimed here. -/
theorem currentCanonicalFullActionLorentzStateResponse_realizes
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (identityCoframe : forall space, current.coframe space = 1) :
    StageNineCurrentCanonicalFullActionLorentzStateResponseLaw source
      current where
  identityCoframeCarrier := identityCoframe
  localActualGenerated := fun _ => rfl
  localActualSmooth :=
    currentCanonicalFullActionLorentzActualFirstJetLift_smooth source current
  localActualNondegenerate := fun space =>
    currentCanonicalFullActionLorentzActualFirstJetLift_nondegenerate
      source current space (identityCoframe space)
  localPathGenerated := fun _ _ => rfl
  updateGenerated := rfl
  preparedOriginGenerated :=
    currentCanonicalFullActionLorentzStateResponseUpdate_zero source current
  preparedOriginIsEstablishedActionInitial :=
    currentCanonicalFullActionLorentzPreparedOrigin_eq_actionInitialState
      source current
  zeroStepIdentityOnActionPrepared :=
    currentCanonicalFullActionLorentzStateResponseUpdate_zero_of_actionPrepared
      source current
  coframeTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_coframeTangent
      source current
  gravityConnectionTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_gravityConnectionTangent
      source current
  gravityAuxiliaryTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_gravityAuxiliaryTangent
      source current
  multiplierTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_multiplierTangent
      source current
  p286ConnectionTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_p286ConnectionTangent
      source current
  p286AuxiliaryTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_p286AuxiliaryTangent
      source current
  scalarTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_scalarTangent source
      current
  scalarVelocityTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_scalarVelocityTangent
      source current
  matterTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_matterTangent source
      current
  conjugateMatterTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_conjugateMatterTangent
      source current
  lorentzResponse :=
    currentCanonicalFullActionLorentzStateResponse_lorentzPairing source
      current
  p286Response :=
    currentCanonicalFullActionLorentzStateResponse_p286Response source current
  primalProjection :=
    currentCanonicalFullActionLorentzStateResponse_matter source current
  primalResponse :=
    currentCanonicalFullActionLorentzStateResponse_primalLaw source current
  primalUnique := fun space candidate candidateLaw =>
    currentCanonicalFullActionLorentzStateResponse_primalUnique source
      current space candidate candidateLaw
  adjointProjection :=
    currentCanonicalFullActionLorentzStateResponse_conjugateMatter source
      current
  adjointResponse :=
    currentCanonicalFullActionLorentzStateResponse_adjointLaw source current
  adjointUnique := fun space candidate candidateLaw =>
    currentCanonicalFullActionLorentzStateResponse_adjointUnique source
      current space candidate candidateLaw

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzStateResponse
