import H0mework.Physics.GaugeAction.FullSynchronizedCompleteP286ActionResponseOperator
import H0mework.Physics.MatterCurrent.LinearPlebanskiSynchronizedLocalActualLift

/-!
# Stage-9 current full-synchronized complete-P286 primitive Cauchy update

This module continues the full-action-dual-first dependency graph at every
spatial contact of an arbitrary current Cauchy state:

```text
(proof-free source, current Cauchy state, global spatial contact)
→ C3h153 linear-Plebanski base actual
→ full synchronized action response
→ complete P286 response generated from that full intermediate actual
→ canonical local path of the generated whole actual
→ one whole-slice primitive update.
```

The zero-time result is a separately generated response state assembled from
the local full-response actuals.  It is not identified with the input state
or with an action-prepared copy of that state.

Only the P286 auxiliary first jet currently has a generic bridge back to an
action-generated response: it is the unique BF-Legendre velocity generated
from the same full intermediate actual at the same contact.  Other canonical
path derivatives remain readouts of the generated actual until their
full-action response bridges are proved; this module does not package them
as a producer velocity.

No residual, endpoint, target field, velocity witness, charge witness,
coefficient, inverse witness, branch choice, stationarity receipt, or
equation certificate is accepted by a constructor.  This instantaneous
update is not yet a restart, autonomous evolution law, flow, or semigroup.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdate

open StageNineCanonicalCauchyState
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineFullSynchronizedCompleteP286ActionResponseOperator
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance currentFullUpdateP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance currentFullUpdateP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance currentFullUpdateP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Full-action-dual-first local actual -/

/-- The C3h153 base actual generated from the current state at one global
spatial contact. -/
def currentFullSynchronizedCompleteP286BaseActual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedLinearPlebanskiJointLocalActualLift source current space

@[simp] theorem currentFullSynchronizedCompleteP286BaseActual_matter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentFullSynchronizedCompleteP286BaseActual source current space).matter
        0 =
      current.matter space := by
  unfold currentFullSynchronizedCompleteP286BaseActual
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift
  exact
    sourceActionGeneratedJointLocalActualLift_initialMatter
      source current space

@[simp] theorem
    currentFullSynchronizedCompleteP286BaseActual_conjugateMatter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentFullSynchronizedCompleteP286BaseActual source current
      space).conjugateMatter 0 =
      current.conjugateMatter space := by
  unfold currentFullSynchronizedCompleteP286BaseActual
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift
  exact
    sourceActionGeneratedJointLocalActualLift_initialConjugateMatter
      source current space

/-- The full synchronized intermediate actual.  This is where the current
matter spin, Einstein--Cartan contorsion, resynchronized matter germs,
non-gravity coframe stress, multiplier, and curvature are generated. -/
def currentFullSynchronizedResponseActual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  fullSynchronizedActionResponseOperator source
    (currentFullSynchronizedCompleteP286BaseActual source current space)

/-- The generated whole actual after the complete P286 response is installed
from the action dual of the full synchronized intermediate. -/
def currentFullSynchronizedCompleteP286Actual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  fullSynchronizedCompleteP286ActionResponseOperator source
    (currentFullSynchronizedCompleteP286BaseActual source current space)

theorem currentFullSynchronizedCompleteP286Actual_eq_outer
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    currentFullSynchronizedCompleteP286Actual source current space =
      currentP286CompleteActionResponseOperator source
        (currentFullSynchronizedResponseActual source current space) :=
  rfl

/-- Outer P286 origin fidelity is relative to the generated full
intermediate, not to the input state or C3h153 base actual. -/
theorem currentFullSynchronizedCompleteP286Actual_originContact
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    toContinuumPointField
        (currentFullSynchronizedCompleteP286Actual source current space) 0 =
      toContinuumPointField
        (currentFullSynchronizedResponseActual source current space) 0 := by
  exact
    fullSynchronizedCompleteP286ActionResponseOperator_pointField_origin
      source
      (currentFullSynchronizedCompleteP286BaseActual source current space)

/-! ## Canonical path and whole-slice update -/

/-- Canonical physical-time restriction of the generated whole local actual. -/
def currentFullSynchronizedCompleteP286LocalPath
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    StageNineCauchyState :=
  canonicalCauchyRestriction time
    (currentFullSynchronizedCompleteP286Actual source current space)

/-- Assemble the local-path origin at each global spatial contact. -/
def currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : ℝ) :
    StageNineCauchyState where
  coframe := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      time).coframe 0
  gravityConnection := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      time).gravityConnection 0
  gravityAuxiliary := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      time).gravityAuxiliary 0
  gravitySimplicityMultiplier := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      time).gravitySimplicityMultiplier 0
  gaugeConnection := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      time).gaugeConnection 0
  gaugeAuxiliary := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      time).gaugeAuxiliary 0
  scalar := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      time).scalar 0
  scalarVelocity := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      time).scalarVelocity 0
  matter := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      time).matter 0
  conjugateMatter := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      time).conjugateMatter 0

/-- The honest zero response is generated by the same full local actual at
every contact.  It is deliberately a distinct definition from `current`. -/
def currentFullSynchronizedCompleteP286GeneratedZeroResponseState
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineCauchyState where
  coframe := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      0).coframe 0
  gravityConnection := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      0).gravityConnection 0
  gravityAuxiliary := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      0).gravityAuxiliary 0
  gravitySimplicityMultiplier := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      0).gravitySimplicityMultiplier 0
  gaugeConnection := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      0).gaugeConnection 0
  gaugeAuxiliary := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      0).gaugeAuxiliary 0
  scalar := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      0).scalar 0
  scalarVelocity := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      0).scalarVelocity 0
  matter := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      0).matter 0
  conjugateMatter := fun space =>
    (currentFullSynchronizedCompleteP286LocalPath source current space
      0).conjugateMatter 0

@[simp] theorem
    currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate_zero :
    ∀ (source : SmoothUnifiedSource) (current : StageNineCauchyState),
      currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate source current
          0 =
        currentFullSynchronizedCompleteP286GeneratedZeroResponseState
          source current :=
  fun _ _ => rfl

/-! ## P286 path coordinate and generated first jet -/

/-- P286 auxiliary coordinate read from the same generated local actual. -/
def currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (globalSpace localSpace : StageNineSpatialPoint)
    (time : ℝ) :
    P286GaugeTwoForm :=
  fun pair =>
    p286CoordinateEquiv
      ((currentFullSynchronizedCompleteP286LocalPath source current globalSpace
        time |>.gaugeAuxiliary) localSpace pair)

theorem
    currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_eq_generated
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (globalSpace localSpace : StageNineSpatialPoint)
    (time : ℝ) :
    currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate source current
        globalSpace localSpace time =
      currentP286CompleteResponseAuxiliaryCoordinate source
        (currentFullSynchronizedResponseActual source current globalSpace)
        (canonicalCauchySlicePoint time localSpace) := by
  funext pair
  unfold currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate
    currentFullSynchronizedCompleteP286LocalPath
    canonicalCauchyRestriction
  change
    holonomicP286GaugeAuxiliaryCoordinate
        (currentP286CompleteActionResponseOperator source
          (currentFullSynchronizedResponseActual source current globalSpace))
        (canonicalCauchySlicePoint time localSpace) pair =
      _
  exact congrFun
    (currentP286CompleteActionResponseOperator_auxiliaryCoordinate source
      (currentFullSynchronizedResponseActual source current globalSpace)
      (canonicalCauchySlicePoint time localSpace))
    pair

/-- The complete local path retains both the generated physical-time
velocity and the generated spatial Gauss profile. -/
theorem
    currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_normalForm
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (globalSpace localSpace : StageNineSpatialPoint)
    (time : ℝ) :
    currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate source current
        globalSpace localSpace time =
      currentP286OriginAuxiliaryCoordinate
          (currentFullSynchronizedResponseActual source current globalSpace) +
        time •
          p286SpatialAuxiliaryVelocityEmbedding
            (currentP286SpatialAuxiliaryVelocity source
              (currentFullSynchronizedResponseActual source current
                globalSpace)) +
        ∑ axis : Fin 3,
          (canonicalP286EqualAxisCoefficient * localSpace axis) •
            p286GaussAuxiliaryAxisEmbedding
              (currentP286GaussCharge source
                (currentFullSynchronizedResponseActual source current
                  globalSpace))
              axis := by
  rw [
    currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_eq_generated,
    currentP286CompleteResponseAuxiliaryCoordinate_canonicalSlice]

/-- At every global contact, local spatial point, auxiliary pair, and time,
the actual path derivative is the unique velocity generated from the same
full intermediate action dual. -/
theorem
    currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_hasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (globalSpace localSpace : StageNineSpatialPoint)
    (pair : Fin 6)
    (time : ℝ) :
    HasDerivAt
      (fun candidate : ℝ =>
        currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate source
          current globalSpace localSpace candidate pair)
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentFullSynchronizedResponseActual source current globalSpace))
        pair)
      time := by
  rw [show
    (fun candidate : ℝ =>
      currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate source
        current globalSpace localSpace candidate pair) =
      (fun candidate : ℝ =>
        currentP286CompleteResponseAuxiliaryCoordinate source
          (currentFullSynchronizedResponseActual source current globalSpace)
          (canonicalCauchySlicePoint candidate localSpace) pair) by
    funext candidate
    exact congrFun
      (currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_eq_generated
        source current globalSpace localSpace candidate)
      pair]
  exact
    currentP286CompleteResponseAuxiliaryCoordinate_canonicalSlice_hasDerivAt
      source
      (currentFullSynchronizedResponseActual source current globalSpace)
      localSpace pair time

theorem
    currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_deriv
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (globalSpace localSpace : StageNineSpatialPoint)
    (pair : Fin 6)
    (time : ℝ) :
    deriv
        (fun candidate : ℝ =>
          currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate source
            current globalSpace localSpace candidate pair)
        time =
      p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentFullSynchronizedResponseActual source current globalSpace))
        pair :=
  (currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_hasDerivAt
    source current globalSpace localSpace pair time).deriv

/-! ## Assembled whole-update P286 first jet -/

/-- The whole-slice field reads the local origin at the same global contact.
Its physical-time first jet therefore remains the velocity generated from
that contact's full intermediate action dual. -/
theorem
    currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate_p286Auxiliary_hasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (globalSpace : StageNineSpatialPoint)
    (pair : Fin 6)
    (time : ℝ) :
    HasDerivAt
      (fun candidate : ℝ =>
        p286CoordinateEquiv
          ((currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate source
            current candidate).gaugeAuxiliary globalSpace pair))
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentFullSynchronizedResponseActual source current globalSpace))
        pair)
      time := by
  change
    HasDerivAt
      (fun candidate : ℝ =>
        currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate source
          current globalSpace 0 candidate pair)
      _
      time
  exact
    currentFullSynchronizedCompleteP286PathAuxiliaryCoordinate_hasDerivAt
      source current globalSpace 0 pair time

theorem
    currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate_p286Auxiliary_deriv
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (globalSpace : StageNineSpatialPoint)
    (pair : Fin 6)
    (time : ℝ) :
    deriv
        (fun candidate : ℝ =>
          p286CoordinateEquiv
            ((currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate source
              current candidate).gaugeAuxiliary globalSpace pair))
        time =
      p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentFullSynchronizedResponseActual source current globalSpace))
        pair :=
  (currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate_p286Auxiliary_hasDerivAt
    source current globalSpace pair time).deriv

/-- The velocity in the path theorem is not a supplied witness: it is the
canonical inverse image of the spatial action target read from the same full
intermediate actual. -/
theorem currentFullSynchronizedCompleteP286Velocity_response
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (globalSpace : StageNineSpatialPoint) :
    p286SpatialBFLegendreDualOperator
        (currentP286SpatialAuxiliaryVelocity source
          (currentFullSynchronizedResponseActual source current globalSpace)) =
      currentP286SpatialActionTarget source
        (currentFullSynchronizedResponseActual source current globalSpace) :=
  currentP286SpatialAuxiliaryVelocity_response _ _

theorem currentFullSynchronizedCompleteP286Velocity_unique
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (globalSpace : StageNineSpatialPoint)
    (candidate : P286SpatialGaugeDirection)
    (response :
      p286SpatialBFLegendreDualOperator candidate =
        currentP286SpatialActionTarget source
          (currentFullSynchronizedResponseActual source current globalSpace)) :
    candidate =
      currentP286SpatialAuxiliaryVelocity source
        (currentFullSynchronizedResponseActual source current globalSpace) :=
  currentP286SpatialAuxiliaryVelocity_unique _ _ candidate response

/-! ## Generic action-first update law -/

structure StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdateLaw
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (update : ℝ → StageNineCauchyState) : Prop where
  updateGenerated :
    update =
      currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate source current
  baseActualGenerated : ∀ space,
    currentFullSynchronizedCompleteP286BaseActual source current space =
      sourceActionGeneratedLinearPlebanskiJointLocalActualLift
        source current space
  fullIntermediateGenerated : ∀ space,
    currentFullSynchronizedResponseActual source current space =
      fullSynchronizedActionResponseOperator source
        (currentFullSynchronizedCompleteP286BaseActual source current space)
  completeActualGenerated : ∀ space,
    currentFullSynchronizedCompleteP286Actual source current space =
      currentP286CompleteActionResponseOperator source
        (currentFullSynchronizedResponseActual source current space)
  outerOriginContact : ∀ space,
    toContinuumPointField
        (currentFullSynchronizedCompleteP286Actual source current space) 0 =
      toContinuumPointField
        (currentFullSynchronizedResponseActual source current space) 0
  localPathGenerated : ∀ space time,
    currentFullSynchronizedCompleteP286LocalPath source current space time =
      canonicalCauchyRestriction time
        (currentFullSynchronizedCompleteP286Actual source current space)
  zeroResponseGenerated :
    update 0 =
      currentFullSynchronizedCompleteP286GeneratedZeroResponseState
        source current
  p286VelocityResponse : ∀ space,
    p286SpatialBFLegendreDualOperator
        (currentP286SpatialAuxiliaryVelocity source
          (currentFullSynchronizedResponseActual source current space)) =
      currentP286SpatialActionTarget source
        (currentFullSynchronizedResponseActual source current space)
  p286VelocityUnique : ∀ space candidate,
    p286SpatialBFLegendreDualOperator candidate =
        currentP286SpatialActionTarget source
          (currentFullSynchronizedResponseActual source current space) →
      candidate =
        currentP286SpatialAuxiliaryVelocity source
          (currentFullSynchronizedResponseActual source current space)
  p286AuxiliaryTimeJet : ∀ globalSpace pair time,
    HasDerivAt
      (fun candidate : ℝ =>
        p286CoordinateEquiv
          ((update candidate).gaugeAuxiliary globalSpace pair))
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentFullSynchronizedResponseActual source current globalSpace))
        pair)
      time

theorem currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate_realizes
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdateLaw
      source current
      (currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate
        source current) := by
  exact
    { updateGenerated := rfl
      baseActualGenerated := fun _ => rfl
      fullIntermediateGenerated := fun _ => rfl
      completeActualGenerated :=
        currentFullSynchronizedCompleteP286Actual_eq_outer source current
      outerOriginContact :=
        currentFullSynchronizedCompleteP286Actual_originContact source current
      localPathGenerated := fun _ _ => rfl
      zeroResponseGenerated :=
        currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate_zero
          source current
      p286VelocityResponse :=
        currentFullSynchronizedCompleteP286Velocity_response source current
      p286VelocityUnique := fun space candidate response =>
        currentFullSynchronizedCompleteP286Velocity_unique source current
          space candidate response
      p286AuxiliaryTimeJet :=
        currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate_p286Auxiliary_hasDerivAt
          source current }

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdate
