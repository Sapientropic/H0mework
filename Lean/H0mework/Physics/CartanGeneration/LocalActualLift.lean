import H0mework.Physics.ActionGeneration.PrimitiveCanonicalRelativeEulerDevelopment
import H0mework.Physics.CoframeJets.StateDependentCartanCoframeFirstJetLocalActualLift

/-!
# S9-C3h127: current-state torsion-free Cartan local actual lift

C3h126 first lets the source and the actual primitive/canonical dynamics
generate a current split.  This module sends the generated primitive
projection back through the existing C3h104 Cartan action constructor:

```text
source + initial primitive state
→ generated current primitive U(anchor)
→ Cartan action computes the current coframe velocity
→ actual local coframe germ
→ B := II⁺(e)
→ only then Cartan/simplicity acceptance.
```

The actual germ therefore replays a velocity computed from the generated
current state; no residual coordinate, endpoint, inverse image, quotient
representative, shell witness, branch receipt, or supplied stationarity
certificate enters the constructor.

This module is deliberately the torsion-free Cartan sector already formalized
in C3h104.  It does not turn a nonzero matter-spin state into an
Einstein--Cartan producer: the interaction-sensitive spin principal remains
a separate forward action gate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanLocalActualLift

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
open StageNineStateDependentCartanCoframeFirstJetLocalActualLift

noncomputable section

set_option autoImplicit false

/-- Re-enter the Cartan action with the primitive state already generated at
the selected anchor.  The current state is computed, not caller supplied. -/
def sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  sourceActionCartanCoframeLocalActualLift source
    (sourceActionGeneratedPrimitiveCanonicalCurrent
      source anchor state).primitive
    space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_initialCoframe
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
      source anchor state space).coframe 0 =
      (sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state).primitive.coframe space := by
  exact sourceActionCartanCoframeLocalActualLift_initialCoframe
    source
    (sourceActionGeneratedPrimitiveCanonicalCurrent
      source anchor state).primitive
    space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_initialGravityConnection
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
      source anchor state space).gravityConnection 0 =
      (sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state).primitive.gravityConnection space := by
  change
    (sourceActionGeneratedJointLocalActualLift source
      (sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state).primitive space).gravityConnection 0 =
      _
  exact sourceActionGeneratedJointLocalActualLift_initialGravityConnection
    source
    (sourceActionGeneratedPrimitiveCanonicalCurrent
      source anchor state).primitive
    space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_gravityAuxiliary_generated
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
      source anchor state space).gravityAuxiliary =
      fun point =>
        physicalIIPlusBivector
          ((sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
            source anchor state space).coframe point) := by
  exact sourceActionCartanCoframeLocalActualLift_gravityAuxiliary_generated
    source
    (sourceActionGeneratedPrimitiveCanonicalCurrent
      source anchor state).primitive
    space

/-- The actual local coframe derivative is the Cartan velocity recomputed
from the generated current primitive state. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_replays_velocity
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internal : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          (sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
            source anchor state space).coframe
            point internal direction.succ)
        0 canonicalLorentzianTimeDirection =
      cartanTorsionFreeSpatialCoframeVelocity
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).primitive
        space direction internal := by
  change
    (holonomicCoframeFirstJetAt
      (sourceActionCartanCoframeLocalActualLift source
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).primitive space).coframe
      0).derivative canonicalLorentzianTimeDirection
        internal direction.succ = _
  rw [sourceActionCartanCoframeLocalActualLift_coframeFirstJet]
  fin_cases direction <;>
    simp [cartanTorsionFreeCoframeFirstJet,
      canonicalLorentzianTimeDirection]

/-- Existing C3h104 action law specialized to the source-generated current
primitive state. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_realizes
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    SourceActionCartanCoframeFirstJetLocalActualLaw
      source
      (sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state).primitive
      space
      (sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
        source anchor state space) := by
  exact sourceActionCartanCoframeLocalActualLift_realizes_update_law
    source
    (sourceActionGeneratedPrimitiveCanonicalCurrent
      source anchor state).primitive
    space

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanLocalActualLift
