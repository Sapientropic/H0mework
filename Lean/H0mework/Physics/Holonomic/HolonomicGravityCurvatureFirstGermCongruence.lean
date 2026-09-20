import H0mework.Physics.Holonomic.HolonomicField

/-!
# Holonomic gravity-curvature first-germ congruence

The actual holonomic curvature at one contact reads only the primitive
Lorentz connection value and its first coordinate derivatives at that same
contact.  This dependency-light lemma records that fact explicitly.

It is a readout seam: it does not construct a connection, accept a curvature
target, or transport a curvature equation from another actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineHolonomicGravityCurvatureFirstGermCongruence

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

/-- Equality of the primitive connection value and all of its coordinate
first derivatives at one contact forces equality of the literal
`dω + ω ∧ ω` curvature read there. -/
theorem holonomicGravityCurvature_eq_of_connection_firstGermAt
    (first second : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (connectionValue :
      ∀ formDirection internalOut internalIn,
        first.gravityConnection point formDirection internalOut internalIn =
          second.gravityConnection point formDirection internalOut internalIn)
    (connectionDerivative :
      ∀ derivativeDirection formDirection internalOut internalIn,
        gravityConnectionDerivative first point derivativeDirection
            formDirection internalOut internalIn =
          gravityConnectionDerivative second point derivativeDirection
            formDirection internalOut internalIn) :
    holonomicGravityCurvature first point =
      holonomicGravityCurvature second point := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
  dsimp only
  rw [connectionDerivative, connectionDerivative]
  simp_rw [connectionValue]

end

end
  SaturationMonoid.PhysicsCore.StageNineHolonomicGravityCurvatureFirstGermCongruence
