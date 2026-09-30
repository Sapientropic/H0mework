import H0mework.Chemistry.LAlanineInertia.DynamicsVelocityVerlet

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Mechanics

open Force.Interface

def addResidual (reference residual : PhasePoint) : PhasePoint :=
  ⟨fun atom axis => reference.position atom axis + residual.position atom axis,
    fun atom axis => reference.momentum atom axis + residual.momentum atom axis⟩

/-- Observed-minus-reference is a readout, never an input to the Verlet producer. -/
def stepResidual (mass : Masses) (q : ℚ) (forceBefore forceAfter : Coordinates)
    (current observed : PhasePoint) : PhasePoint :=
  ⟨fun atom axis => observed.position atom axis -
      positionNext mass q current.position current.momentum forceBefore atom axis,
    fun atom axis => observed.momentum atom axis -
      momentumNext q current.momentum forceBefore forceAfter atom axis⟩

theorem reconstruct_recorded (mass : Masses) (q : ℚ) (forceBefore forceAfter : Coordinates)
    (current observed : PhasePoint) :
    addResidual (verletStep mass q forceBefore forceAfter current)
      (stepResidual mass q forceBefore forceAfter current observed) = observed := by
  apply PhasePoint.ext <;> funext atom axis <;>
    simp [addResidual, stepResidual, verletStep]

theorem residual_position_read (mass : Masses) (q : ℚ) (forceBefore forceAfter : Coordinates)
    (current observed : PhasePoint) (atom : Atom) (axis : Axis) :
    |observed.position atom axis - (verletStep mass q forceBefore forceAfter current).position atom axis| =
      |(stepResidual mass q forceBefore forceAfter current observed).position atom axis| := rfl

theorem residual_momentum_read (mass : Masses) (q : ℚ) (forceBefore forceAfter : Coordinates)
    (current observed : PhasePoint) (atom : Atom) (axis : Axis) :
    |observed.momentum atom axis - (verletStep mass q forceBefore forceAfter current).momentum atom axis| =
      |(stepResidual mass q forceBefore forceAfter current observed).momentum atom axis| := rfl

def reverseResidual (mass : Masses) (q : ℚ) (residual : PhasePoint) : PhasePoint :=
  ⟨fun atom axis => residual.position atom axis - q * residual.momentum atom axis / mass atom,
    residual.momentum⟩

theorem verletStep_reverse_residual (mass : Masses) (q : ℚ) (forceBefore forceAfter : Coordinates)
    (current residual : PhasePoint) (massNonzero : ∀ atom, mass atom ≠ 0) :
    verletStep mass (-q) forceAfter forceBefore
      (addResidual (verletStep mass q forceBefore forceAfter current) residual) =
        addResidual current (reverseResidual mass q residual) := by
  apply PhasePoint.ext <;> funext atom axis
  · simp only [verletStep, positionNext, momentumNext, addResidual, reverseResidual]
    field_simp [massNonzero atom]
    ring
  · simp only [verletStep, momentumNext, addResidual, reverseResidual]
    ring

theorem reverse_recorded (mass : Masses) (q : ℚ) (forceBefore forceAfter : Coordinates)
    (current observed : PhasePoint) (massNonzero : ∀ atom, mass atom ≠ 0) :
    verletStep mass (-q) forceAfter forceBefore observed =
      addResidual current (reverseResidual mass q
        (stepResidual mass q forceBefore forceAfter current observed)) := by
  have generated := verletStep_reverse_residual mass q forceBefore forceAfter current
    (stepResidual mass q forceBefore forceAfter current observed) massNonzero
  rw [reconstruct_recorded] at generated
  exact generated

theorem reverseResidual_error (mass : Masses) (q : ℚ) (residual : PhasePoint)
    (atom : Atom) (axis : Axis) :
    |(reverseResidual mass q residual).position atom axis| ≤
      |residual.position atom axis| + |q| * |residual.momentum atom axis| / |mass atom| := by
  have bound := abs_add_le (residual.position atom axis) (-(q * residual.momentum atom axis / mass atom))
  simpa only [reverseResidual, sub_eq_add_neg, abs_neg, abs_div, abs_mul] using bound

theorem reverseResidual_momentum (mass : Masses) (q : ℚ) (residual : PhasePoint) :
    (reverseResidual mass q residual).momentum = residual.momentum := rfl

end LAlanine40K2025.Inertia.Mechanics
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
