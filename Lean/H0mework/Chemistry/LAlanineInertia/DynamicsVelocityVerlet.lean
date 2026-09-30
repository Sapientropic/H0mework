import H0mework.Chemistry.LAlanineForce.NativeNuclearUpdate
import Mathlib.Tactic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Mechanics

open Force.Interface

abbrev Coordinates := Atom → Axis → ℚ
abbrev Masses := Atom → ℚ

@[ext] structure PhasePoint where
  position : Coordinates
  momentum : Coordinates

def positionNext (mass : Masses) (q : ℚ) (position momentum force : Coordinates) : Coordinates :=
  fun atom axis => position atom axis + q * momentum atom axis / mass atom +
    q ^ 2 * force atom axis / (2 * mass atom)

def momentumNext (q : ℚ) (momentum forceBefore forceAfter : Coordinates) : Coordinates :=
  fun atom axis => momentum atom axis + q * (forceBefore atom axis + forceAfter atom axis) / 2

def verletStep (mass : Masses) (q : ℚ) (forceBefore forceAfter : Coordinates)
    (current : PhasePoint) : PhasePoint :=
  ⟨positionNext mass q current.position current.momentum forceBefore,
    momentumNext q current.momentum forceBefore forceAfter⟩

def halfKick (q : ℚ) (force : Coordinates) (current : PhasePoint) : PhasePoint :=
  ⟨current.position, fun atom axis => current.momentum atom axis + q * force atom axis / 2⟩

def drift (mass : Masses) (q : ℚ) (current : PhasePoint) : PhasePoint :=
  ⟨fun atom axis => current.position atom axis + q * current.momentum atom axis / mass atom,
    current.momentum⟩

theorem verletStep_split (mass : Masses) (q : ℚ) (forceBefore forceAfter : Coordinates)
    (current : PhasePoint) (massNonzero : ∀ atom, mass atom ≠ 0) :
    verletStep mass q forceBefore forceAfter current =
      halfKick q forceAfter (drift mass q (halfKick q forceBefore current)) := by
  apply PhasePoint.ext <;> funext atom axis
  · simp only [verletStep, positionNext, halfKick, drift]
    field_simp [massNonzero atom]
    ring
  · simp only [verletStep, momentumNext, halfKick, drift]
    ring

theorem halfKick_reverse (q : ℚ) (force : Coordinates) (current : PhasePoint) :
    halfKick (-q) force (halfKick q force current) = current := by
  apply PhasePoint.ext
  · rfl
  · funext atom axis
    simp only [halfKick]
    ring

theorem drift_reverse (mass : Masses) (q : ℚ) (current : PhasePoint) :
    drift mass (-q) (drift mass q current) = current := by
  apply PhasePoint.ext
  · funext atom axis
    simp only [drift]
    ring
  · rfl

theorem verletStep_reverse (mass : Masses) (q : ℚ) (forceBefore forceAfter : Coordinates)
    (current : PhasePoint) (massNonzero : ∀ atom, mass atom ≠ 0) :
    verletStep mass (-q) forceAfter forceBefore
      (verletStep mass q forceBefore forceAfter current) = current := by
  rw [verletStep_split mass (-q) forceAfter forceBefore _ massNonzero,
    verletStep_split mass q forceBefore forceAfter _ massNonzero,
    halfKick_reverse, drift_reverse, halfKick_reverse]

theorem verletStep_zero (mass : Masses) (forceBefore forceAfter : Coordinates) (current : PhasePoint) :
    verletStep mass 0 forceBefore forceAfter current = current := by
  apply PhasePoint.ext <;> funext atom axis <;> simp [verletStep, positionNext, momentumNext]

theorem position_only_cannot_determine_next (mass : Masses) (q : ℚ) (force : Coordinates)
    (massNonzero : ∀ atom, mass atom ≠ 0) (timeNonzero : q ≠ 0) :
    ¬ ∃ read : Coordinates → Coordinates, ∀ current : PhasePoint,
      positionNext mass q current.position current.momentum force = read current.position := by
  rintro ⟨read, faithful⟩
  have same := (faithful ⟨0, 0⟩).trans (faithful ⟨0, 1⟩).symm
  have entry := congrFun (congrFun same (0 : Atom)) (0 : Axis)
  simp only [positionNext, Pi.zero_apply, Pi.one_apply, mul_zero, mul_one, zero_div, zero_add] at entry
  have vanished : q / mass 0 = 0 := by linarith
  exact div_ne_zero timeNonzero (massNonzero 0) vanished

end LAlanine40K2025.Inertia.Mechanics
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
