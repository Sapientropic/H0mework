import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Four-phase tactical algebra

This module supplies the pure algebraic carrier consumed by the G4 relation
phase producer.  It does not assign tactical roles: a later same-occurrence
consumer must generate a phase from the change in future-freedom fibres.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

/-- The four composable tactical phases. -/
abbrev TacticalPhase := ZMod 4

namespace TacticalPhase

/-- Composition of relation phases is the additive law of `C4`. -/
def compose (first second : TacticalPhase) : TacticalPhase :=
  first + second

@[simp] theorem compose_eq_add (first second : TacticalPhase) :
    compose first second = first + second :=
  rfl

@[simp] theorem compose_zero_left (phase : TacticalPhase) :
    compose 0 phase = phase := by
  simp [compose]

@[simp] theorem compose_zero_right (phase : TacticalPhase) :
    compose phase 0 = phase := by
  simp [compose]

theorem compose_assoc (first second third : TacticalPhase) :
    compose (compose first second) third = compose first (compose second third) := by
  simp [compose, add_assoc]

/-- The canonical faithful character `C4 → U(1)`. -/
noncomputable def character : AddChar TacticalPhase Circle :=
  ZMod.toCircle

/-- The unit-circle rotation carried by a phase. -/
noncomputable def rotation (phase : TacticalPhase) : Circle :=
  character phase

@[simp] theorem rotation_compose (first second : TacticalPhase) :
    rotation (compose first second) = rotation first * rotation second := by
  simp [rotation, character, compose, AddChar.map_add_eq_mul]

/-- The `C4 → U(1)` character is faithful. -/
theorem character_injective : Function.Injective character :=
  ZMod.injective_toCircle

/-- The rotation readout is faithful as well. -/
theorem rotation_injective : Function.Injective rotation := by
  intro first second equalRotations
  exact character_injective equalRotations

@[simp] theorem rotation_zero : rotation 0 = 1 := by
  simp [rotation, character]

/-- A phase has trivial rotation exactly when it is the identity phase. -/
@[simp] theorem rotation_eq_one_iff (phase : TacticalPhase) :
    rotation phase = 1 ↔ phase = 0 := by
  constructor
  · intro equalRotations
    exact rotation_injective (equalRotations.trans rotation_zero.symm)
  · rintro rfl
    exact rotation_zero

/-- A nonidentity phase produces a nontrivial unit-circle rotation. -/
@[simp] theorem rotation_ne_one_iff (phase : TacticalPhase) :
    rotation phase ≠ 1 ↔ phase ≠ 0 :=
  not_congr (rotation_eq_one_iff phase)

/-- Phase `0` maps to `1`. -/
theorem rotation_zero_complex : ((rotation 0 : Circle) : ℂ) = 1 := by
  simp

/-- Phase `1` maps to `i`. -/
theorem rotation_one_complex : ((rotation 1 : Circle) : ℂ) = Complex.I := by
  change ZMod.stdAddChar ((1 : ℤ) : ZMod 4) = Complex.I
  rw [ZMod.stdAddChar_coe]
  norm_num
  rw [show 2 * (Real.pi : ℂ) * Complex.I / 4 =
      Real.pi / 2 * Complex.I by ring]
  exact Complex.exp_pi_div_two_mul_I

/-- Phase `2` maps to `-1`. -/
theorem rotation_two_complex : ((rotation 2 : Circle) : ℂ) = -1 := by
  change ZMod.stdAddChar ((2 : ℤ) : ZMod 4) = -1
  rw [ZMod.stdAddChar_coe]
  norm_num
  rw [show 2 * (Real.pi : ℂ) * Complex.I * 2 / 4 =
      Real.pi * Complex.I by ring]
  exact Complex.exp_pi_mul_I

/-- Phase `3` maps to `-i`. -/
theorem rotation_three_complex : ((rotation 3 : Circle) : ℂ) = -Complex.I := by
  change ZMod.stdAddChar ((3 : ℤ) : ZMod 4) = -Complex.I
  rw [ZMod.stdAddChar_coe]
  norm_num
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (3 : ℂ) / (4 : ℂ)) =
      Real.pi / 2 * Complex.I + Real.pi * Complex.I by ring]
  rw [Complex.exp_add, Complex.exp_pi_div_two_mul_I, Complex.exp_pi_mul_I]
  ring

end TacticalPhase

end Go
end ProcessGame
end SaturationMonoid
