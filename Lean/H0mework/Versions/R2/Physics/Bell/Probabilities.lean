import H0mework.Versions.R2.Physics.Bell.Source

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell

open Matrix Stage9DEF State
open Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource
open scoped Kronecker ComplexOrder

noncomputable section

structure Axis where
  x : ℝ
  z : ℝ
  unit : x^2 + z^2 = 1

def sign : Bool → ℝ | false => 1 | true => -1

def Axis.signed (a : Axis) (outcome : Bool) : Axis where
  x := sign outcome * a.x
  z := sign outcome * a.z
  unit := by cases outcome <;> simpa [sign] using a.unit

def Axis.reflected (a : Axis) : Axis where
  x := -a.x
  z := a.z
  unit := by simpa using a.unit

def Axis.atAngle (angle : ℝ) : Axis :=
  ⟨Real.sin angle, Real.cos angle, Real.sin_sq_add_cos_sq angle⟩

def probability (a b : Axis) (outcomeA outcomeB : Bool) : ℝ :=
  (1 - sign outcomeA * sign outcomeB * (a.x * b.x + a.z * b.z)) / 4

def outcomeEffect (a b : Axis) (outcomeA outcomeB : Bool) : Effect :=
  let first := a.signed outcomeA
  let second := b.signed outcomeB
  jointEffect first.x first.z second.x second.z first.unit second.unit

theorem probability_from_source (point : BasePoint) (a b : Axis) (x y : Bool) :
    effectWeight point (outcomeEffect a b x y) = probability a b x y := by
  rw [outcomeEffect, joint_probability_at]
  simp only [Axis.signed, probability]
  ring

theorem probability_nonnegative (a b : Axis) (x y : Bool) :
    0 ≤ probability a b x y := by
  rw [← probability_from_source 0]
  exact effectWeight_nonnegative _ _

theorem probability_le_one (a b : Axis) (x y : Bool) :
    probability a b x y ≤ 1 := by
  rw [← probability_from_source 0]
  exact effectWeight_le_one _ _

theorem probability_normalized (a b : Axis) :
    ∑ x : Bool, ∑ y : Bool, probability a b x y = 1 := by
  simp [probability, sign]
  ring

theorem probability_left_marginal (a b : Axis) (x : Bool) :
    ∑ y : Bool, probability a b x y = 1 / 2 := by
  simp [probability, sign]
  ring

theorem probability_right_marginal (a b : Axis) (y : Bool) :
    ∑ x : Bool, probability a b x y = 1 / 2 := by
  simp [probability, sign]
  ring

theorem correlation (a b : Axis) :
    (∑ x : Bool, ∑ y : Bool,
      sign x * sign y * probability a b x y) = -(a.x * b.x + a.z * b.z) := by
  simp [probability, sign]
  ring


end
end SaturationMonoid.PhysicsCore.Stage10.Bell
