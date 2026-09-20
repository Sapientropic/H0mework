import H0mework.Realization.Operations.Effects
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Int.Basic

/-! Nested, heterogeneous and noncommutative operation-update consumers. -/

set_option autoImplicit false

namespace SaturationMonoid.SourceOperationEffects.Controls

section Cubic

variable (R : Type*) [NonUnitalNonAssocRing R]

def cubic : Expr (fun _ : Unit => R) (fun _ => ℕ) () :=
  .bilinear (s := ()) (t := ()) AddMonoidHom.mul
    (.bilinear (s := ()) (t := ()) AddMonoidHom.mul (.var 0) (.var 1)) (.var 2)

def tripleEnvironment (x y z : R) : Env (fun _ : Unit => R) (fun _ => ℕ) :=
  fun _ n => match n with
    | 0 => x
    | 1 => y
    | _ => z

/-- Seven ordered effects survive a nested multiplication; no associative or
commutative multiplication is assumed. -/
theorem cubic_generated_effect (x y z dx dy dz : R) :
    (cubic R).effect (tripleEnvironment R x y z) (tripleEnvironment R dx dy dz) =
      (dx * y) * z + (x * dy) * z + (x * y) * dz + (dx * dy) * z +
        (dx * y) * dz + (x * dy) * dz + (dx * dy) * dz := by
  change (x * y) * dz + (x * dy + dx * y + dx * dy) * z +
    (x * dy + dx * y + dx * dy) * dz = _
  simp only [add_mul]
  abel

theorem cubic_update_consumer (x y z dx dy dz : R) :
    ((x + dx) * (y + dy)) * (z + dz) =
      (x * y) * z + ((dx * y) * z + (x * dy) * z + (x * y) * dz +
        (dx * dy) * z + (dx * y) * dz + (x * dy) * dz + (dx * dy) * dz) := by
  have h := (cubic R).eval_update (tripleEnvironment R x y z)
    (tripleEnvironment R dx dy dz)
  rw [cubic_generated_effect] at h
  exact h

end Cubic

/-- An actual nonsymmetric bilinear operation, so the two cross actions cannot
be collapsed into one doubled scalar term. -/
def leftWeighted : (ℤ × ℤ) →+ (ℤ × ℤ) →+ (ℤ × ℤ) where
  toFun x :=
    { toFun := fun y => (x.1 * y.1, x.1 * y.2)
      map_zero' := by simp
      map_add' := by intro y z; ext <;> simp [mul_add] }
  map_zero' := by ext y <;> simp
  map_add' := by intro x y; ext z <;> simp [add_mul]

theorem cross_actions_are_distinct :
    leftWeighted (1, 2) (3, 4) ≠ leftWeighted (3, 4) (1, 2) := by decide

theorem joint_increment_survives : leftWeighted (3, 4) (3, 4) ≠ 0 := by decide

def nestedWeighted : Expr (fun _ : Unit => ℤ × ℤ) (fun _ => Unit) () :=
  .bilinear (s := ()) (t := ()) leftWeighted
    (.bilinear (s := ()) (t := ()) leftWeighted (.var ()) (.var ())) (.var ())

theorem nested_noncommutative_effect :
    nestedWeighted.effect (fun _ _ => (1, 2)) (fun _ _ => (3, 4)) = (63, 94) := rfl

inductive Coordinate
  | scalar
  | pair

abbrev Value : Coordinate → Type
  | .scalar => ℤ
  | .pair => ℤ × ℤ

instance (s : Coordinate) : AddCommGroup (Value s) := by
  cases s <;> dsimp [Value] <;> infer_instance

def duplicate : ℤ →+ ℤ × ℤ := (AddMonoidHom.id ℤ).prod (AddMonoidHom.id ℤ)

def heterogeneous : Expr Value (fun _ => Unit) .scalar :=
  .add
    (.linear (s := .pair) (AddMonoidHom.fst ℤ ℤ)
      (.bilinear (s := .pair) (t := .pair) leftWeighted (.var ())
        (.linear (s := .scalar) duplicate (.var ()))))
    (.var ())

def old : Env Value (fun _ => Unit)
  | .scalar, _ => 5
  | .pair, _ => (1, 2)

def increment : Env Value (fun _ => Unit)
  | .scalar, _ => 7
  | .pair, _ => (3, 4)

theorem heterogeneous_effect : heterogeneous.effect old increment = 50 := rfl

theorem heterogeneous_update_consumer : heterogeneous.eval (old + increment) = 60 := by
  rw [heterogeneous.eval_update, heterogeneous_effect]
  rfl

end SaturationMonoid.SourceOperationEffects.Controls
