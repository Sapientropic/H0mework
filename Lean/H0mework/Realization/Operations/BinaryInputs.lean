import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.BilinearMap
import H0mework.Realization.Operations.DerivationReduction

/-! Raw native binary functions enter the existing language through free joint inputs. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeBinary

open SourceOperationEffects SourceOperationDerivations

noncomputable section

universe u

abbrev Free (X : Type u) := X →₀ ℤ

variable {X Y Z : Type u}

/-- Independent free inputs generate their bilinear joint carrier. Existing correlated
joint inventory must instead enter `pushJoint` directly. -/
def joint : Free X →ₗ[ℤ] Free Y →ₗ[ℤ] Free (X × Y) :=
  Finsupp.linearCombination ℤ fun x =>
    Finsupp.linearCombination ℤ fun y => Finsupp.single (x, y) 1

def pushJoint (native : X → Y → Z) : Free (X × Y) →ₗ[ℤ] Free Z :=
  Finsupp.lmapDomain ℤ ℤ (Function.uncurry native)

def linear (native : X → Y → Z) : Free X →ₗ[ℤ] Free Y →ₗ[ℤ] Free Z :=
  joint.compr₂ (pushJoint native)

def lift (native : X → Y → Z) : Free X →+ Free Y →+ Free Z :=
  LinearMap.toAddMonoidHom'.comp (linear native).toAddMonoidHom

theorem lift_through_joint (native : X → Y → Z) (left : Free X) (right : Free Y) :
    lift native left right = pushJoint native (joint left right) := rfl

@[simp] theorem joint_point (x : X) (y : Y) :
    joint (Finsupp.single x 1) (Finsupp.single y 1) = Finsupp.single (x, y) 1 := by
  simp only [joint, Finsupp.linearCombination_single, one_smul]

@[simp] theorem pushJoint_point (native : X → Y → Z) (x : X) (y : Y) :
    pushJoint native (Finsupp.single (x, y) 1) = Finsupp.single (native x y) 1 := by
  simp only [pushJoint, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Function.uncurry_apply_pair]

@[simp] theorem lift_point (native : X → Y → Z) (x : X) (y : Y) :
    lift native (Finsupp.single x 1) (Finsupp.single y 1) = Finsupp.single (native x y) 1 := by
  rw [lift_through_joint, joint_point, pushJoint_point]

inductive BinarySort
  | left
  | right
  | result
  deriving DecidableEq

abbrev Value (X Y Z : Type u) : BinarySort → Type u
  | .left => Free X
  | .right => Free Y
  | .result => Free Z

instance : (slot : BinarySort) → AddCommGroup (Value X Y Z slot)
  | .left => inferInstance
  | .right => inferInstance
  | .result => inferInstance

abbrev Var (X Y Z : Type u) : BinarySort → Type u
  | .left => X
  | .right => Y
  | .result => Z

/-- Fixed input positions preserve both argument identity and the source universe. -/
def environment : Env (Value X Y Z) (Var X Y Z)
  | .left, value => Finsupp.single value 1
  | .right, value => Finsupp.single value 1
  | .result, value => Finsupp.single value 1

def expression (native : X → Y → Z) (x : X) (y : Y) :
    Expr (Value X Y Z) (Var X Y Z) .result :=
  .bilinear (s := .left) (t := .right) (lift native) (.var x) (.var y)

@[simp] theorem expression_eval (native : X → Y → Z) (x : X) (y : Y) :
    (expression native x y).eval environment = Finsupp.single (native x y) 1 :=
  lift_point native x y

theorem expression_mixed_update (native : X → Y → Z) (x : X) (y : Y)
    (increment : Env (Value X Y Z) (Var X Y Z)) :
    (expression native x y).eval (environment + increment) =
      Finsupp.single (native x y) 1 +
        (lift native (Finsupp.single x 1) (increment .right y) +
          lift native (increment .left x) (Finsupp.single y 1) +
          lift native (increment .left x) (increment .right y)) := by
  exact Expr.eval_update (expression native x y) environment increment |>.trans
    (congrArg (fun old => old + (expression native x y).effect environment increment)
      (expression_eval native x y))

def normalization (native : X → Y → Z) (x : X) (y : Y) :
    Derivation environment (expression native x y) (.const (Finsupp.single (native x y) 1)) := by
  have generated := Derivation.normalize environment (expression native x y)
  rw [expression_eval] at generated
  exact generated

end
end SourceNativeBinary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
