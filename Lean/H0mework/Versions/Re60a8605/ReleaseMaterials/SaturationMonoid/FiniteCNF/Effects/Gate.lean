import H0mework.Realization.Operations.InventoryLift
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Forgetting.Scalar
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.EffectGate
open SourceOperationEffects SourceOperationScalarInventoryLift
open InterferenceProgram

abbrev Field := ZMod 2
abbrev Value (_ : Unit) := Field
abbrev Variable (_ : Unit) := Nat
abbrev Expression := SourceOperationEffects.Expr Value Variable ()

def mulMap : Field →+ Field →+ Field where
  toFun a := { toFun := fun b => a*b, map_zero' := mul_zero a, map_add' := mul_add a }
  map_zero' := by ext b; simp
  map_add' := by intro a b; ext c; simp [add_mul]

def productExpression : Expression := .bilinear mulMap (.var 0 : Expression) (.var 1 : Expression)

def environment (a b : Field) : Env Value Variable := fun _ i => if i=0 then a else b

theorem generated_product (a da b db : Field) :
    (liftExpr productExpression).eval (pairEnvironment (environment a b) (environment da db))=
      (a*b,a*db+da*b+da*db) := by
  rw [eval_liftExpr]
  simp [productExpression,Expr.eval,Expr.effect,environment,mulMap]

theorem product_update (a da b db : Field) : (a+da)*(b+db)=a*b+(a*db+da*b+da*db) := by
  have generated := productExpression.eval_update (environment a b) (environment da db)
  simpa [productExpression,Expr.eval,Expr.effect,environment,mulMap] using generated

def encode (value : Bool) : Field := if value then 1 else 0

theorem encode_xor (a b : Bool) : encode (a^^b)=encode a+encode b := by
  cases a <;> cases b <;> decide

theorem encode_and (a b : Bool) : encode (a&&b)=encode a*encode b := by
  cases a <;> cases b <;> decide

theorem encode_injective : Function.Injective encode := by
  intro a b same
  cases a <;> cases b <;> simp_all [encode]

abbrev Pair := Bool × Bool

def add (left right : Pair) : Pair := (left.1^^right.1,left.2^^right.2)
def multiply (left right : Pair) : Pair := (left.1&&right.1,((left.1&&right.2)^^(left.2&&right.1))^^(left.2&&right.2))
def invert (value : Pair) : Pair := (!value.1,value.2)
def select (control left right : Pair) : Pair := add left (multiply control (add left right))

theorem multiply_generated (left right : Pair) :
    (encode (multiply left right).1,encode (multiply left right).2)=
      (liftExpr productExpression).eval (pairEnvironment (environment (encode left.1) (encode right.1))
        (environment (encode left.2) (encode right.2))) := by
  rw [generated_product]
  simp only [multiply,encode_and,encode_xor]

theorem multiply_update (left right : Pair) :
    ((multiply left right).1^^(multiply left right).2)=((left.1^^left.2)&&(right.1^^right.2)) := by
  apply encode_injective
  rw [encode_xor,encode_and,encode_xor,encode_xor]
  have source := multiply_generated left right
  rw [generated_product] at source
  have first := congrArg Prod.fst source
  have second := congrArg Prod.snd source
  dsimp only at first second
  rw [first,second]
  exact (product_update _ _ _ _).symm

theorem add_update (left right : Pair) :
    ((add left right).1^^(add left right).2)=((left.1^^left.2)^^(right.1^^right.2)) := by
  rcases left with ⟨a,da⟩
  rcases right with ⟨b,db⟩
  cases a <;> cases da <;> cases b <;> cases db <;> rfl

theorem invert_update (value : Pair) : ((invert value).1^^(invert value).2)=(!(value.1^^value.2)) := by
  rcases value with ⟨a,da⟩
  cases a <;> cases da <;> rfl

theorem select_base (control left right : Pair) : (select control left right).1=
    (if control.1 then right.1 else left.1) := by
  simp only [select,add,multiply]
  cases control.1 <;> cases left.1 <;> cases right.1 <;> rfl

theorem select_update (control left right : Pair) :
    ((select control left right).1^^(select control left right).2)=
      (if control.1^^control.2 then right.1^^right.2 else left.1^^left.2) := by
  rw [select,add_update,multiply_update,add_update]
  cases (control.1^^control.2) <;> cases (left.1^^left.2) <;> cases (right.1^^right.2) <;> rfl

theorem existential_read (value : Pair) : (value.1^^(!value.1 && value.2))=(value.1 || (value.1^^value.2)) := by
  rcases value with ⟨old,delta⟩
  cases old <;> cases delta <;> rfl

end SaturationMonoid.ComplexityProjection.SATSource.EffectGate
