import H0mework.Realization.Operations.Execution.Coefficients.Words
import Mathlib.Algebra.Group.Pi.Lemmas
set_option autoImplicit false
noncomputable section
universe u v w z
namespace SaturationMonoid.SourceOperationExecution.InventoryVector
open SourceOperationEffects SourceOperationExecution
variable {S : Type u} {Value : S → Type v} {Var : S → Type w} [∀ sort,AddCommGroup (Value sort)]
variable (Index : Type z)
abbrev VectorValue (sort : S) := Index → Value sort
def linear {s t : S} (f : Value s →+ Value t) : VectorValue Index (Value:=Value) s →+ VectorValue Index (Value:=Value) t where
 toFun x := fun index => f (x index)
 map_zero' := by funext index; exact f.map_zero
 map_add' x y := by funext index; exact f.map_add _ _
def bilinear {s t r : S} (f : Value s →+ Value t →+ Value r) :
 VectorValue Index (Value:=Value) s →+ VectorValue Index (Value:=Value) t →+ VectorValue Index (Value:=Value) r where
 toFun x := {
  toFun:=fun y index => f (x index) (y index)
  map_zero':=by funext index; exact (f (x index)).map_zero
  map_add':=by intro y first; funext index; exact (f (x index)).map_add _ _ }
 map_zero' := by ext y index; exact congrFun (congrArg DFunLike.coe f.map_zero) (y index)
 map_add' x y := by ext argument index; exact congrArg (fun g : Value t →+ Value r => g (argument index)) (f.map_add _ _)
def expression {sort : S} : Expr Value Var sort → Expr (VectorValue Index (Value:=Value)) Var sort
 | .var name => .var name
 | .const value => .const (fun _ => value)
 | .add left right => .add (expression left) (expression right)
 | .linear f argument => .linear (linear Index f) (expression argument)
 | .bilinear f left right => .bilinear (bilinear Index f) (expression left) (expression right)
def environment (source : Env Value Var) : Env (VectorValue Index (Value:=Value)) Var := fun sort name _ => source sort name
theorem expression_read {sort : S} (term : Expr Value Var sort) (source : Env Value Var) (index : Index) :
 (expression Index term).eval (environment Index source) index=term.eval source := by
 induction term with
 | var => rfl
 | const => rfl
 | add left right first second => exact congrArg₂ (· + ·) first second
 | linear f argument previous => exact congrArg f previous
 | bilinear f left right first second => exact congrArg₂ (fun x y => f x y) first second
theorem expression_charge {sort : S} (term : Expr Value Var sort) : remaining (expression Index term)=remaining term := by
 induction term with
 | var => rfl
 | const => rfl
 | add left right first second => simp only [expression,remaining,first,second]
 | linear f argument previous => simp only [expression,remaining,previous]
 | bilinear f left right first second => simp only [expression,remaining,first,second]
def mask [DecidableEq Index] {sort : S} (index : Index) :
 VectorValue Index (Value:=Value) sort →+ VectorValue Index (Value:=Value) sort where
 toFun value := fun coordinate => if coordinate=index then value coordinate else 0
 map_zero' := by funext coordinate; split <;> rfl
 map_add' left right := by
  funext coordinate
  by_cases same : coordinate=index <;> simp only [same,if_true,if_false,Pi.add_apply,zero_add]
def query [DecidableEq Index] {sort : S} : List (Index × Expr Value Var sort) → Expr (VectorValue Index (Value:=Value)) Var sort
 | [] => .const 0
 | (index,term)::tail => .add (.linear (mask Index index) (expression Index term)) (query tail)
theorem query_read [DecidableEq Index] {sort : S} (items : List (Index × Expr Value Var sort))
 (source : Env Value Var) (coordinate : Index) :
 (query Index items).eval (environment Index source) coordinate=
 (items.map (fun item => if coordinate=item.1 then item.2.eval source else 0)).sum := by
 induction items with
 | nil => rfl
 | cons head tail previous =>
  rcases head with ⟨index,term⟩
  change (if coordinate=index then (expression Index term).eval (environment Index source) coordinate else 0)+
   (query Index tail).eval (environment Index source) coordinate = _
  rw [expression_read,previous]
  rfl
def charge {sort : S} : List (Index × Expr Value Var sort) → Nat
 | [] => 0
 | (_,term)::tail => remaining term+charge tail+2
theorem query_charge [DecidableEq Index] {sort : S} (items : List (Index × Expr Value Var sort)) :
 remaining (query Index items)=charge Index items := by
 induction items with
 | nil => rfl
 | cons head tail previous =>
  simp only [query,remaining,expression_charge,previous,charge]
  omega
end SaturationMonoid.SourceOperationExecution.InventoryVector
end
