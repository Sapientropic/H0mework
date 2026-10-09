import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Source
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Source

/-! The complete next source term generates a typed relation programme.
Actual orbit substitution retains its proof trees and coefficients; the
existing retained-word compiler emits executable pair syntax from that word. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Relations
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceOperationScalarInventoryLift
namespace E
export SourceOperationInquiry.Context.Faces.Execution (expression expression_eval)
end E
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (cursor : Cursor (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

def nextExpression : Expr PhysicalValue (Orbit.Var PhysicalVar) sort := Orbit.embed cursor.next.raw.expression

def nextTrace : Trace cursor.next.orbitEnvironment (nextExpression cursor)
    (.const ((nextExpression cursor).eval cursor.next.orbitEnvironment)) :=
  execution cursor.next.orbitEnvironment (nextExpression cursor)

def sourceTrace : Trace (SourceSubstitution.sourceEnvironment Orbit.binding cursor.orbitEnvironment)
    (nextExpression cursor) (.const ((nextExpression cursor).eval cursor.next.orbitEnvironment)) :=
  cursor.shift_environment.symm ▸ nextTrace cursor

def programme : RelationIndex ℤ (SourceSubstitution.sourceEnvironment Orbit.binding cursor.orbitEnvironment) sort →₀ ℤ :=
  (sourceTrace cursor).relationWords (R := ℤ)

def actedProgramme : RelationIndex ℤ cursor.orbitEnvironment sort →₀ ℤ :=
  SourceSubstitution.relationWords Orbit.binding cursor.orbitEnvironment (programme cursor)

def word : Formal ℤ PhysicalValue (Orbit.Var PhysicalVar) sort :=
  relationMap (R := ℤ) cursor.orbitEnvironment (actedProgramme cursor)

theorem word_generated : word cursor = substitution (R := ℤ) Orbit.binding
    (Finsupp.single (nextExpression cursor) 1 -
      Finsupp.single (.const ((nextExpression cursor).eval cursor.next.orbitEnvironment)) 1) := by
  have square := LinearMap.congr_fun
    (SourceSubstitution.boundary_square (R := ℤ) (s := sort) Orbit.binding cursor.orbitEnvironment) (programme cursor)
  exact square.trans (congrArg (substitution (R := ℤ) Orbit.binding) (sourceTrace cursor).relation_boundary)

def pairRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue PhysicalValue) (Var := Orbit.Var PhysicalVar) (sort := sort) :=
  ⟨pairEnvironment cursor.orbitEnvironment (cursor.next.orbitEnvironment - cursor.orbitEnvironment),
    liftExpr (E.expression (word cursor))⟩

theorem pair_eval : (pairRaw cursor).expression.eval (pairRaw cursor).environment =
    updateInventory (R := ℤ) cursor.orbitEnvironment
      (cursor.next.orbitEnvironment - cursor.orbitEnvironment) (word cursor) := by
  change (liftExpr (E.expression (word cursor))).eval
    (pairEnvironment cursor.orbitEnvironment (cursor.next.orbitEnvironment - cursor.orbitEnvironment)) = _
  rw [eval_liftExpr, E.expression_eval]
  apply Prod.ext
  · rfl
  · apply add_left_cancel (a := evaluation (R := ℤ) cursor.orbitEnvironment (word cursor))
    change evaluation (R := ℤ) cursor.orbitEnvironment (word cursor) +
      (E.expression (word cursor)).effect cursor.orbitEnvironment (cursor.next.orbitEnvironment - cursor.orbitEnvironment) =
      evaluation (R := ℤ) cursor.orbitEnvironment (word cursor) +
        effectEvaluator (R := ℤ) cursor.orbitEnvironment (cursor.next.orbitEnvironment - cursor.orbitEnvironment) (word cursor)
    rw [← E.expression_eval (word cursor) cursor.orbitEnvironment, ← Expr.eval_update, E.expression_eval]
    simpa only [E.expression_eval, LinearMap.add_apply] using LinearMap.congr_fun (evaluation_update (R := ℤ)
      cursor.orbitEnvironment (cursor.next.orbitEnvironment - cursor.orbitEnvironment)) (word cursor)

theorem old_component : ((pairRaw cursor).expression.eval (pairRaw cursor).environment).1 = 0 :=
  (congrArg Prod.fst (pair_eval cursor)).trans
    (LinearMap.congr_fun (evaluation_relationMap (R := ℤ) (s := sort) cursor.orbitEnvironment) (actedProgramme cursor))

def complex := SourceSubstitution.complexMorphism (R := ℤ) (s := sort) Orbit.binding cursor.orbitEnvironment

end SourceOperationInquiry.Context.Native.Orbit.Installation.Relations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
