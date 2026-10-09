import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Request.Consumer
import H0mework.Realization.Operations.Execution.Substitution.Source
import H0mework.Realization.Operations.Substitution.Complex
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedIncrementSubstitution
open SourceOperationEffects SourceOperationExecution
variable {S : Type u} {A X : S → Type u} [∀ slot,AddCommGroup (A slot)]
variable (old delta : Env A X)
def binding (slot : S) (name : X slot) : Expr A X slot := .add (.var name) (.const (delta slot name))
theorem environment : SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment (binding delta) old=old+delta := rfl
variable {slot : S}
def updatedTrace (expression : Expr A X slot) := execution (old+delta) expression
def substitutedTrace (expression : Expr A X slot) := Trace.substitutedTrace (binding delta) old (updatedTrace old delta expression)
theorem value (expression : Expr A X slot) : (expression.subst (binding delta)).eval old=expression.eval (old+delta) :=
 expression.eval_subst (binding delta) old
theorem charge (expression : Expr A X slot) : (substitutedTrace old delta expression).length=remaining (expression.subst (binding delta)) :=
 substituted_charge (binding delta) old (updatedTrace old delta expression)
def paidSubstitutedTrace (expression : Expr A X slot)
 (state : SourceOperationExecutionDebt.State (old+delta) expression)
 (settled : SourceOperationExecutionDebt.Settlement state) :
 Trace old (expression.subst (binding delta)) (.const settled.1) := by
 have source := state.2.substitutedTrace (binding delta) old
 have endpoint := congrArg (fun term : Expr A X slot => term.subst (binding delta)) settled.2.down
 rw [endpoint] at source
 exact source
end SourceGeneratedIncrementSubstitution
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Request.Update
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable (frame : Frame.{u})
abbrev binding := SourceGeneratedIncrementSubstitution.binding (actualMaterial frame).increment
abbrev before := (actualMaterial frame).environment
abbrev after := (registered frame).input.environment
theorem source_environment : SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment (binding frame) (before frame)=after frame := rfl
abbrev expression := R.expression (actualMaterial frame)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue Value.{u}) (Var:=Var.{u}) (sort:=Slot.orbit) :=
 ⟨before frame,(expression frame).subst (binding frame)⟩
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Request.Update
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
