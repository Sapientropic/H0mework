import H0mework.Realization.Operations.Execution.Relations
import H0mework.Realization.Operations.Execution.Run
import H0mework.Realization.Operations.Substitution.Source
/-! Each original forward step runs the substituted source binding and
retains every generated intermediate. The actual transported trace is
constructed from source syntax, before its value or relation readout. -/

set_option autoImplicit false
namespace SaturationMonoid.SourceOperationExecution
open SourceOperationEffects SourceOperationScalarPresentation
noncomputable section
universe u v w w'
variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w} {Var' : Sorts → Type w'}
  [∀ sort, AddCommGroup (Value sort)]
variable (binding : ∀ sort, Var sort → Expr Value Var' sort) (environment : Env Value Var')

def Step.substitutedTrace {sort : Sorts} {before after : Expr Value Var sort} :
    Step (fun sort name => (binding sort name).eval environment) before after →
      Trace environment (before.subst binding) (after.subst binding)
  | .bind name => execution environment (binding _ name)
  | .addConst left right => Trace.single (.addConst left right)
  | .linearConst operation value => Trace.single (.linearConst operation value)
  | .bilinearConst operation left right => Trace.single (.bilinearConst operation left right)
  | .addLeft step => (substitutedTrace step).addLeft _
  | .addRight step => Trace.addRight _ (substitutedTrace step)
  | .linear operation step => Trace.linear operation (substitutedTrace step)
  | .bilinearLeft operation step => Trace.bilinearLeft operation (substitutedTrace step) _
  | .bilinearRight operation step => Trace.bilinearRight operation _ (substitutedTrace step)

def Trace.substitutedTrace {sort : Sorts} {before after : Expr Value Var sort} :
    Trace (fun sort name => (binding sort name).eval environment) before after →
      Trace environment (before.subst binding) (after.subst binding)
  | .nil expression => .nil (expression.subst binding)
  | .cons step tail => (step.substitutedTrace binding environment).append (substitutedTrace tail)

theorem substituted_charge {sort : Sorts} {before : Expr Value Var sort} {value : Value sort}
    (trace : Trace (fun sort name => (binding sort name).eval environment) before (.const value)) :
    (trace.substitutedTrace binding environment).length = remaining (before.subst binding) :=
  (trace.substitutedTrace binding environment).length_to_const

theorem substituted_boundary {sort : Sorts} {before after : Expr Value Var sort}
    (trace : Trace (fun sort name => (binding sort name).eval environment) before after) :
    SourceOperationScalarPresentation.relationMap (R := ℤ) environment
      (trace.substitutedTrace binding environment).relationWords =
        Finsupp.single (before.subst binding) 1 - Finsupp.single (after.subst binding) 1 :=
  (trace.substitutedTrace binding environment).relation_boundary
end
end SaturationMonoid.SourceOperationExecution
