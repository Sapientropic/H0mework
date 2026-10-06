import H0mework.Realization.Operations.Execution.Coefficients.Words
import H0mework.Realization.Operations.Execution.Relations.History.Events
import H0mework.Realization.Operations.ScalarComplex
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.SourceOperationExecution.Cochain
open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {Value : S → Type u} {Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {sort : S}
variable (old increment : Env Value Var) (word : Formal ℤ Value Var sort)
def boundary := SourceOperationScalarCochain.boundary (R:=ℤ) word
def expression := Coefficients.expression (boundary word)
def trace := execution (mixedEnvironment old increment) (expression word)
def relations := (trace old increment word).relationWords (R:=ℤ)
def written := ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationPaidRelations.exposure
 (trace old increment word)
theorem source_zero : (expression word).eval (mixedEnvironment old increment)=0 :=
 (Coefficients.expression_eval _ _).trans
  (LinearMap.congr_fun (SourceOperationScalarCochain.evaluation_boundary (R:=ℤ) old increment) word)
theorem complete_charge : (trace old increment word).length=Coefficients.cost (boundary word) :=
 (execution_length _ _).trans (Coefficients.expression_remaining _)
theorem complete_steps : (ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationPaidRelations.words
 (trace old increment word)).length=(trace old increment word).length :=
 ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationPaidRelations.complete_steps _
theorem generated_boundary : relationMap (R:=ℤ) (mixedEnvironment old increment) (relations old increment word)=
 Finsupp.single (expression word) 1-Finsupp.single (Expr.const 0) 1 :=
 ((trace old increment word).relation_boundary (R:=ℤ)).trans
  (congrArg (fun value => Finsupp.single (expression word) 1-Finsupp.single (Expr.const value) 1)
   (source_zero old increment word))
end SaturationMonoid.SourceOperationExecution.Cochain
end
