import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Tail
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
namespace Future.Words
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
variable (after : Env W X)
def into : W s →ₗ[ℤ] PairValue W s := (LinearMap.id).prod 0

theorem effect_zero : effectEvaluator (R:=ℤ) (s:=s) after 0=0 := by
 apply Finsupp.lhom_ext
 intro expression coefficient
 simp only [effectEvaluator,Finsupp.linearCombination_single,Expr.effect_zero,smul_zero,LinearMap.zero_apply]

theorem lift_value (word : Formal ℤ W X s) :
 evaluation (R:=ℤ) (pairEnvironment after 0) (liftMap word)=(evaluation after word,0) := by
 have square := LinearMap.congr_fun (evaluation_liftMap (R:=ℤ) (s:=s) after (0:Env W X)) word
 rw [LinearMap.comp_apply] at square
 simpa only [updateInventory,LinearMap.prod_apply,effect_zero,LinearMap.zero_apply,Function.prod] using square

def morphism : SourceGeneratedScalarDifferentialResidual.Morphism (evaluation (R:=ℤ) (s:=s) after)
 (evaluation (R:=ℤ) (s:=s) (pairEnvironment after 0)) where
 sourceMap:=liftMap
 targetMap:=into
 commutes:=by
  apply LinearMap.ext
  intro word
  exact (lift_value after word).symm

theorem lifted_zero_iff (word : Formal ℤ W X s) : evaluation (R:=ℤ) (pairEnvironment after 0) (liftMap word)=0 ↔ evaluation after word=0 := by
 rw [lift_value]
 constructor
 · intro same
   exact congrArg Prod.fst same
 · intro same
   rw [same]
   rfl
end Future.Words
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
