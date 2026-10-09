import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Words
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual
namespace Future.Transport
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
variable (after : Env W X) (next : Env (PairValue W) X)
variable (generated : next=pairEnvironment after 0)

def morphism : Morphism (evaluation (R:=ℤ) (s:=s) after) (evaluation (R:=ℤ) (s:=s) next) where
 sourceMap:=liftMap
 targetMap:=Words.into
 commutes:=by
  rw [generated]
  exact (Words.morphism after).commutes

theorem word_value (generated : next=pairEnvironment after 0) (word : Formal ℤ W X s) : evaluation (R:=ℤ) next (liftMap word)=(evaluation after word,0) := by
 rw [generated]
 exact Words.lift_value after word

theorem residual_source (word : Formal ℤ W X s) : inducedResidualMap (morphism after next generated)
 (canonicalResidual (evaluation (R:=ℤ) after) word)=canonicalResidual (evaluation (R:=ℤ) next) (liftMap word) := by
 have natural := LinearMap.congr_fun (inducedResidualMap_comp_canonical (morphism after next generated)) word
 simpa only [LinearMap.comp_apply,morphism] using natural

theorem residual_zero_iff (generated : next=pairEnvironment after 0) (word : Formal ℤ W X s) : canonicalResidual (evaluation (R:=ℤ) next) (liftMap word)=0 ↔
 canonicalResidual (evaluation (R:=ℤ) after) word=0 := by
 rw [canonicalResidual_eq_zero_iff,canonicalResidual_eq_zero_iff,generated]
 exact Words.lifted_zero_iff after word

variable (before : Env W X)
abbrev increment := after-before

def updateMorphism : Morphism (updateInventory (R:=ℤ) (s:=s) before (increment after before))
 (evaluation (R:=ℤ) (s:=s) after) where
 sourceMap:=LinearMap.id
 targetMap:=additionReadout
 commutes:=by
  have existing := (SourceOperationScalarRelations.updateMorphism (R:=ℤ) (s:=s) before (increment after before)).commutes
  have envEq : before+increment after before=after := add_sub_cancel _ _
  change additionReadout.comp (updateInventory (R:=ℤ) (s:=s) before (increment after before))=
   (evaluation (R:=ℤ) (s:=s) (before+increment after before)).comp LinearMap.id at existing
  rw [envEq] at existing
  exact existing

def wholeMorphism : Morphism (updateInventory (R:=ℤ) (s:=s) before (increment after before))
 (evaluation (R:=ℤ) (s:=s) next) := (morphism after next generated).comp (updateMorphism after before)

theorem whole_value (generated : next=pairEnvironment after 0) (word : Formal ℤ W X s) :
 evaluation (R:=ℤ) next (liftMap word)=(evaluation before word+effectEvaluator before (increment after before) word,0) := by
 have value := word_value after next generated word
 have update := LinearMap.congr_fun (SourceOperationScalarRelations.evaluation_update (R:=ℤ) (s:=s) before (increment after before)) word
 have envEq : before+increment after before=after := add_sub_cancel _ _
 rw [envEq,LinearMap.add_apply] at update
 exact value.trans (congrArg (fun value : W s => (value,0)) update)

theorem whole_residual (word : Formal ℤ W X s) : inducedResidualMap (wholeMorphism (s:=s) after next generated before)
 (canonicalResidual (updateInventory (R:=ℤ) before (increment after before)) word)=
 canonicalResidual (evaluation (R:=ℤ) next) (liftMap word) := by
 have natural := LinearMap.congr_fun (inducedResidualMap_comp_canonical (wholeMorphism (s:=s) after next generated before)) word
 have mapEq : (wholeMorphism (s:=s) after next generated before).sourceMap=liftMap := by
  change liftMap.comp LinearMap.id=liftMap
  exact LinearMap.comp_id _
 simpa only [LinearMap.comp_apply,mapEq] using natural
end Future.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
