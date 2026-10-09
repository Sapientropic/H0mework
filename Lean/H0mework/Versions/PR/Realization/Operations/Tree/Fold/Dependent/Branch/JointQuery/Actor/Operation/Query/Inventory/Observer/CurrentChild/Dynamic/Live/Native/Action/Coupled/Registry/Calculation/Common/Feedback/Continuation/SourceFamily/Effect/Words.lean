import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Payment
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Effect
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
variable (binding : ∀ t,X t → Expr W X t)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s)))
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (scalar : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) X s)))
variable (pair : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (PairValue W)) X s)))
variable (word : Formal ℤ (PairValue W) X s)
theorem actual_word : evaluation (R:=ℤ) (nextEnv binding seed frame scalar pair) (liftMap word)=
 updateInventory (R:=ℤ) (decoder binding seed frame scalar pair) (increment binding seed frame scalar pair) word := by
 have generated := LinearMap.congr_fun (evaluation_liftMap (R:=ℤ) (s:=s)
  (decoder binding seed frame scalar pair) (increment binding seed frame scalar pair)) word
 rw [actual_environment]
 exact generated

def wholeMorphism : Morphism (updateInventory (R:=ℤ) (s:=s) (decoder binding seed frame scalar pair) (increment binding seed frame scalar pair))
 (evaluation (R:=ℤ) (s:=s) (nextEnv binding seed frame scalar pair)) where
 sourceMap:=liftMap
 targetMap:=LinearMap.id
 commutes:=by
  rw [LinearMap.id_comp,actual_environment]
  exact (evaluation_liftMap _ _).symm

theorem whole_residual : inducedResidualMap (wholeMorphism binding seed frame scalar pair)
 (canonicalResidual (updateInventory (R:=ℤ) (decoder binding seed frame scalar pair) (increment binding seed frame scalar pair)) word)=
 canonicalResidual (evaluation (R:=ℤ) (nextEnv binding seed frame scalar pair)) (liftMap word) := by
 have natural := LinearMap.congr_fun (inducedResidualMap_comp_canonical (wholeMorphism binding seed frame scalar pair)) word
 exact natural
theorem whole_residual_injective : Function.Injective (inducedResidualMap (wholeMorphism binding seed frame scalar pair)) := by
 intro left right same
 obtain ⟨leftWord,rfl⟩ := Submodule.mkQ_surjective
  (LinearMap.ker (updateInventory (R:=ℤ) (s:=s) (decoder binding seed frame scalar pair) (increment binding seed frame scalar pair))) left
 obtain ⟨rightWord,rfl⟩ := Submodule.mkQ_surjective
  (LinearMap.ker (updateInventory (R:=ℤ) (s:=s) (decoder binding seed frame scalar pair) (increment binding seed frame scalar pair))) right
 have observed := congrArg (fun residual => (residualToRange
  (evaluation (R:=ℤ) (s:=s) (nextEnv binding seed frame scalar pair)) residual).val) same
 change evaluation (R:=ℤ) (nextEnv binding seed frame scalar pair) (liftMap leftWord)=
  evaluation (R:=ℤ) (nextEnv binding seed frame scalar pair) (liftMap rightWord) at observed
 rw [actual_word,actual_word] at observed
 apply residualToRange_injective (updateInventory (R:=ℤ) (s:=s) (decoder binding seed frame scalar pair) (increment binding seed frame scalar pair))
 exact Subtype.ext observed

end Lower.SourceFamily.Effect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
