import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Model
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Foresight
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] sourceGroups
variable (binding : ∀ t,X t → Expr W X t) (state : L.State (W:=W) (X:=X) (s:=s))
abbrev actualBinding (k : Nat) := Future.Replay.Binding.at binding (stage binding state k)
abbrev decoder (k : Nat) := Lower.SourceFamily.Effect.decoder (actualBinding binding state k)
 (L.tail binding state k).2.2 (frame binding state k) (scalar binding state k) (pair binding state k)
abbrev increment (k : Nat) := Lower.SourceFamily.Effect.increment (actualBinding binding state k)
 (L.tail binding state k).2.2 (frame binding state k) (scalar binding state k) (pair binding state k)
theorem actual_environment (k : Nat) : environment binding state (k+1)=
 pairEnvironment (decoder binding state k) (increment binding state k) :=
 Lower.SourceFamily.Effect.actual_environment (actualBinding binding state k)
 (L.tail binding state k).2.2 (frame binding state k) (scalar binding state k) (pair binding state k)

theorem actual_word (t : S) (k : Nat) (word : Word binding state t k) :
 read binding state t (k+1) (action binding state t k word)=
 updateInventory (R:=ℤ) (decoder binding state k) (increment binding state k) word := by
 change evaluation (R:=ℤ) (environment binding state (k+1)) (liftMap word)=_
 rw [actual_environment]
 exact LinearMap.congr_fun (evaluation_liftMap (R:=ℤ) (s:=t) (decoder binding state k) (increment binding state k)) word

theorem actual_recovered_environment (k : Nat) : recoveredNext binding state k=
 pairEnvironment (decoder binding state k) (increment binding state k) :=
 (recovered_next binding state k).trans (actual_environment binding state k)

abbrev nextCfg (k : Nat) := cfg binding state (k+1)
def generated (k : Nat) := Lower.SourceFamily.Admission.generatedAction (frame binding state k) (cfg binding state k)
 (scalar binding state k) (pair binding state k) (nextCfg binding state k)
theorem actual_whole_root (k : Nat) : (generated binding state k).target.targetRoot=
 Lower.SourceFamily.StockObservation.root (frame binding state (k+1)) (nextCfg binding state k) :=
 Lower.SourceFamily.Admission.target_root (frame binding state k) (cfg binding state k)
 (scalar binding state k) (pair binding state k) (nextCfg binding state k)
 (Lower.SourceFamily.Admission.sourceEvent (frame binding state k) (cfg binding state k))
theorem actual_whole_next (k : Nat) : type_of%
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission.target_next
  (frame binding state k) (cfg binding state k) (scalar binding state k) (pair binding state k) (nextCfg binding state k)
  (Lower.SourceFamily.Admission.sourceEvent (frame binding state k) (cfg binding state k))) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission.target_next _ _ _ _ _ _

theorem actual_consumption (t : S) (k bound : Nat) (word : Word binding state t k) :
 type_of% (source_prefix binding state t k bound word) ∧
 type_of% (actual_word binding state t k word) ∧
 type_of% (actual_whole_root binding state k) ∧ type_of% (actual_whole_next binding state k) :=
 ⟨source_prefix _ _ _ _ _ _,actual_word _ _ _ _ _,actual_whole_root _ _ _,actual_whole_next _ _ _⟩

end Lower.SourceFamily.Foresight
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
