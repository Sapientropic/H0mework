import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.History
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Effect.Transport
namespace E
export Lower.SourceFamily.Effect.Environment (nativeFrame nativeSeed nativeBinding scalarAt pairAt afterEnv nextEnv native_environment)
end E
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance wordsGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (originalBinding : ∀ t,X t → Expr W X t)
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
abbrev increment (n : Nat) := History.increment originalBinding initial firstCfg language n

abbrev observation (n : Nat) := History.read originalBinding initial firstCfg language n

theorem actual_word (firstCharge : 2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query initial firstCfg).raw.expression) (n : Nat) (word : Formal ℤ (PairValue (Lower.Value W (n+1))) X s) :
 evaluation (Value:=PairValue (PairValue (Lower.Value W (n+1)))) (R:=ℤ) (E.nextEnv originalBinding initial firstCfg language n) (liftMap word)=
 observation originalBinding initial firstCfg language n word := by
 rw [E.native_environment originalBinding initial firstCfg language firstCharge n]
 exact LinearMap.congr_fun (evaluation_liftMap (R:=ℤ) (s:=s)
  (E.afterEnv originalBinding initial firstCfg language n) (increment originalBinding initial firstCfg language n)) word

def wholeMorphism (firstCharge : 2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query initial firstCfg).raw.expression) (n : Nat) : Morphism (observation originalBinding initial firstCfg language n)
 (evaluation (Value:=PairValue (PairValue (Lower.Value W (n+1)))) (R:=ℤ) (s:=s) (E.nextEnv originalBinding initial firstCfg language n)) where
 sourceMap:=liftMap
 targetMap:=LinearMap.id
 commutes:=by
  apply LinearMap.ext
  intro word
  exact (actual_word originalBinding initial firstCfg language firstCharge n word).symm

theorem whole_residual (firstCharge : 2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query initial firstCfg).raw.expression) (n : Nat) (word : Formal ℤ (PairValue (Lower.Value W (n+1))) X s) :
 inducedResidualMap (wholeMorphism originalBinding initial firstCfg language firstCharge n)
  (canonicalResidual (observation originalBinding initial firstCfg language n) word)=
 canonicalResidual (evaluation (Value:=PairValue (PairValue (Lower.Value W (n+1)))) (R:=ℤ) (E.nextEnv originalBinding initial firstCfg language n)) (liftMap word) :=
 LinearMap.congr_fun (inducedResidualMap_comp_canonical (wholeMorphism originalBinding initial firstCfg language firstCharge n)) word

theorem residual_injective (firstCharge : 2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query initial firstCfg).raw.expression) (n : Nat) : Function.Injective
 (inducedResidualMap (wholeMorphism originalBinding initial firstCfg language firstCharge n)) := by
 intro left right same
 obtain ⟨leftWord,rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (observation originalBinding initial firstCfg language n)) left
 obtain ⟨rightWord,rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (observation originalBinding initial firstCfg language n)) right
 have observed := congrArg (fun residual => (residualToRange
  (evaluation (Value:=PairValue (PairValue (Lower.Value W (n+1)))) (R:=ℤ) (s:=s) (E.nextEnv originalBinding initial firstCfg language n)) residual).val) same
 change evaluation (Value:=PairValue (PairValue (Lower.Value W (n+1)))) (R:=ℤ) (E.nextEnv originalBinding initial firstCfg language n) (liftMap leftWord)=
  evaluation (Value:=PairValue (PairValue (Lower.Value W (n+1)))) (R:=ℤ) (E.nextEnv originalBinding initial firstCfg language n) (liftMap rightWord) at observed
 rw [actual_word originalBinding initial firstCfg language firstCharge,actual_word originalBinding initial firstCfg language firstCharge] at observed
 apply residualToRange_injective (observation originalBinding initial firstCfg language n)
 exact Subtype.ext observed
end Lower.SourceFamily.Effect.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
