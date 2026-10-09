import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Transport
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual
namespace Future.Read
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
local instance readGroup (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
abbrev frameAt := Lower.frameAt initial firstCfg language
abbrev cfgAt := Lower.cfgAt initial firstCfg language
abbrev afterEnv (n : Nat) := SourceGeneratedInquiryReceiptAction.afterEnvironment (frameAt initial firstCfg language (n+1)) (cfgAt initial firstCfg language (n+1))
abbrev nextEnv (n : Nat) := (Future.Actual.Q.query (frameAt initial firstCfg language (n+2)) (cfgAt initial firstCfg language (n+2))).raw.environment
abbrev Word (n : Nat) := Formal ℤ (PairValue (Lower.Value W (n+1))) X s

def morphism (n : Nat)  := Transport.morphism (s:=s) (afterEnv initial firstCfg language n) (nextEnv initial firstCfg language n)
 (Tail.actual_tail_environment initial firstCfg language n)

theorem actual_word (n : Nat) (word : Word (W:=W) (X:=X) (s:=s) n) : evaluation (R:=ℤ) (nextEnv initial firstCfg language n) (liftMap word)=
 (evaluation (afterEnv initial firstCfg language n) word,0) :=
 Transport.word_value _ _ (Tail.actual_tail_environment initial firstCfg language n) word

theorem actual_residual (n : Nat) (word : Word (W:=W) (X:=X) (s:=s) n) :
 inducedResidualMap (morphism initial firstCfg language n) (canonicalResidual (evaluation (R:=ℤ) (afterEnv initial firstCfg language n)) word)=
 canonicalResidual (evaluation (R:=ℤ) (nextEnv initial firstCfg language n)) (liftMap word) := Transport.residual_source (s:=s) _ _ (Tail.actual_tail_environment initial firstCfg language n) word

theorem actual_fibre (n : Nat) (word : Word (W:=W) (X:=X) (s:=s) n) :
 canonicalResidual (evaluation (R:=ℤ) (nextEnv initial firstCfg language n)) (liftMap word)=0 ↔
 canonicalResidual (evaluation (R:=ℤ) (afterEnv initial firstCfg language n)) word=0 := Transport.residual_zero_iff (s:=s) _ _ (Tail.actual_tail_environment initial firstCfg language n) word

abbrev beforeEnv (n : Nat) := (Future.Actual.Q.query (frameAt initial firstCfg language (n+1)) (cfgAt initial firstCfg language (n+1))).raw.environment
abbrev increment (n : Nat) := afterEnv initial firstCfg language n-beforeEnv initial firstCfg language n

def wholeMorphism (n : Nat) := Transport.wholeMorphism (s:=s)
 (afterEnv initial firstCfg language n) (nextEnv initial firstCfg language n)
 (Tail.actual_tail_environment initial firstCfg language n) (beforeEnv initial firstCfg language n)

theorem actual_old_effect (n : Nat) (word : Word (W:=W) (X:=X) (s:=s) n) :
 evaluation (R:=ℤ) (nextEnv initial firstCfg language n) (liftMap word)=
 (evaluation (beforeEnv initial firstCfg language n) word+
  effectEvaluator (beforeEnv initial firstCfg language n) (increment initial firstCfg language n) word,0) := by
 have law := Transport.whole_value (s:=s)
  (afterEnv initial firstCfg language n) (nextEnv initial firstCfg language n)
  (beforeEnv initial firstCfg language n) (Tail.actual_tail_environment initial firstCfg language n) word
 exact law

theorem actual_whole_residual (n : Nat) (word : Word (W:=W) (X:=X) (s:=s) n) :
 inducedResidualMap (wholeMorphism initial firstCfg language n)
 (canonicalResidual (updateInventory (R:=ℤ) (beforeEnv initial firstCfg language n) (increment initial firstCfg language n)) word)=
 canonicalResidual (evaluation (R:=ℤ) (nextEnv initial firstCfg language n)) (liftMap word) :=
 Transport.whole_residual _ _ _ _ word
end Future.Read
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
