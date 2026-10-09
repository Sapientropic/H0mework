import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Environment
import H0mework.Realization.ObservationActions.Algebraic
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Effect.History
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance historyGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (originalBinding : ∀ t,X t → Expr W X t)
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
abbrev Word (n : Nat) := Formal ℤ (PairValue (Lower.Value W (n+1))) X s
abbrev Pair (n : Nat) := PairValue (PairValue (Lower.Value W (n+1))) s

def action (n : Nat) : Word (W:=W) (X:=X) (s:=s) n →ₗ[ℤ] Word (W:=W) (X:=X) (s:=s) (n+1) := liftMap
abbrev environment (n : Nat) := Environment.afterEnv originalBinding initial firstCfg language n
def increment (n : Nat) := SourceSubstitution.sourceEnvironment
 (nextBinding (Environment.nativeBinding originalBinding n)) (environment originalBinding initial firstCfg language n)-
 environment originalBinding initial firstCfg language n
def read (n : Nat) : Word (W:=W) (X:=X) (s:=s) n →ₗ[ℤ] Pair (W:=W) (s:=s) n :=
 updateInventory (R:=ℤ) (environment originalBinding initial firstCfg language n) (increment originalBinding initial firstCfg language n)

def data (n : Nat) := AlgebraicDependent.data (action (W:=W) (X:=X) (s:=s)) (read originalBinding initial firstCfg language) n
theorem compatible (n : Nat) : (data originalBinding initial firstCfg language n).Compatible :=
 AlgebraicDependent.compatible _ _ n
abbrev completion (n : Nat) := AlgebraicDependent.completion (action (W:=W) (X:=X) (s:=s)) (read originalBinding initial firstCfg language) n
abbrev sourceMap (n : Nat) := AlgebraicDependent.sourceMap (action (W:=W) (X:=X) (s:=s)) (read originalBinding initial firstCfg language) n
abbrev successor (n : Nat) := AlgebraicDependent.successor (action (W:=W) (X:=X) (s:=s)) (read originalBinding initial firstCfg language) n

theorem source_prefix (n bound : Nat) (word : Word (W:=W) (X:=X) (s:=s) n) : type_of%
 (AlgebraicDependent.source_prefix (action (W:=W) (X:=X) (s:=s)) (read originalBinding initial firstCfg language) n bound word) :=
 AlgebraicDependent.source_prefix _ _ _ _ word

theorem source_fibre (n : Nat) (left right : Word (W:=W) (X:=X) (s:=s) n) : type_of%
 (AlgebraicDependent.source_fibre (action (W:=W) (X:=X) (s:=s)) (read originalBinding initial firstCfg language) n left right) :=
 AlgebraicDependent.source_fibre _ _ _ left right

theorem successor_source (n : Nat) (word : Word (W:=W) (X:=X) (s:=s) n) : type_of%
 (AlgebraicDependent.successor_source (action (W:=W) (X:=X) (s:=s)) (read originalBinding initial firstCfg language) n word) :=
 AlgebraicDependent.successor_source _ _ _ word

variable (firstCharge : 2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query initial firstCfg).raw.expression)
include firstCharge in
theorem actual_word (n : Nat) (word : Word (W:=W) (X:=X) (s:=s) n) :
 evaluation (R:=ℤ) (Environment.nextEnv originalBinding initial firstCfg language n) (action (W:=W) (X:=X) (s:=s) n word)=
 read originalBinding initial firstCfg language n word := by
 rw [Environment.native_environment originalBinding initial firstCfg language firstCharge n]
 exact LinearMap.congr_fun (evaluation_liftMap (R:=ℤ) (s:=s) (environment originalBinding initial firstCfg language n)
  (increment originalBinding initial firstCfg language n)) word
end Lower.SourceFamily.Effect.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
