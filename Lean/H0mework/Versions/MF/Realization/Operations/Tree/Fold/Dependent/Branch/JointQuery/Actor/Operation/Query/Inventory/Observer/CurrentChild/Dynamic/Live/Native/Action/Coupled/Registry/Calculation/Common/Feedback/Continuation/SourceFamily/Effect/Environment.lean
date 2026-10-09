import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Installed
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Paid.Effect
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Environment.Generated
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement

namespace Lower.SourceFamily.Effect.Environment
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance environmentGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (originalBinding : ∀ t,X t → Expr W X t)
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
abbrev dataAt (n : Nat) := Lower.SourceFamily.tailData (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) originalBinding) initial firstCfg language n
abbrev nativeFrame (n : Nat) := (dataAt originalBinding initial firstCfg language n).1
abbrev nativeSeed (n : Nat) := (dataAt originalBinding initial firstCfg language n).2
abbrev nativeBinding (n : Nat) := Future.Replay.Binding.at originalBinding (n+1)
abbrev scalarAt (n : Nat) := Lower.SourceFamily.scalar (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) originalBinding)
  (n+1) (dataAt originalBinding initial firstCfg language n)
abbrev pairAt (n : Nat) := Lower.SourceFamily.pair (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) originalBinding)
  (n+1) (dataAt originalBinding initial firstCfg language n)
def afterEnv (n : Nat) : Env (PairValue (Lower.Value W (n+1))) X :=
  SourceGeneratedInquiryReceiptAction.afterEnvironment (nativeFrame originalBinding initial firstCfg language n)
    (Lower.SourceFamily.cfg (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) originalBinding) (n+1)
      (nativeSeed originalBinding initial firstCfg language n))
def nextEnv (n : Nat) : Env (PairValue (Lower.Value W (n+2))) X :=
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query
    (nativeFrame originalBinding initial firstCfg language (n+1))
    (Lower.SourceFamily.cfg (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) originalBinding) (n+2)
      (nativeSeed originalBinding initial firstCfg language (n+1)))).raw.environment

theorem native_environment
    (firstCharge : 2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query initial firstCfg).raw.expression)
    (n : Nat) : nextEnv originalBinding initial firstCfg language n =
      pairEnvironment (afterEnv originalBinding initial firstCfg language n)
        (SourceSubstitution.sourceEnvironment (Lower.SourceFamily.Effect.nextBinding (nativeBinding originalBinding n))
          (afterEnv originalBinding initial firstCfg language n)-afterEnv originalBinding initial firstCfg language n) :=
  Generated.generic_native_environment
    (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) originalBinding) originalBinding
    (Lower.SourceFamily.Foresight.Contextual.factory_environment originalBinding)
    initial firstCfg language (Lower.SourceFamily.Foresight.Contextual.factory_fee originalBinding) firstCharge n
end Lower.SourceFamily.Effect.Environment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
