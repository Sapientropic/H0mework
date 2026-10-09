import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Installation
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Effect
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query datum actualOccurrence)
end Q
namespace Faces
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower (configuration)
end Faces
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
variable (binding : ∀ t,X t → Expr W X t)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s)))
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
def cfg := Faces.configuration (Future.Replay.Installed.programme binding seed)
variable (scalar : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) X s)))
variable (pair : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (PairValue W)) X s)))
def receiver : M.Frame (Value:=PairValue W) (Var:=X) (sort:=s) := B.initial frame (cfg binding seed) scalar pair
def after : Env (PairValue W) X := SourceGeneratedInquiryReceiptAction.afterEnvironment frame (cfg binding seed)
def nextSeed := SourceHistoryCommon.seed scalar
 (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator (receiver binding seed frame scalar pair).registered.input.expression))
def nextBinding := Future.Replay.pairBinding binding
def nextCfg := Faces.configuration (Future.Replay.Installed.programme (nextBinding binding) (nextSeed binding seed frame scalar pair))
def before : Env (PairValue W) X := (Q.query frame (cfg binding seed)).raw.environment
def nextEnv : Env (PairValue (PairValue W)) X :=
 (Q.query (receiver binding seed frame scalar pair) (nextCfg binding seed frame scalar pair)).raw.environment

def sourceOccurrence := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence
 (receiver binding seed frame scalar pair).registered (receiver binding seed frame scalar pair).packetAt
 (Q.actualOccurrence (receiver binding seed frame scalar pair))
def decoder : Env (PairValue W) X := (receiver binding seed frame scalar pair).environment
 (sourceOccurrence binding seed frame scalar pair)

theorem same_source_decoder : decoder binding seed frame scalar pair=
 ((Q.datum frame (cfg binding seed)).reader (sourceOccurrence binding seed frame scalar pair)).environment := rfl

theorem receiver_source : Future.Replay.physicalEnvironment
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (receiver binding seed frame scalar pair))
 (Q.actualOccurrence (receiver binding seed frame scalar pair))=decoder binding seed frame scalar pair := rfl

def acted : Env (PairValue W) X := SourceSubstitution.sourceEnvironment (nextBinding binding)
 (decoder binding seed frame scalar pair)
def increment : Env (PairValue W) X := acted binding seed frame scalar pair-decoder binding seed frame scalar pair

theorem actual_environment : nextEnv binding seed frame scalar pair=
 pairEnvironment (decoder binding seed frame scalar pair) (increment binding seed frame scalar pair) := by
 change Future.Replay.actionPairEnvironment (nextBinding binding)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (receiver binding seed frame scalar pair))
  (Q.actualOccurrence (receiver binding seed frame scalar pair))=_
 exact congrArg (fun base : Env (PairValue W) X =>
  pairEnvironment base (SourceSubstitution.sourceEnvironment (nextBinding binding) base-base))
  (receiver_source binding seed frame scalar pair)


end Lower.SourceFamily.Effect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
