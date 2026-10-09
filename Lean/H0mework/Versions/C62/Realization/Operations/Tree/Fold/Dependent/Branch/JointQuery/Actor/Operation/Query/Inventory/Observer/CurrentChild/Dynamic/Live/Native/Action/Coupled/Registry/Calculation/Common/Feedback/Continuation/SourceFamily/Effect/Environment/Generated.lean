import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Installed
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Paid.Effect
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Effect.Environment.Generated
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query datum actualOccurrence)
end Q
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end E
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance sourceGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (source : Lower.SourceFamily.Factory W X s)
variable (binding : ∀ t,X t → Expr W X t)

def packetEnvironment (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n) :
    Env (PairValue (Lower.Value W n)) X :=
  (Q.query data.1 (Lower.SourceFamily.cfg source n data.2)).raw.environment
def packetAfter (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n) :
    Env (Lower.Value W (n+1)) X :=
  SourceGeneratedInquiryReceiptAction.afterEnvironment data.1 (Lower.SourceFamily.cfg source n data.2)
def packetDecoder (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n) : Env (Lower.Value W (n+1)) X :=
  (Lower.SourceFamily.receiver source n data).environment
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence
      (Lower.SourceFamily.receiver source n data).registered (Lower.SourceFamily.receiver source n data).packetAt
      (Q.actualOccurrence (Lower.SourceFamily.receiver source n data)))

theorem packet_decoder_paid (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
    (paid : DebtActivationWorld.GeneratedStepAt
      (RootGeneratedDebtActivationJointSource.Idle.law data.1.registered.input.environment data.1.registered.input.expression)
      data.1.event.state) (actual : data.1.action=.inr paid) :
    packetDecoder source n data = packetAfter source n data := by
  unfold packetAfter SourceGeneratedInquiryReceiptAction.afterEnvironment
  unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
  rw [actual]
  rfl

variable (sourceRaw : ∀ (n : Nat) (seed : Lower.SourceFamily.Seed W X s n)
    (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)),
    (Q.query frame (Lower.SourceFamily.cfg source n seed)).raw.environment =
      Future.Replay.Source.pairEnvironment (Future.Replay.Binding.at binding n)
        (E.epoch frame) (Q.actualOccurrence frame))

include sourceRaw in
theorem packet_step_environment (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
    (paid : DebtActivationWorld.GeneratedStepAt
      (RootGeneratedDebtActivationJointSource.Idle.law data.1.registered.input.environment data.1.registered.input.expression)
      data.1.event.state) (actual : data.1.action=.inr paid) :
    packetEnvironment source (n+1) (Lower.SourceFamily.step source n data) =
      pairEnvironment (packetAfter source n data)
        (SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding (n+1))
          (packetAfter source n data)-packetAfter source n data) := by
  have generated := sourceRaw (n+1) (Lower.SourceFamily.nextSeed source n data) (Lower.SourceFamily.receiver source n data)
  apply generated.trans
  have decoded : Future.Replay.physicalEnvironment (E.epoch (Lower.SourceFamily.receiver source n data))
      (Q.actualOccurrence (Lower.SourceFamily.receiver source n data)) = packetDecoder source n data := rfl
  exact congrArg (fun base : Env (Lower.Value W (n+1)) X =>
    pairEnvironment base (SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding (n+1)) base-base))
    (decoded.trans (packet_decoder_paid source n data paid actual))

variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
variable (sourceCharge : ∀ n seed frame, 2≤remaining
  (Q.query frame (Lower.SourceFamily.cfg source n seed)).raw.expression)

include sourceRaw sourceCharge in
theorem generic_native_environment
    (firstCharge : 2≤remaining (Q.query initial firstCfg).raw.expression) (n : Nat) :
    packetEnvironment source (n+2) (Lower.SourceFamily.tailData source initial firstCfg language (n+1)) =
      pairEnvironment (packetAfter source (n+1) (Lower.SourceFamily.tailData source initial firstCfg language n))
        (SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding (n+2))
          (packetAfter source (n+1) (Lower.SourceFamily.tailData source initial firstCfg language n))-
          packetAfter source (n+1) (Lower.SourceFamily.tailData source initial firstCfg language n)) := by
  rcases Lower.SourceFamily.Effect.PaidSource.native_paid_from_raw initial firstCfg language source sourceCharge firstCharge n
    with ⟨paid,selected⟩
  rw [Lower.SourceFamily.Foresight.Paid.tail_next]
  exact packet_step_environment source binding sourceRaw (n+1)
    (Lower.SourceFamily.tailData source initial firstCfg language n) paid selected
end Lower.SourceFamily.Effect.Environment.Generated

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
