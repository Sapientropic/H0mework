import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Completion
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.RawState

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace RegisteredRawTrace
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion (event next_state initial_state completedEvent)
end C
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw inputNext)
end O
variable {S:Type u} {U X:S→Type u} [∀t,AddCommGroup (U t)] {s:S}
variable {N:WorldRelationNetwork.{u}} {V:Vocabulary.{u}}
variable (old:SourceNativeAuthoritativeRootClosure N V) {origin:V.Current}
variable (registered:RootGeneratedDebtActivationJointSource.RegisteredAt (Value:=U) (Var:=X) (sort:=s) old.toLedgerRoot origin)
variable (packetAt:(current:V.Current)→RootGeneratedDebtActivationJointSource.Successor.Packet old.toLedgerRoot current)
def raw:O.Raw (Value:=U) (Var:=X) (sort:=s):=⟨registered.input.environment,registered.input.expression⟩
def rawHistoryState (input:O.Raw (Value:=U) (Var:=X) (sort:=s)) (count:Nat):
 SourceOperationExecutionDebt.State input.environment input.expression:=
 Nat.rec (SourceOperationExecutionDebt.initial input.environment input.expression)
  (fun _ prior=>O.inputNext input prior) count
abbrev historyState (count:Nat):=rawHistoryState (raw old registered) count

def rawWritten (input:O.Raw (Value:=U) (Var:=X) (sort:=s)):=
 SourceOperationPaidRelations.exposure (rawHistoryState input (remaining input.expression)).2

theorem step_raw {current:V.Current} (event:RootGeneratedDebtActivationJointSource.EventAt registered current):
 RootGeneratedDebtActivationJointSource.mathTarget event=O.inputNext (raw old registered) event.state:=by
 unfold RootGeneratedDebtActivationJointSource.mathTarget RootGeneratedDebtActivationJointSource.mathAction
  O.inputNext raw
 generalize SourceOperationExecutionDebt.generate registered.input.environment registered.input.expression event.state=selected
 cases selected <;>rfl

theorem event_state (count:Nat):(C.event old registered packetAt count).state=historyState old registered count:=by
 induction count with
 | zero=>rfl
 | succ count prior=>
  rw [C.next_state]
  apply (step_raw old registered (C.event old registered packetAt count)).trans
  exact congrArg (O.inputNext (raw old registered)) prior

theorem event_written (count:Nat):SourceOperationPaidRelations.exposure (C.event old registered packetAt count).state.2=
 SourceOperationPaidRelations.exposure (historyState old registered count).2:=
 congrArg (fun state:SourceOperationExecutionDebt.State registered.input.environment registered.input.expression=>
  SourceOperationPaidRelations.exposure state.2) (event_state old registered packetAt count)
theorem terminal_written:
 SourceOperationPaidRelations.exposure (C.completedEvent old registered packetAt).state.2=
 rawWritten (raw old registered):=event_written old registered packetAt _

variable (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=U) (Var:=X) (sort:=s))
variable (clock:frame.depth+1=remaining frame.registered.input.expression)
include clock in
theorem frame_written:
 SourceOperationPaidRelations.exposure
  (RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathAnswerFace
   frame.old frame.registered frame.packetAt frame.depth).rootRead.state.2=
 rawWritten (raw frame.old.root.toAuthoritativeRoot frame.registered):=
 (congrArg (fun state:SourceOperationExecutionDebt.State frame.registered.input.environment
  frame.registered.input.expression=>SourceOperationPaidRelations.exposure state.2)
  (SourceRegisteredClaimCompletion.terminal_state frame clock)).trans
  (terminal_written frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt)

end RegisteredRawTrace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
