import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Payment

/-! The actual source cofaces transport the paid epoch restriction to the
activation root. The original registry state, successor and whole row are
retained; no authority is reconstructed from an erased ledger. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.Payment
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution DebtActivationWorld
namespace J
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (World JointV)
end J
namespace P
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment
  (process stateAt debtCurrent debtStep payment)
end P
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
namespace Shared
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (root presentation frames runtime actual_node)
end A
variable (programme : Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
variable (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

abbrev baseProcess := P.process frame

def stateAt (state : (baseProcess frame).State) : SourceNativeLivingRootCurrentAt (J.World frame.registered) :=
  ⟨J.JointV frame.registered frame.packetAt, A.root frame programme, (P.stateAt frame state).visit⟩

private def depthAt (current : SourceNativeLivingRootCurrentAt (J.World frame.registered)) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

private theorem depth_state (state : (baseProcess frame).State) :
    depthAt frame (stateAt programme frame state) = some state.down := by
  change some (ProductiveFiniteRootHistoryAt.causalDepth
    (RootGeneratedDebtActivationJointSource.Successor.Restructuring.finiteVisit
      frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt state.down).history) = _
  have depths : (count : Nat) → ProductiveFiniteRootHistoryAt.causalDepth
      (RootGeneratedDebtActivationJointSource.Successor.Restructuring.finiteVisit
        frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count).history = count := by
    intro count
    induction count with
    | zero => rfl
    | succ count prior => exact congrArg (fun value => value + 1) prior
  exact congrArg some (depths state.down)

def process : SourceNativeLivingRootProcess (J.World frame.registered) where
  State := (baseProcess frame).State
  stateAt := stateAt programme frame
  stateAt_injective := by
    intro first second same
    have depths := congrArg (depthAt frame) same
    rw [depth_state, depth_state] at depths
    have values := Option.some.inj depths
    cases first
    cases second
    cases values
    rfl
  initial := (baseProcess frame).initial
  successorAt := fun state => ⟨(baseProcess frame).successor state, by rfl, by rfl⟩

def debtCurrent : SourceNativeRootDebtCurrentAt (process programme frame)
    (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Payment.mathEntry
      frame.old frame.registered frame.packetAt 0) where
  state := (P.debtCurrent frame).state
  entry := (P.debtCurrent frame).entry
  sameDebt := (P.debtCurrent frame).sameDebt

def debtStep : SourceNativeRootDebtStepAt (debtCurrent programme frame) where
  targetEntry := (P.debtStep frame).targetEntry
  evolution := (P.debtStep frame).evolution
  sameDebtTarget_unique := (P.debtStep frame).sameDebtTarget_unique

def payment (paid : GeneratedStepAt
    (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment
      frame.registered.input.expression) frame.event.state)
    (action : frame.action = .inr paid) : SourceNativeRootDebtPaymentStepAt (debtCurrent programme frame) where
  step := debtStep programme frame
  strictDebit := (P.payment frame paid action).strictDebit

def generatePayment : SourceOperationExecutionDebt.Settlement frame.event.state ⊕
    SourceNativeRootDebtPaymentStepAt (debtCurrent programme frame) := by
  cases selected : frame.action with
  | inl settled => exact .inl settled
  | inr paid => exact .inr (payment programme frame paid selected)

theorem process_state_preserved : (process programme frame).State = (baseProcess frame).State := rfl

theorem process_successor_preserved (state : (process programme frame).State) :
    (process programme frame).successor state = (baseProcess frame).successor state := rfl

theorem receipt_preserved : HEq (debtStep programme frame).evolution (P.debtStep frame).evolution := HEq.rfl

end Shared

variable (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
abbrev baseProcess := Shared.baseProcess frame
abbrev stateAt := Shared.stateAt originalProgramme frame
abbrev process := Shared.process originalProgramme frame
abbrev debtCurrent := Shared.debtCurrent originalProgramme frame
abbrev debtStep := Shared.debtStep originalProgramme frame
abbrev payment := Shared.payment originalProgramme frame
abbrev generatePayment := Shared.generatePayment originalProgramme frame
abbrev process_state_preserved := Shared.process_state_preserved originalProgramme frame
abbrev process_successor_preserved := Shared.process_successor_preserved originalProgramme frame
abbrev receipt_preserved := Shared.receipt_preserved originalProgramme frame

end SourceOperationInquiry.Context.Faces.Execution.Activation.Payment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
