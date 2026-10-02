import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Runtime
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Payment

/-! The source token cofaces transport the original fixed epoch process.
Its state and successor stay literal; payment now lives at the macro's root. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment
open SourceOperationEffects SourceOperationExecution DebtActivationWorld DebtActivationLedger RootInquiryCompletion CompilerFromPacketSourceLaw
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

abbrev baseProcess := Inquiry.Payment.process frame.old frame.registered frame.packetAt

def stateAt (state : (baseProcess frame).State) : SourceNativeLivingRootCurrentAt (World frame.registered) :=
  ⟨JointV frame.registered frame.packetAt, Inquiry.targetRoot frame.old frame.registered frame.packetAt,
    Restructuring.temporalVisit frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt state.down⟩

private def stateDepth (current : SourceNativeLivingRootCurrentAt (World frame.registered)) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

private theorem state_depth (state : (baseProcess frame).State) :
    stateDepth frame (stateAt frame state) = some state.down := by
  change some (ProductiveFiniteRootHistoryAt.causalDepth
    (Restructuring.finiteVisit frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt state.down).history) = _
  have depths : (count : Nat) → ProductiveFiniteRootHistoryAt.causalDepth
      (Restructuring.finiteVisit frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count).history = count := by
    intro count
    induction count with
    | zero => rfl
    | succ count prior => exact congrArg (fun value => value + 1) prior
  exact congrArg some (depths state.down)

/-- A source-installation transporter of the existing epoch registry. -/
def process : SourceNativeLivingRootProcess (World frame.registered) where
  State := (baseProcess frame).State
  stateAt := stateAt frame
  stateAt_injective := by
    intro first second same
    have depths := congrArg (stateDepth frame) same
    rw [state_depth, state_depth] at depths
    have values := Option.some.inj depths
    cases first
    cases second
    cases values
    rfl
  initial := (baseProcess frame).initial
  successorAt := fun state =>
    ⟨(baseProcess frame).successor state, by rfl, by rfl⟩

private theorem visit_current (count : Nat) :
    (Inquiry.finiteVisit frame.old frame.registered frame.packetAt count).current =
      (Restructuring.finiteVisit frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count).current := by
  induction count with
  | zero => rfl
  | succ count prior =>
      change targetCurrent frame.registered frame.packetAt
        (Inquiry.finiteVisit frame.old frame.registered frame.packetAt count).current =
        targetCurrent frame.registered frame.packetAt
          (Restructuring.finiteVisit frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count).current
      exact congrArg (targetCurrent frame.registered frame.packetAt) prior

private theorem state_eq : frame.event.state =
    (Inquiry.Payment.mathCurrent frame.old frame.registered frame.packetAt frame.depth).2.state :=
  congrArg (fun current : Current frame.registered => current.2.state) (visit_current frame (frame.depth + 1))

private def transportPaid {environment : Env Value Var} {raw : Expr Value Var sort}
    {first second : SourceOperationExecutionDebt.State environment raw}
    (same : first = second)
    (paid : GeneratedStepAt (Idle.law environment raw) first)
    (action : SourceOperationExecutionDebt.generate environment raw first = .inr paid) :
    Σ target : GeneratedStepAt (Idle.law environment raw) second,
      PLift (SourceOperationExecutionDebt.generate environment raw second = .inr target) := by
  cases same
  exact ⟨paid, ⟨action⟩⟩

def debtCurrent : SourceNativeRootDebtCurrentAt (process frame)
    (Inquiry.Payment.mathEntry frame.old frame.registered frame.packetAt 0) where
  state := ⟨frame.depth + 1⟩
  entry := Inquiry.Payment.mathEntry frame.old frame.registered frame.packetAt frame.depth
  sameDebt := Inquiry.Payment.rowLineage frame.old frame.registered frame.packetAt frame.depth

theorem debt_current_actual : (⟨World frame.registered, (debtCurrent frame).rooted.erase⟩ : AnyAuthoritativeRootCurrent.{u}) = frame.currentPresentation.erase := by
  apply congrArg (fun visit =>
    (⟨World frame.registered,
      ⟨JointV frame.registered frame.packetAt, (Inquiry.targetRoot frame.old frame.registered frame.packetAt).toAuthoritativeRoot,
        visit⟩⟩ : AnyAuthoritativeRootCurrent.{u}))
  have visits : (count : Nat) →
      Restructuring.finiteVisit frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count =
        Inquiry.finiteVisit frame.old frame.registered frame.packetAt count := by
    intro count
    induction count with
    | zero => rfl
    | succ count prior =>
        exact congrArg (fun visit => visit.next (by rfl)) prior
  exact congrArg SourceNativeTemporalVisitAt.finite (visits (frame.depth + 1))

def debtStep : SourceNativeRootDebtStepAt (debtCurrent frame) where
  targetEntry := (Inquiry.Payment.debtStep frame.old frame.registered frame.packetAt frame.depth).targetEntry
  evolution := (Inquiry.Payment.debtStep frame.old frame.registered frame.packetAt frame.depth).evolution
  sameDebtTarget_unique := (Inquiry.Payment.debtStep frame.old frame.registered frame.packetAt frame.depth).sameDebtTarget_unique

def payment
    (paid : GeneratedStepAt (scope frame.registered) frame.event.state)
    (action : frame.action = .inr paid) : SourceNativeRootDebtPaymentStepAt (debtCurrent frame) where
  step := debtStep frame
  strictDebit := by
    let generated := transportPaid (state_eq frame) paid action
    exact (Inquiry.Payment.payment frame.old frame.registered frame.packetAt frame.depth generated.1 generated.2.down).strictDebit

def generatePayment : SourceOperationExecutionDebt.Settlement frame.event.state ⊕
    SourceNativeRootDebtPaymentStepAt (debtCurrent frame) := by
  cases selected : frame.action with
  | inl settled => exact .inl settled
  | inr paid => exact .inr (payment frame paid selected)

def paidContinuation
    (paid : GeneratedStepAt (scope frame.registered) frame.event.state)
    (action : frame.action = .inr paid) : SourceNativePaidRootDebtMacroContinuationAt (debtCurrent frame) :=
  .ofPayment .refl (payment frame paid action) .refl

theorem continuation_wellFounded : WellFounded (SourceNativePaidRootDebtContinuationRel
    (process := process frame) (origin := Inquiry.Payment.mathEntry frame.old frame.registered frame.packetAt 0)) :=
  sourceNativePaidRootDebtContinuationRel_wellFounded


theorem process_state_preserved : (process frame).State = (baseProcess frame).State := rfl

theorem process_successor_preserved (state : (process frame).State) :
    (process frame).successor state = (baseProcess frame).successor state := rfl

theorem debt_step_receipt : HEq (debtStep frame).evolution
    (Inquiry.Payment.debtStep frame.old frame.registered frame.packetAt frame.depth).evolution := HEq.rfl

theorem no_refill : (debtStep frame).targetEntry.progressBudget ≤ (debtCurrent frame).budget :=
  (debtStep frame).progressBudget_not_refilled

theorem macro_current (initial : Frame (Value := Value) (Var := Var) (sort := sort)) (count : Nat) :
    ((Continuation.runtime initial).stateAt count).engine.node.erase =
      (⟨World (frames initial count).registered, (debtCurrent (frames initial count)).rooted.erase⟩ : AnyAuthoritativeRootCurrent.{u}) :=
  (Continuation.actual_current initial count).trans (debt_current_actual (frames initial count)).symm

end RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
