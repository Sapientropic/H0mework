import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Consumer
import H0mework.Versions.Rdf421ff6.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualNativePaidPrefix
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace AS
export ActualSourceSegmentBornEffect.AS (AdmissionPacket localNativeReceipt localPaidAt stockCfg)
end AS
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next)
end S
namespace P
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment (process debtCurrent debtStep payment)
end P
namespace BP
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Payment
 (canonicalSuccessor destination_math actual_tick_receipt)
end BP
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_distance_exact)
end Complete
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance levelGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) :=
 L.groups W grade target
variable (native : AS.AdmissionPacket (W := W) (X := X) (s := s))
abbrev initial := native.2.1.1
abbrev configuration := AS.stockCfg native.2.2.1
local notation "f" => initial native
local notation "cfg" => configuration native

abbrev length := (AS.localNativeReceipt native).1

def frameAt (offset : Nat) : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
 (Value := L.Value W native.1) (Var := X) (sort := s) :=
 { f with depth := (f).depth + offset }

theorem actual_frame (offset : Nat) (within : offset ≤ length native) :
 S.frames f cfg (0+offset) = frameAt native offset := by
 induction offset with
 | zero => rfl
 | succ offset previous =>
  let paid := AS.localPaidAt native ⟨offset,by change offset < length native; omega⟩
  have step : S.frames f cfg (0+(offset+1)) =
   (S.frames f cfg (0+offset)).mathNext := by
   change S.next (S.frames f cfg (0+offset)) cfg = _
   unfold S.next
   rw [paid.2.down]
  exact step.trans (by rw [previous (by omega)]; rfl)

abbrev current (offset : Nat) : SourceNativeRootDebtCurrentAt (P.process f)
 (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Payment.mathEntry
  (f).old (f).registered (f).packetAt 0) := P.debtCurrent (frameAt native offset)

def actualPaid (offset : Fin (length native)) :
 Σ paid : DebtActivationWorld.GeneratedStepAt
  (RootGeneratedDebtActivationJointSource.law (frameAt native offset.val).registered)
  (frameAt native offset.val).event.state,
 PLift ((frameAt native offset.val).action = .inr paid) := by
 exact Eq.mp (congrArg (fun candidate : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
  (Value := L.Value W native.1) (Var := X) (sort := s) =>
   Σ paid : DebtActivationWorld.GeneratedStepAt
    (RootGeneratedDebtActivationJointSource.law candidate.registered) candidate.event.state,
   PLift (candidate.action = .inr paid))
  (actual_frame native offset.val (Nat.le_of_lt offset.isLt))) (AS.localPaidAt native offset)

def payment (offset : Fin (length native)) : SourceNativeRootDebtPaymentStepAt (current native offset.val) :=
 P.payment (frameAt native offset.val) (actualPaid native offset).1 (actualPaid native offset).2.down

private theorem debtCurrent_ext {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
 {support : N.Support} {origin : OpenResponsibilityAt N support}
 (left right : SourceNativeRootDebtCurrentAt process origin)
 (state : left.state = right.state) (entry : HEq left.entry right.entry) : left = right := by
 rcases left with ⟨firstState,firstEntry,firstDebt⟩
 rcases right with ⟨secondState,secondEntry,secondDebt⟩
 cases state
 cases entry
 cases firstDebt
 cases secondDebt
 rfl

theorem next_current (offset : Nat) :
 (current native offset).next (P.debtStep (frameAt native offset)) = current native (offset+1) := by
 apply debtCurrent_ext
 · rfl
 · exact heq_of_eq (BP.destination_math (f).old (f).registered (f).packetAt ((f).depth+offset))

/-- Only the already generated paid offsets enter this fixed registered process. -/
def between (start count : Nat) (within : start+count ≤ length native) :
 SourceNativeRootDebtMacroHistoryAt (current native start) (current native (start+count)) := by
 induction count with
 | zero => exact .refl
 | succ count previous =>
  have result := (previous (by omega)).snoc (P.debtStep (frameAt native (start+count)))
  simpa only [next_current, Nat.add_assoc] using result

def history : SourceNativeRootDebtMacroHistoryAt (current native 0) (current native (length native)) := by
 simpa only [Nat.zero_add] using between native 0 (length native) (by omega)

/-- A literal paid position supplies the payment; every other offset remains in its history. -/
def paidMacro (offset : Fin (length native)) : SourceNativePaidRootDebtMacroContinuationAt (current native 0) := by
 have before : SourceNativeRootDebtMacroHistoryAt (current native 0) (current native offset.val) := by
  simpa only [Nat.zero_add] using between native 0 offset.val (by omega)
 let after := between native (offset.val+1) (length native-(offset.val+1)) (by omega)
 have stop : offset.val+1+(length native-(offset.val+1)) = length native := by omega
 have retained : SourceNativeRootDebtMacroHistoryAt
  ((current native offset.val).next (payment native offset).step) (current native (length native)) := by
  change SourceNativeRootDebtMacroHistoryAt
   ((current native offset.val).next (P.debtStep (frameAt native offset.val))) _
  rw [next_current]
  simpa only [stop] using after
 exact .ofPayment before (payment native offset) retained

theorem macro_target (offset : Fin (length native)) :
 (paidMacro native offset).target = current native (length native) := rfl

def wholeSuccessor (offset : Nat) :=
 BP.canonicalSuccessor (f).old (f).registered (f).packetAt ((f).depth+offset)

theorem payment_whole_destination (offset : Fin (length native)) :
 HEq (payment native offset).step.evolution
  ((wholeSuccessor native offset.val).ledgerEvolution.destination (current native offset.val).entry).2 := HEq.rfl

theorem actual_tick_receipt (offset : Fin (length native)) : type_of%
 (BP.actual_tick_receipt (f).old (f).registered (f).packetAt ((f).depth+offset.val)) :=
 BP.actual_tick_receipt (f).old (f).registered (f).packetAt ((f).depth+offset.val)

theorem suffix_stop :
 (SourceRegisteredClaimClock.suffixHistory f).target =
 RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime
  (f).old.root.toAuthoritativeRoot (f).registered (f).packetAt ((f).depth+length native+1) := by
 change (SourceRegisteredClaimClock.currentRuntime f).advance
  (SourceRegisteredClaimClock.sourceRemainder f) = _
 rw [SourceRegisteredClaimClock.currentRuntime, SourceRegisteredClaimClock.runtime_advance]
 have distance : length native = SourceRegisteredClaimClock.sourceRemainder f :=
  Complete.receipt_distance_exact cfg f 0
 rw [distance]
 congr 1
 omega

end ActualNativePaidPrefix
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
