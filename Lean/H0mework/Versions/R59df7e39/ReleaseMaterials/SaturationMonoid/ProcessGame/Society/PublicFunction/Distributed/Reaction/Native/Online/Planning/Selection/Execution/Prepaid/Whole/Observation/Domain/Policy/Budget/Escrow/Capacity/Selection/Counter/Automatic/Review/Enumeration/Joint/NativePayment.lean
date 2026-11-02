import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.NativePayment
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue}

variable {owner : Ready all} (made : Generated owner)

/-- An observed receipt in this exact, already paid outer history. -/
structure At where
  private mk ::
  event : Fin made.execution.work.length
  packet : Admission.Credit.Packet all
  observed : (made.execution.work[event]).creditLog owner = .tested packet

def observe (event : Fin made.execution.work.length) : Option (At made) :=
  match actual : (made.execution.work[event]).creditLog owner with
  | .tested packet => some ⟨event,packet,actual⟩
  | _ => none

namespace At
variable {made} (row : At made)
theorem segment : Admission.Credit.Segment (made.execution.work.map (Action.creditLog owner)) row.event.val row.packet := by
  apply made.all_native_receipts_have_actual_prior_credit_events owner row.event.val row.packet
  simpa only [Fin.getElem_fin,List.getElem?_map,List.getElem?_eq_getElem row.event.isLt,Option.map_some] using congrArg some row.observed

def creditEvent (native : Fin row.packet.receipt.checked.work.length) : Fin made.execution.work.length :=
  ⟨row.event.val-row.packet.receipt.prepaid+(row.packet.receipt.slot native).val,by
    have paid := row.segment.bounds.1
    have bounded := (row.packet.receipt.slot native).isLt
    have last := row.event.isLt
    omega⟩

theorem credit_precedes_receipt (native : Fin row.packet.receipt.checked.work.length) :
    (row.creditEvent native).val < row.event.val := by
  have paid := row.segment.bounds.1
  have bounded := (row.packet.receipt.slot native).isLt
  dsimp only [creditEvent];omega

theorem actual_credit (native : Fin row.packet.receipt.checked.work.length) :
    (made.execution.work[row.creditEvent native]).creditLog owner = .credit row.packet.tag native.val := by
  have paid := (row.segment.credit_at (row.packet.receipt.slot native)).2.2
  change (made.execution.work.map (Action.creditLog owner))[(row.creditEvent native).val]? = _ at paid
  simpa only [Fin.getElem_fin,List.getElem?_map,List.getElem?_eq_getElem (row.creditEvent native).isLt,
    Option.map_some,Option.some.injEq,Admission.Receipt.slot] using paid

def slot (index : Index prepared) (native : Fin row.packet.receipt.checked.work.length) := made.slot index (row.creditEvent native)
def nativeOperation (native : Fin row.packet.receipt.checked.work.length) := row.packet.receipt.checked.work[native]
def allocation (index : Index prepared) (native : Fin row.packet.receipt.checked.work.length) := made.allocation index (row.creditEvent native)

theorem slots_are_distinct (index : Index prepared) : Function.Injective (row.slot index) := by
  intro first second same
  have events := made.slots_are_not_reused index same
  have values := congrArg Fin.val events
  apply Fin.ext
  have paid := row.segment.bounds.1
  dsimp only [creditEvent,Admission.Receipt.slot] at values
  omega

theorem all_work_uses_the_original_successful_invoice (index : Index prepared) (native : Fin row.packet.receipt.checked.work.length) :
    (row.allocation index native).invoice.bill.payment.succeeded = true ∧
    (row.allocation index native).invoice.bill.units = owner.quota.val ∧
    (row.allocation index native).operation = made.execution.work[row.creditEvent native] ∧
    (row.allocation index native).slot.val = Review.offset owner+(row.creditEvent native).val ∧
    (made.execution.work[row.creditEvent native]).creditLog owner = .credit row.packet.tag native.val := by
  have original := made.every_event_uses_the_same_successful_invoice index (row.creditEvent native)
  exact ⟨original.1,original.2.1,original.2.2,rfl,row.actual_credit native⟩

theorem all_old_slots_are_separate (index : Index prepared) (old : owner.release.Token)
    (native : Fin row.packet.receipt.checked.work.length) : row.slot index native ≠ owner.release.slot index old :=
  made.all_old_slots_are_separate index old (row.creditEvent native)

theorem different_receipts_use_disjoint_slots (other : At made) (different : row.event ≠ other.event)
    (index : Index prepared) (left : Fin row.packet.receipt.checked.work.length)
    (right : Fin other.packet.receipt.checked.work.length) : row.slot index left ≠ other.slot index right := by
  intro reused
  have same := congrArg Fin.val (made.slots_are_not_reused index reused)
  have ordered : row.event.val ≠ other.event.val := fun equal => different (Fin.ext equal)
  have rowPaid := row.segment.bounds.1
  have otherPaid := other.segment.bounds.1
  have rowBound := (row.packet.receipt.slot left).isLt
  have otherBound := (other.packet.receipt.slot right).isLt
  rcases Nat.lt_or_gt_of_ne ordered with earlier | later
  · have apart := row.segment.separate other.segment earlier
    dsimp only [creditEvent] at same
    omega
  · have apart := other.segment.separate row.segment later
    dsimp only [creditEvent] at same
    omega

theorem observed_again : observe made row.event = some row := by
  unfold observe
  split
  · rename_i packet actual
    have equal := Admission.Credit.Log.tested.inj (actual.symm.trans row.observed)
    cases row
    cases equal
    rfl
  · rename_i actual
    rw [row.observed] at actual
    exact False.elim (actual row.packet rfl)
end At

/-- The complete audit directory of the history, including every source owner. -/
structure Book where
  private mk ::
  receipts : List (At made)
  generated : receipts = (List.finRange made.execution.work.length).filterMap (observe made)
def generate : Book made := ⟨(List.finRange made.execution.work.length).filterMap (observe made),rfl⟩
theorem every_actual_receipt_is_in_the_generated_book (row : At made) : row ∈ (generate made).receipts :=
  List.mem_filterMap.mpr ⟨row.event,List.mem_finRange _,row.observed_again⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.NativePayment
