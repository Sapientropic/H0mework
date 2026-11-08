import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveExternalSupplyControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeDeliveryJournal
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

abbrev before (saved : Cursor code) (index : Nat) := saved.source.feedbackState saved.entry index

def paidDelivery? (saved : Cursor code) (index : Nat) : Option (Nat × code.Packet) :=
  match saved.source.feedbackPolicy index,Feedback.decision code saved.entry (before saved index) with
  | some _,some chosen => match chosen.val with
    | .deliver serial => match (before saved index).frame.sent[serial]? with
      | none => none
      | some packet => if ∀ item ∈ code.law.rawItems (before saved index).current (code.deliveryCost packet.recipient),
          code.law.Valid item.before item.request then some (serial,packet) else none
    | _ => none
  | _,_ => none

-- The journal is generated only from completed source cuts. It has no receipt-list input.
def entries (saved : Cursor code) : List (Nat × Nat) :=
  (List.range saved.cut).filterMap fun index => (paidDelivery? saved index).map (fun found => (index,found.1))
def settled (saved : Cursor code) : List Nat := ((entries saved).map Prod.snd).dedup
-- This is the outstanding first-delivery obligation. Replays remain fresh paid actions.
def pending (saved : Cursor code) : List Nat :=
  (List.range (EventStep.seed saved).frame.sent.length).filter fun serial =>
    decide (.deliver serial ∈ code.eventAlphabet ∧ serial ∉ settled saved)
def feeWord (saved : Cursor code) := (pending saved).flatMap fun serial =>
  match (EventStep.seed saved).frame.sent[serial]? with
  | none => [] | some packet => code.deliveryCost packet.recipient

theorem paidDelivery_sound (saved : Cursor code) (index serial : Nat) (packet : code.Packet)
    (found : paidDelivery? saved index = some (serial,packet)) :
    ∃ policy chosen, saved.source.feedbackPolicy index = some policy ∧
      Feedback.decision code saved.entry (before saved index) = some chosen ∧ chosen.val = .deliver serial ∧
      (before saved index).frame.sent[serial]? = some packet ∧
      (∀ item ∈ code.law.rawItems (before saved index).current (code.deliveryCost packet.recipient),
        code.law.Valid item.before item.request) := by
  unfold paidDelivery? at found
  split at found <;> try contradiction
  rename_i policy chosen active decision
  split at found <;> try contradiction
  rename_i address event
  split at found <;> try contradiction
  rename_i stored present
  split at found <;> try contradiction
  rename_i paid
  have shape := Option.some.inj found
  cases Prod.mk.inj shape with
  | intro sameAddress samePacket =>
      subst address
      subst stored
      exact ⟨policy,chosen,active,decision,event,present,paid⟩

theorem every_entry_has_its_actual_paid_source (saved : Cursor code) (index serial : Nat)
    (member : (index,serial) ∈ entries saved) :
    index < saved.cut ∧ ∃ packet, paidDelivery? saved index = some (serial,packet) := by
  obtain ⟨cut,inside,found⟩ := List.mem_filterMap.mp member
  obtain ⟨foundPacket,delivered,shape⟩ := Option.map_eq_some_iff.mp found
  rcases foundPacket with ⟨address,packet⟩
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj shape
  exact ⟨List.mem_range.mp inside,packet,delivered⟩

theorem unfinished_cuts_are_not_published (saved : Cursor code) (serial : Nat) :
    (saved.cut,serial) ∉ entries saved := by
  intro member
  exact Nat.lt_irrefl _ (every_entry_has_its_actual_paid_source saved saved.cut serial member).1

theorem a_paid_source_cut_is_in_the_journal (saved : Cursor code) (index serial : Nat) (packet : code.Packet)
    (completed : index < saved.cut) (found : paidDelivery? saved index = some (serial,packet)) :
    (index,serial) ∈ entries saved :=
  List.mem_filterMap.mpr ⟨index,List.mem_range.mpr completed,by rw [found];rfl⟩

theorem settled_has_no_duplicate_liability (saved : Cursor code) : (settled saved).Nodup := List.nodup_dedup _

theorem confirmed_delivery_releases_first_delivery_reserve (saved : Cursor code) (index serial : Nat) (packet : code.Packet)
    (completed : index < saved.cut) (found : paidDelivery? saved index = some (serial,packet)) :
    serial ∉ pending saved := by
  have included : serial ∈ settled saved := by
    simp only [settled,List.mem_dedup]
    exact List.mem_map.mpr ⟨(index,serial),a_paid_source_cut_is_in_the_journal saved index serial packet completed found,rfl⟩
  intro present
  have unconfirmed := (of_decide_eq_true (List.mem_filter.mp present).2).2
  exact unconfirmed included
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeDeliveryJournal
