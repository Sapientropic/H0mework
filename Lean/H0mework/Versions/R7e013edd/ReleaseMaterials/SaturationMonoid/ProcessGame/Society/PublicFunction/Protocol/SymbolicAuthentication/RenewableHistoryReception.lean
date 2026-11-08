import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableCodeLineage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryReception
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {root : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
 (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law root) (origin : Cursor root) (past : List (EventHistory.Stage (code := root)))
 (recipient : Fin root.sites)

def check (row : RenewableCodeLineage.Row root) (seen : List (Nat×Nat)) (wire : HeaderTransport.Wire (code := root)) :
 HeaderReception.Verdict (code := root) :=
 let actual := row.material
 if StageReception.delivered actual wire.serial≠true then .rejected .missingDelivery
 else if ¬wire.sendCut<actual.cursor.cut then .rejected .unauthenticated
 else if HeaderTransport.verify vocabulary origin past wire≠true then .rejected .unauthenticated
 else if StageReception.matchingPacket actual wire≠true then .rejected .missingPacket
 else if wire.recipient≠recipient then .rejected .wrongRecipient
 else if wire.ballot.scope≠law.scope recipient actual.before.current then .rejected .staleScope
 else if ¬actual.cursor.cut≤wire.sendCut+law.maxDelay then .rejected .late
 else if ¬∀ item∈StageTrace.items actual,
   (CatalogueHandoffSource.code root row.catalogue).law.Valid item.before item.request then .rejected .unpaidDelivery
 else if (wire.ballot.cut,wire.ballot.position)∈seen then .rejected .duplicate
 else .accepted wire

theorem check_sound (row : RenewableCodeLineage.Row root) (seen : List (Nat×Nat))
 (wire result : HeaderTransport.Wire (code := root))
 (accepted : check vocabulary law origin past recipient row seen wire=.accepted result) :
 result=wire ∧ StageReception.delivered row.material wire.serial=true ∧ wire.sendCut<row.material.cursor.cut ∧
 HeaderTransport.verify vocabulary origin past wire=true ∧
 StageReception.matchingPacket row.material wire=true ∧ wire.recipient=recipient ∧
 wire.ballot.scope=law.scope recipient row.material.before.current ∧
 row.material.cursor.cut≤wire.sendCut+law.maxDelay ∧
 (∀ item∈StageTrace.items row.material,
  (CatalogueHandoffSource.code root row.catalogue).law.Valid item.before item.request) ∧
 (wire.ballot.cut,wire.ballot.position)∉seen := by
 unfold check at accepted
 dsimp only at accepted
 split_ifs at accepted with delivered earlier authenticated matched addressed sameScope timely paid unused
 cases accepted
 exact ⟨rfl,of_not_not delivered,earlier,of_not_not authenticated,of_not_not matched,
  of_not_not addressed,of_not_not sameScope,timely,paid,unused⟩

def incoming (row : RenewableCodeLineage.Row root) : Option (HeaderTransport.Wire (code := root)) :=
 (HeaderTransport.wires vocabulary origin past).find? (fun wire => StageReception.delivered row.material wire.serial)

def receive (row : RenewableCodeLineage.Row root) (index : Nat) (prior : HeaderReception.Receiver (code := root)) :
 HeaderReception.Receiver (code := root) :=
 let candidate := incoming vocabulary origin past row
 let verdict := match candidate with
 | none => AttestationReception.VerdictData.rejected .missingWire
 | some wire => check vocabulary law origin past recipient row
    (prior.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire
 ⟨match verdict with
  | .accepted wire => prior.receipts++[⟨wire,index,row.material.cursor.cut⟩]
  | .rejected _ => prior.receipts,
  prior.audit++[(row.material.cursor.cut,candidate,verdict)]⟩

def scan (rows : List (RenewableCodeLineage.Row root)) (offset : Nat)
 (prior : HeaderReception.Receiver (code := root)) : HeaderReception.Receiver (code := root) :=
 (List.rec (motive := fun _ => Nat → HeaderReception.Receiver (code := root) → HeaderReception.Receiver (code := root))
  (fun _ prior => prior) (fun row _tail recur offset prior =>
   recur (offset+1) (receive vocabulary law origin past recipient row offset prior)) rows) offset prior

theorem fresh_receipt_has_its_original_source_and_actual_row
 (row : RenewableCodeLineage.Row root) (index : Nat) (prior : HeaderReception.Receiver (code := root))
 (receipt : HeaderReception.Receipt (code := root))
 (inside : receipt∈(receive vocabulary law origin past recipient row index prior).receipts) :
 receipt∈prior.receipts ∨ (receipt.index=index ∧ receipt.delivery=row.material.cursor.cut ∧
 ∃ seen, check vocabulary law origin past recipient row seen receipt.wire=.accepted receipt.wire) := by
 unfold receive at inside
 dsimp only at inside
 split at inside
 · rename_i wire accepted
   rcases List.mem_append.mp inside with old | new
   · exact Or.inl old
   · cases List.mem_singleton.mp new
     cases found : incoming vocabulary origin past row with
     | none => simp only [found] at accepted; contradiction
     | some candidate =>
       simp only [found] at accepted
       obtain ⟨rfl,_⟩ := check_sound _ _ _ _ _ _ _ _ _ accepted
       exact Or.inr ⟨rfl,rfl,_,accepted⟩
 · exact Or.inl inside

theorem all_received_ballots_keep_the_original_paid_issuing_ledger
 (rows : List (RenewableCodeLineage.Row root)) (offset : Nat) (prior : HeaderReception.Receiver (code := root))
 (original : ∀ receipt∈prior.receipts,receipt.wire.ballot∈StageBudget.ledger vocabulary origin past) :
 ∀ receipt∈(scan vocabulary law origin past recipient rows offset prior).receipts,
 receipt.wire.ballot∈StageBudget.ledger vocabulary origin past := by
 induction rows generalizing offset prior with
 | nil => exact original
 | cons row tail ih =>
   apply ih (offset+1) (receive vocabulary law origin past recipient row offset prior)
   intro receipt inside
   rcases fresh_receipt_has_its_original_source_and_actual_row vocabulary law origin past recipient row offset prior receipt inside with old | fresh
   · exact original receipt old
   · obtain ⟨_,_,seen,accepted⟩ := fresh
     have verified := (check_sound _ _ _ _ _ _ _ _ _ accepted).2.2.2.1
     obtain ⟨_,_,_,_,_,_,_,paid,_⟩ := HeaderTransport.authenticated_wire_has_actual_send_and_paid_ballot
      vocabulary origin past receipt.wire verified
     exact paid

theorem every_received_receipt_locates_its_actual_descendant_row
 (rows : List (RenewableCodeLineage.Row root)) (offset : Nat) (prior : HeaderReception.Receiver (code := root))
 (receipt : HeaderReception.Receipt (code := root))
 (inside : receipt∈(scan vocabulary law origin past recipient rows offset prior).receipts) :
 receipt∈prior.receipts ∨ ∃ index row, rows[index]?=some row ∧ receipt.index=offset+index ∧
 receipt.delivery=row.material.cursor.cut ∧
 ∃ seen, check vocabulary law origin past recipient row seen receipt.wire=.accepted receipt.wire := by
 induction rows generalizing offset prior with
 | nil => exact Or.inl inside
 | cons row tail ih =>
   rcases ih (offset+1) (receive vocabulary law origin past recipient row offset prior) inside with earlier | later
   · rcases fresh_receipt_has_its_original_source_and_actual_row vocabulary law origin past recipient row offset prior receipt earlier with old | fresh
     · exact Or.inl old
     · obtain ⟨index,delivery,seen,checked⟩ := fresh
       exact Or.inr ⟨0,row,rfl,by simpa only [Nat.add_zero] using index,delivery,seen,checked⟩
   · obtain ⟨index,actual,found,whereFrom,delivery,seen,checked⟩ := later
     exact Or.inr ⟨index+1,actual,found,by omega,delivery,seen,checked⟩

theorem scan_append (before more : List (RenewableCodeLineage.Row root)) (offset : Nat)
 (prior : HeaderReception.Receiver (code := root)) :
 scan vocabulary law origin past recipient (before++more) offset prior=
 scan vocabulary law origin past recipient more (offset+before.length)
  (scan vocabulary law origin past recipient before offset prior) := by
 induction before generalizing offset prior with
 | nil => rfl
 | cons row tail ih =>
   change scan vocabulary law origin past recipient (tail++more) (offset+1)
    (receive vocabulary law origin past recipient row offset prior)=_
   rw [ih]
   simp only [List.length_cons]
   congr 1
   omega

theorem scan_keeps_all_prior_receipts (rows : List (RenewableCodeLineage.Row root)) (offset : Nat)
 (prior : HeaderReception.Receiver (code := root)) :
 prior.receipts <+: (scan vocabulary law origin past recipient rows offset prior).receipts := by
 induction rows generalizing offset prior with
 | nil => exact List.prefix_refl _
 | cons row tail ih =>
   apply List.IsPrefix.trans (l₂ := (receive vocabulary law origin past recipient row offset prior).receipts)
   · unfold receive
     dsimp only
     split <;> first | exact List.prefix_append _ _ | exact List.prefix_refl _
   · exact ih (offset+1) _

theorem duplicate_births_cannot_be_added_across_any_descendant_codes
 (rows : List (RenewableCodeLineage.Row root)) (offset : Nat) (prior : HeaderReception.Receiver (code := root))
 (distinct : (prior.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)).Nodup) :
 ((scan vocabulary law origin past recipient rows offset prior).receipts.map
  fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)).Nodup := by
 induction rows generalizing offset prior with
 | nil => exact distinct
 | cons row tail ih =>
   apply ih (offset+1) (receive vocabulary law origin past recipient row offset prior)
   unfold receive
   dsimp only
   split
   · rename_i wire outcome
     have fresh : (wire.ballot.cut,wire.ballot.position)∉
      prior.receipts.map (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) := by
       cases found : incoming vocabulary origin past row with
       | none => simp only [found] at outcome; contradiction
       | some candidate =>
         simp only [found] at outcome
         obtain ⟨rfl,_,_,_,_,_,_,_,_,unused⟩ := check_sound _ _ _ _ _ _ _ _ _ outcome
         exact unused
     simpa using List.nodup_append.mpr ⟨distinct,by simp,by simpa using fresh⟩
   · exact distinct

theorem actual_delivery_conditions_generate_the_next_receipt
 (row : RenewableCodeLineage.Row root) (index : Nat) (prior : HeaderReception.Receiver (code := root))
 (wire : HeaderTransport.Wire (code := root))
 (found : incoming vocabulary origin past row=some wire)
 (afterSend : wire.sendCut<row.material.cursor.cut)
 (packet : StageReception.matchingPacket row.material wire=true)
 (address : wire.recipient=recipient)
 (scope : wire.ballot.scope=law.scope recipient row.material.before.current)
 (timely : row.material.cursor.cut≤wire.sendCut+law.maxDelay)
 (paid : ∀ item∈StageTrace.items row.material,
  (CatalogueHandoffSource.code root row.catalogue).law.Valid item.before item.request)
 (unused : (wire.ballot.cut,wire.ballot.position)∉
  prior.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) :
 (receive vocabulary law origin past recipient row index prior).receipts=
 prior.receipts++[⟨wire,index,row.material.cursor.cut⟩] := by
 have verified : HeaderTransport.verify vocabulary origin past wire=true := decide_eq_true (List.mem_of_find?_eq_some found)
 have delivered := List.find?_some found
 have checked : check vocabulary law origin past recipient row
  (prior.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire=.accepted wire := by
  unfold check
  dsimp only
  rw [if_neg (not_not.mpr delivered),if_neg (not_not.mpr afterSend),if_neg (not_not.mpr verified),
   if_neg (not_not.mpr packet),if_neg (not_not.mpr address),if_neg (not_not.mpr scope),
   if_neg (not_not.mpr timely),if_neg (not_not.mpr paid),if_neg unused]
 simp only [receive,found,checked]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryReception
