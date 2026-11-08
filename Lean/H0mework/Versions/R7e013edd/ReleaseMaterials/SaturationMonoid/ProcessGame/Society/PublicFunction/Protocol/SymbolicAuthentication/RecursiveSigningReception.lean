import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecursiveSigningSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecursiveSigningReception
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code)

-- Authentication remains at the original issuing segment. Delivery rows may be
-- from any later segment of the same actual history; its phase and deadline stay old.
def incoming (origin : Segment bound) (row : StageTrace.Record (code := bound.source.code)) :=
 (origin.wires bound base).find? (fun wire => HeaderReception.delivered row wire.serial)

def receive (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (index : Nat) (row : StageTrace.Record (code := bound.source.code))
 (previous : HeaderReception.Receiver (code := bound.source.code)) : HeaderReception.Receiver (code := bound.source.code) :=
 let candidate := incoming bound base origin row
 let verdict := match candidate with
  | none => AttestationReception.VerdictData.rejected .missingWire
  | some wire => HeaderReception.check (origin.vocabulary bound base) (origin.law bound law)
    origin.origin origin.stages receiver row
    (previous.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire
 ⟨match verdict with
   | .accepted wire => previous.receipts ++ [⟨wire,index,row.cursor.cut⟩]
   | .rejected _ => previous.receipts,
  previous.audit ++ [(row.cursor.cut,candidate,verdict)]⟩

def scan (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (rows : List (StageTrace.Record (code := bound.source.code)))
 (offset : Nat) (previous : HeaderReception.Receiver (code := bound.source.code)) :
 HeaderReception.Receiver (code := bound.source.code) :=
 ((List.zipIdx rows offset).foldl fun seen row => receive bound base law origin receiver row.2 row.1 seen) previous

theorem actual_delivery_conditions_generate_the_next_receipt
 (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (index : Nat) (row : StageTrace.Record (code := bound.source.code))
 (previous : HeaderReception.Receiver (code := bound.source.code))
 (wire : HeaderTransport.Wire (code := bound.source.code))
 (found : incoming bound base origin row=some wire)
 (afterSend : wire.sendCut<row.cursor.cut)
 (packet : HeaderReception.matchingPacket row wire=true)
 (address : wire.recipient=receiver)
 (scope : wire.ballot.scope=(origin.law bound law).scope receiver row.before.current)
 (timely : row.cursor.cut ≤ wire.sendCut+law.maxDelay)
 (paid : ∀ item ∈ StageTrace.items row, bound.source.code.law.Valid item.before item.request)
 (unused : (wire.ballot.cut,wire.ballot.position) ∉
  previous.receipts.map (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position))) :
 (receive bound base law origin receiver index row previous).receipts=
  previous.receipts++[⟨wire,index,row.cursor.cut⟩] := by
 have member := List.mem_of_find?_eq_some found
 have delivered := List.find?_some found
 have verified : HeaderTransport.verify (origin.vocabulary bound base) origin.origin origin.stages wire=true :=
  decide_eq_true member
 have yes : HeaderReception.check (origin.vocabulary bound base) (origin.law bound law)
  origin.origin origin.stages receiver row
  (previous.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire=.accepted wire := by
   simp_all [HeaderReception.check,Segment.law]
 simp only [receive,found,yes]

theorem duplicate_origin_cannot_add_another_receipt
 (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (rows : List (StageTrace.Record (code := bound.source.code))) (offset : Nat)
 (previous : HeaderReception.Receiver (code := bound.source.code))
 (unique : (previous.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)).Nodup) :
 ((scan bound base law origin receiver rows offset previous).receipts.map
  fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)).Nodup := by
 induction rows generalizing offset previous with
 | nil => exact unique
 | cons row tail ih =>
   apply ih (offset+1) (receive bound base law origin receiver offset row previous)
   unfold receive
   dsimp only
   split
   · rename_i wire outcome
     have fresh : (wire.ballot.cut,wire.ballot.position) ∉
      previous.receipts.map (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) := by
       cases found : incoming bound base origin row with
       | none => simp only [found] at outcome; contradiction
       | some candidate =>
         simp only [found] at outcome
         obtain ⟨rfl,_,_,_,_,_,_,_,_,unused⟩ := HeaderReception.check_sound _ _ _ _ _ _ _ _ _ outcome
         exact unused
     simpa using List.nodup_append.mpr ⟨unique,by simp,by simpa using fresh⟩
   · exact unique

abbrev observed (genesis : Cursor bound.source.code) (state : State bound genesis)
 (origin : Segment bound) (receiver : Fin bound.source.code.sites) :=
 scan bound base law origin receiver (state.rows bound genesis) 0 ⟨[],[]⟩

theorem each_new_receipt_has_its_own_checked_origin
 (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (index : Nat) (row : StageTrace.Record (code := bound.source.code))
 (previous : HeaderReception.Receiver (code := bound.source.code))
 (receipt : HeaderReception.Receipt (code := bound.source.code))
 (inside : receipt ∈ (receive bound base law origin receiver index row previous).receipts) :
 receipt ∈ previous.receipts ∨
 (receipt.index=index ∧ receipt.delivery=row.cursor.cut ∧
  ∃ seen, HeaderReception.check (origin.vocabulary bound base) (origin.law bound law)
   origin.origin origin.stages receiver row seen receipt.wire=.accepted receipt.wire) := by
 unfold receive at inside
 dsimp only at inside
 split at inside
 · rename_i wire accepted
   rcases List.mem_append.mp inside with old | new
   · exact Or.inl old
   · cases List.mem_singleton.mp new
     cases found : incoming bound base origin row with
     | none => simp only [found] at accepted; contradiction
     | some candidate =>
       simp only [found] at accepted
       obtain ⟨rfl,_⟩ := HeaderReception.check_sound _ _ _ _ _ _ _ _ _ accepted
       exact Or.inr ⟨rfl,rfl,_,accepted⟩
 · exact Or.inl inside

theorem received_ballots_keep_the_original_issuing_ledger
 (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (rows : List (StageTrace.Record (code := bound.source.code))) (offset : Nat)
 (previous : HeaderReception.Receiver (code := bound.source.code))
 (prior : ∀ receipt ∈ previous.receipts,
  receipt.wire.ballot ∈ StageBudget.ledger (origin.vocabulary bound base) origin.origin origin.stages) :
 ∀ receipt ∈ (scan bound base law origin receiver rows offset previous).receipts,
 receipt.wire.ballot ∈ StageBudget.ledger (origin.vocabulary bound base) origin.origin origin.stages := by
 induction rows generalizing offset previous with
 | nil => exact prior
 | cons row tail ih =>
   apply ih (offset+1) (receive bound base law origin receiver offset row previous)
   intro receipt member
   rcases each_new_receipt_has_its_own_checked_origin bound base law origin receiver offset row previous receipt member with old | fresh
   · exact prior receipt old
   · obtain ⟨_,_,seen,accepted⟩ := fresh
     have authentic := (HeaderReception.check_sound _ _ _ _ _ _ _ _ _ accepted).2.2.2.1
     obtain ⟨_,_,_,_,_,_,_,paid,_⟩ := HeaderTransport.authenticated_wire_has_actual_send_and_paid_ballot
      (origin.vocabulary bound base) origin.origin origin.stages receipt.wire authentic
     exact paid

theorem receipt_has_its_own_original_paid_ballot
 (genesis : Cursor bound.source.code) (state : State bound genesis) (origin : Segment bound)
 (receiver : Fin bound.source.code.sites) (receipt : HeaderReception.Receipt (code := bound.source.code))
 (inside : receipt ∈ (observed bound base law genesis state origin receiver).receipts) :
 receipt.wire.ballot ∈ StageBudget.ledger (origin.vocabulary bound base) origin.origin origin.stages :=
 received_ballots_keep_the_original_issuing_ledger bound base law origin receiver _ _ _ (by simp) receipt inside

private theorem scan_receipt_property
 (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (rows : List (StageTrace.Record (code := bound.source.code))) (offset : Nat)
 (previous : HeaderReception.Receiver (code := bound.source.code))
 (property : HeaderReception.Receipt (code := bound.source.code) → Prop)
 (old : ∀ receipt ∈ previous.receipts, property receipt)
 (new : ∀ index row, row ∈ rows → ∀ seen wire,
  HeaderReception.check (origin.vocabulary bound base) (origin.law bound law)
   origin.origin origin.stages receiver row seen wire=.accepted wire →
  property ⟨wire,index,row.cursor.cut⟩) :
 ∀ receipt ∈ (scan bound base law origin receiver rows offset previous).receipts, property receipt := by
 induction rows generalizing offset previous with
 | nil => exact old
 | cons row tail ih =>
   apply ih (offset+1) (receive bound base law origin receiver offset row previous)
   · intro receipt member
     rcases each_new_receipt_has_its_own_checked_origin bound base law origin receiver offset row previous receipt member with prior | fresh
     · exact old receipt prior
     · rcases receipt with ⟨wire,index,delivery⟩
       obtain ⟨rfl,rfl,seen,accepted⟩ := fresh
       exact new index row (List.mem_cons_self) seen wire accepted
   · intro index later member seen wire accepted
     exact new index later (List.mem_cons_of_mem _ member) seen wire accepted

theorem every_receipt_has_an_actual_paid_delivery_in_the_cumulative_history
 (genesis : Cursor bound.source.code) (state : State bound genesis) (origin : Segment bound)
 (receiver : Fin bound.source.code.sites) (receipt : HeaderReception.Receipt (code := bound.source.code))
 (inside : receipt ∈ (observed bound base law genesis state origin receiver).receipts) :
 ∃ row ∈ state.rows bound genesis, receipt.delivery=row.cursor.cut ∧
  HeaderReception.delivered row receipt.wire.serial=true ∧
  HeaderReception.matchingPacket row receipt.wire=true ∧
  row.cursor.cut ≤ receipt.wire.sendCut+law.maxDelay ∧
  (∀ item ∈ StageTrace.items row, bound.source.code.law.Valid item.before item.request) := by
 apply scan_receipt_property bound base law origin receiver _ _ _ _ (by simp) ?_ receipt inside
 intro index row member seen wire accepted
 have checked := HeaderReception.check_sound _ _ _ _ _ _ _ _ _ accepted
 exact ⟨row,member,rfl,checked.2.1,checked.2.2.2.2.1,checked.2.2.2.2.2.2.2.1,checked.2.2.2.2.2.2.2.2.1⟩

theorem scan_preserves_all_prior_receipts
 (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (rows : List (StageTrace.Record (code := bound.source.code))) (offset : Nat)
 (previous : HeaderReception.Receiver (code := bound.source.code)) :
 previous.receipts <+: (scan bound base law origin receiver rows offset previous).receipts := by
 induction rows generalizing offset previous with
 | nil => exact List.prefix_refl _
 | cons row tail ih =>
   apply List.IsPrefix.trans (l₂ := (receive bound base law origin receiver offset row previous).receipts)
   · unfold receive
     dsimp only
     split
     · exact List.prefix_append _ _
     · exact List.prefix_refl _
   · exact ih _ _

theorem scan_append
 (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (past more : List (StageTrace.Record (code := bound.source.code))) (offset : Nat)
 (previous : HeaderReception.Receiver (code := bound.source.code)) :
 scan bound base law origin receiver (past++more) offset previous =
 scan bound base law origin receiver more (offset+past.length)
  (scan bound base law origin receiver past offset previous) := by
 induction past generalizing offset previous with
 | nil => rfl
 | cons row tail ih =>
   change scan bound base law origin receiver (tail++more) (offset+1) _ = _
   rw [ih]
   congr 1
   simp only [List.length_cons]
   omega

theorem actual_later_rounds_preserve_all_old_receipts
 (genesis : Cursor bound.source.code) (state : State bound genesis)
 (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (inputs : List LocalCommandSource.Input) :
 (observed bound base law genesis state origin receiver).receipts <+:
 (observed bound base law genesis (next bound genesis state inputs) origin receiver).receipts := by
 unfold observed
 change _ <+: (scan bound base law origin receiver (StageTrace.records genesis (state.stages++_)) 0 _).receipts
 rw [StageQueue.records_append,scan_append]
 exact scan_preserves_all_prior_receipts bound base law origin receiver _ _ _

def produce (genesis : Cursor bound.source.code) (state : State bound genesis)
 (index : Nat) (receiver : Fin bound.source.code.sites) (scope : Scope) (threshold : Nat) : ProspectiveQuorum.Result :=
 match state.archive[index]? with
 | none => .blocked .missingQuorum
 | some origin =>
   if ¬ (ActorEnvelope.roster origin.origin.source).card+
     ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope < threshold+threshold then
    .blocked .unsafeSourceBudget
   else match ActorQuorum.readout (observed bound base law genesis state origin receiver) scope threshold with
    | .blocked => .blocked .missingQuorum
    | .decided value => .decided value

theorem a_cumulative_supporter_has_its_original_paid_ballot
 (genesis : Cursor bound.source.code) (state : State bound genesis) (origin : Segment bound)
 (receiver : Fin bound.source.code.sites) (scope : Scope) (value : Bool) (actor : Party)
 (inside : actor ∈ ActorQuorum.support (observed bound base law genesis state origin receiver) scope value) :
 ∃ receipt ∈ (observed bound base law genesis state origin receiver).receipts,
  receipt.wire.ballot ∈ StageBudget.ledger (origin.vocabulary bound base) origin.origin origin.stages ∧
  receipt.wire.ballot.actor=actor ∧ receipt.wire.ballot.scope=scope ∧ receipt.wire.ballot.choice=value := by
 obtain ⟨key,member,owner⟩ := (ActorQuorum.mem_support_iff _ scope value actor).mp inside
 obtain ⟨receipt,present,sameScope,choice,sameKey⟩ := (StageQuorum.mem_support_iff _ scope value key).mp member
 have paid := receipt_has_its_own_original_paid_ballot bound base law genesis state origin receiver receipt present
 have actual := ActorEnvelope.actual_ballot_retains_the_original_actor (origin.vocabulary bound base)
  origin.origin origin.stages _ paid
 exact ⟨receipt,present,paid,by rw [actual,sameKey,owner],sameScope,choice⟩

theorem conflicting_cumulative_support_spends_the_original_affected_identity
 (genesis : Cursor bound.source.code) (state : State bound genesis) (origin : Segment bound)
 (left right : Fin bound.source.code.sites) (scope : Scope) (a b : Bool) (different : a≠b) :
 ActorQuorum.support (observed bound base law genesis state origin left) scope a ∩
  ActorQuorum.support (observed bound base law genesis state origin right) scope b ⊆
 ActorStageEnvelope.affected origin.origin (origin.vocabulary bound base) origin.stages scope := by
 intro actor member
 obtain ⟨one,_,first,actorOne,scopeOne,valueOne⟩ := a_cumulative_supporter_has_its_original_paid_ballot
  bound base law genesis state origin left scope a actor (Finset.mem_inter.mp member).1
 obtain ⟨two,_,second,actorTwo,scopeTwo,valueTwo⟩ := a_cumulative_supporter_has_its_original_paid_ballot
  bound base law genesis state origin right scope b actor (Finset.mem_inter.mp member).2
 have charged := ActorStageEnvelope.conflicting_actual_aliases_or_cuts_spend_one_affected_identity
  origin.origin (origin.vocabulary bound base) origin.stages scope one.wire.ballot two.wire.ballot first second
  (actorOne.trans actorTwo.symm) scopeOne scopeTwo
  (by intro same;exact different (valueOne.symm.trans (same.trans valueTwo)))
 simpa only [actorOne] using charged

theorem a_produced_decision_has_its_actual_archived_source_and_quorum
 (genesis : Cursor bound.source.code) (state : State bound genesis) (index : Nat)
 (receiver : Fin bound.source.code.sites) (scope : Scope) (threshold : Nat) (value : Bool)
 (done : produce bound base law genesis state index receiver scope threshold=.decided value) :
 ∃ origin, state.archive[index]?=some origin ∧
  (ActorEnvelope.roster origin.origin.source).card+
   ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope < threshold+threshold ∧
  ActorQuorum.readout (observed bound base law genesis state origin receiver) scope threshold=.decided value := by
 unfold produce at done
 split at done <;> try contradiction
 rename_i origin found
 split at done <;> try contradiction
 rename_i safe
 split at done <;> try contradiction
 rename_i answer readout
 cases done
 exact ⟨origin,found,of_not_not safe,readout⟩

theorem produced_decisions_agree_across_receivers_after_arbitrary_rounds
 (genesis : Cursor bound.source.code) (state : State bound genesis) (index : Nat)
 (left right : Fin bound.source.code.sites) (scope : Scope) (threshold : Nat) (a b : Bool)
 (one : produce bound base law genesis state index left scope threshold=.decided a)
 (two : produce bound base law genesis state index right scope threshold=.decided b) : a=b := by
 obtain ⟨origin,found,safe,first⟩ := a_produced_decision_has_its_actual_archived_source_and_quorum bound base law genesis state index left scope threshold a one
 obtain ⟨other,again,_,second⟩ := a_produced_decision_has_its_actual_archived_source_and_quorum bound base law genesis state index right scope threshold b two
 have same : other=origin := Option.some.inj (again.symm.trans found)
 subst other
 by_contra different
 have firstCount := (ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ first).2
 have secondCount := (ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ second).2
 have overlap := Finset.card_le_card (conflicting_cumulative_support_spends_the_original_affected_identity
  bound base law genesis state origin left right scope a b different)
 have roster (receiver : Fin bound.source.code.sites) (value : Bool) :
  ActorQuorum.support (observed bound base law genesis state origin receiver) scope value ⊆ ActorEnvelope.roster origin.origin.source := by
   intro actor member
   obtain ⟨key,_,owner⟩ := (ActorQuorum.mem_support_iff _ scope value actor).mp member
   exact Finset.mem_image.mpr ⟨key,Finset.mem_univ _,owner⟩
 have union := Finset.card_le_card (Finset.union_subset (roster left a) (roster right b))
 have count := Finset.card_union_add_card_inter
  (ActorQuorum.support (observed bound base law genesis state origin left) scope a)
  (ActorQuorum.support (observed bound base law genesis state origin right) scope b)
 unfold ActorStageEnvelope.budget at safe
 omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecursiveSigningReception
