import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueue

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueueProgress

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem issued_coordinates (row : StageTrace.Record (code := code)) (position : Nat)
    (body : StageBudget.Ballot (code := code)) (made : StageBudget.issued vocabulary row position = some body) :
    body.cut = row.cursor.cut ∧ body.position = position := by
  obtain ⟨_, _, _, _, _, _, _, _, _, cut, index, _⟩ := StageBudget.issued_has_an_owned_valid_paid_origin vocabulary row position body made
  exact ⟨cut, index⟩

theorem issued_cut_is_not_before_its_actual_history
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (body : StageBudget.Ballot (code := code)) (inside : body ∈ StageBudget.ledger vocabulary cursor stages) : cursor.cut ≤ body.cut := by
  obtain ⟨row, included, position, made⟩ := StageBudget.ledger_origin vocabulary cursor stages body inside
  have cut := (issued_coordinates vocabulary row position body made).1
  have member : row.cursor.cut ∈ (StageTrace.records cursor stages).map (fun row => row.cursor.cut) :=
    List.mem_map.mpr ⟨row, included, rfl⟩
  rw [StageTrace.no_occurrence_is_lost_or_duplicated] at member
  obtain ⟨_, _, same⟩ := List.mem_map.mp member
  omega

theorem one_owned_origin_has_one_actual_body
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (first second : StageBudget.Ballot (code := code))
    (one : first ∈ StageBudget.ledger vocabulary cursor stages)
    (two : second ∈ StageBudget.ledger vocabulary cursor stages)
    (same : (first.cut, first.position) = (second.cut, second.position)) : first = second := by
  induction stages generalizing cursor with
  | nil => simp [StageBudget.ledger, StageTrace.records] at one
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    change first ∈ StageTransport.ballots vocabulary (StageTrace.material cursor protocol rival) ++
      StageBudget.ledger vocabulary (cursor.after protocol rival) tail at one
    change second ∈ StageTransport.ballots vocabulary (StageTrace.material cursor protocol rival) ++
      StageBudget.ledger vocabulary (cursor.after protocol rival) tail at two
    rcases List.mem_append.mp one with now | later
    · obtain ⟨a, _, made⟩ := List.mem_filterMap.mp now
      have coords := issued_coordinates vocabulary _ a first made
      rcases List.mem_append.mp two with other | remaining
      · obtain ⟨b, _, produced⟩ := List.mem_filterMap.mp other
        have secondCoords := issued_coordinates vocabulary _ b second produced
        have index : a = b := by have equal := (Prod.mk.inj same).2; omega
        rw [index, produced] at made
        exact Option.some.inj made.symm
      · have lower := issued_cut_is_not_before_its_actual_history vocabulary (cursor.after protocol rival) tail second remaining
        have equal := (Prod.mk.inj same).1
        change cursor.cut + 1 ≤ second.cut at lower
        have cut : first.cut = cursor.cut := coords.1
        omega
    · rcases List.mem_append.mp two with now | laterSecond
      · obtain ⟨b, _, made⟩ := List.mem_filterMap.mp now
        have coords := (issued_coordinates vocabulary _ b second made).1
        have lower := issued_cut_is_not_before_its_actual_history vocabulary (cursor.after protocol rival) tail first later
        have equal := (Prod.mk.inj same).1
        change cursor.cut + 1 ≤ first.cut at lower
        change second.cut = cursor.cut at coords
        omega
      · exact ih (cursor.after protocol rival) later laterSecond

variable (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))

/-- Inspect actual transport, payment, scope and timing without consulting any receipt list. -/
def readyAt (receiver : Fin code.sites) (index : Nat) : Option (StageTransport.Wire (code := code)) :=
  match (StageTrace.records cursor stages)[index]?, StageReception.incoming vocabulary encoding cursor stages index with
  | some row, some wire =>
    if StageReception.check vocabulary encoding law cursor stages receiver row [] wire = .accepted wire then some wire else none
  | _, _ => none

theorem receipts_are_preserved (receiver : Fin code.sites) (first last : Nat) (later : first ≤ last) :
    (StageReception.run vocabulary encoding law cursor stages receiver first).receipts <+:
      (StageReception.run vocabulary encoding law cursor stages receiver last).receipts := by
  induction last, later using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ last _ ih =>
    apply ih.trans
    simp only [StageReception.run, StageReception.receive]
    split
    · exact List.prefix_refl _
    · split
      · exact List.prefix_append _ _
      · exact List.prefix_refl _

theorem source_ready_delivery_generates_or_preserves_its_actual_content_receipt
    (receiver : Fin code.sites) (index : Nat) (wire : StageTransport.Wire (code := code))
    (ready : readyAt vocabulary encoding law cursor stages receiver index = some wire) :
    ∃ receipt ∈ (StageReception.run vocabulary encoding law cursor stages receiver (index + 1)).receipts,
      receipt.wire.ballot = wire.ballot := by
  unfold readyAt at ready
  split at ready <;> try contradiction
  rename_i row body actual incoming
  split at ready <;> try contradiction
  rename_i accepts
  cases Option.some.inj ready
  have facts := StageReception.check_sound vocabulary encoding law cursor stages receiver row [] wire wire accepts
  obtain ⟨_, _, _, _, _, _, _, owned, _⟩ :=
    StageTransport.authenticated_wire_has_actual_send_and_paid_ballot vocabulary encoding cursor stages wire facts.2.2.2.1
  by_cases duplicate : (wire.ballot.cut, wire.ballot.position) ∈
      (StageReception.run vocabulary encoding law cursor stages receiver index).receipts.map
        (fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position))
  · obtain ⟨old, inside, same⟩ := List.mem_map.mp duplicate
    have oldOwned := StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law cursor stages receiver index old inside
    exact ⟨old, (receipts_are_preserved vocabulary encoding law cursor stages receiver index (index + 1) (by omega)).subset inside,
      one_owned_origin_has_one_actual_body vocabulary cursor stages old.wire.ballot wire.ballot oldOwned owned same⟩
  · have acceptsSeen : StageReception.check vocabulary encoding law cursor stages receiver row
        ((StageReception.run vocabulary encoding law cursor stages receiver index).receipts.map
          fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position)) wire = .accepted wire := by
      obtain ⟨_, delivery, earlier, auth, packet, who, currentScope, time, paid, _⟩ := facts
      simp [StageReception.check, delivery, earlier, auth, packet, who, currentScope, time, duplicate]
      exact paid
    refine ⟨⟨wire, index, row.cursor.cut⟩, ?_, rfl⟩
    simp only [StageReception.run, StageReception.receive, actual, incoming, acceptsSeen]
    exact List.mem_append_right _ (List.mem_singleton_self _)

def supportingAt (receiver : Fin code.sites) (scope : Scope) (value : Bool) (index : Nat) : Option (Fin code.sites) :=
  match readyAt vocabulary encoding law cursor stages receiver index with
  | none => none
  | some wire => if wire.ballot.scope = scope ∧ wire.ballot.choice = value then some wire.ballot.key else none

def readySupport (receiver : Fin code.sites) (scope : Scope) (value : Bool) : Finset (Fin code.sites) :=
  ((List.range stages.length).filterMap (supportingAt vocabulary encoding law cursor stages receiver scope value)).toFinset

theorem generated_support_is_in_the_actual_receiver (receiver : Fin code.sites) (scope : Scope) (value : Bool) :
    readySupport vocabulary encoding law cursor stages receiver scope value ⊆
      StageQuorum.support (StageReception.run vocabulary encoding law cursor stages receiver stages.length) scope value := by
  intro key inside
  obtain ⟨index, bounded, supported⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp inside)
  unfold supportingAt at supported
  split at supported <;> try contradiction
  rename_i wire ready
  split at supported <;> try contradiction
  rename_i aligned
  have sameKey := Option.some.inj supported
  obtain ⟨receipt, actual, same⟩ := source_ready_delivery_generates_or_preserves_its_actual_content_receipt
    vocabulary encoding law cursor stages receiver index wire ready
  have received := (receipts_are_preserved vocabulary encoding law cursor stages receiver (index + 1) stages.length
    (by have before := List.mem_range.mp bounded; omega)).subset actual
  exact (StageQuorum.mem_support_iff _ scope value key).mpr ⟨receipt, received,
    (congrArg OwnedAttestation.BallotData.scope same).trans aligned.1,
    (congrArg OwnedAttestation.BallotData.choice same).trans aligned.2,
    (congrArg OwnedAttestation.BallotData.key same).trans sameKey⟩

inductive Obstruction where
  | zeroThreshold | unsafeBudget | insufficientReadySupport | insufficientCuts
  deriving DecidableEq
inductive Plan where
  | blocked (reason : Obstruction)
  | ready (value : Bool)
  deriving DecidableEq

variable (base : Code Party Good Port (Mandate.State Party Technology) Instrument)

def plan (encoding : StageTransport.Encoding (code := AdmissionCode.lift base))
    (law : StageReception.Law (AdmissionCode.lift base)) (cursor : Cursor (AdmissionCode.lift base))
    (stages : List (EventHistory.Stage (code := AdmissionCode.lift base)))
    (receiver : Fin base.sites) (scope : Scope) (threshold : Nat) : Plan :=
  if threshold = 0 then .blocked .zeroThreshold
  else if ¬ base.sites + AdmissionCode.budget base < threshold + threshold then .blocked .unsafeBudget
  else match [false, true].find? (fun value => decide (threshold ≤ (readySupport vocabulary encoding law cursor stages receiver scope value).card)) with
    | none => .blocked .insufficientReadySupport
    | some value => .ready value

theorem source_ready_support_generates_an_online_decision
    (encoding : StageTransport.Encoding (code := AdmissionCode.lift base))
    (law : StageReception.Law (AdmissionCode.lift base)) (cursor : Cursor (AdmissionCode.lift base))
    (stages : List (EventHistory.Stage (code := AdmissionCode.lift base)))
    (receiver : Fin base.sites) (scope : Scope) (threshold : Nat) (value : Bool)
    (ready : plan vocabulary base encoding law cursor stages receiver scope threshold = .ready value) :
    AdmissionQuorum.produce base vocabulary encoding law cursor stages receiver scope threshold = .decided value := by
  unfold plan at ready
  split at ready <;> try contradiction
  rename_i positive
  split at ready <;> try contradiction
  rename_i safe
  split at ready <;> try contradiction
  rename_i choice found
  cases Plan.ready.inj ready
  have enough := of_decide_eq_true (List.find?_some
    (p := fun value => decide (threshold ≤ (readySupport vocabulary encoding law cursor stages receiver scope value).card)) found)
  have actual := le_trans enough (Finset.card_le_card (generated_support_is_in_the_actual_receiver vocabulary encoding law cursor stages receiver scope value))
  have budget : base.sites + AdmissionCode.budget base < threshold + threshold := by simpa using safe
  have existsDecision : ∃ choice, StageQuorum.readout
      (StageReception.run vocabulary encoding law cursor stages receiver stages.length) scope threshold = .decided choice := by
    unfold StageQuorum.readout
    rw [if_neg positive]
    cases chosen : [false, true].find? (fun choice => decide (threshold ≤ (StageQuorum.support
        (StageReception.run vocabulary encoding law cursor stages receiver stages.length) scope choice).card)) with
    | some choice => exact ⟨choice, rfl⟩
    | none =>
      have absent := List.find?_eq_none.mp chosen value (by cases value <;> simp)
      exact False.elim (absent (decide_eq_true actual))
  obtain ⟨choice, decided⟩ := existsDecision
  have same : choice = value := by
    by_contra different
    have first := (StageQuorum.decided_has_positive_quorum _ scope threshold choice decided).2
    have exposed := Finset.card_le_card (AdmissionQuorum.conflicting_support_across_actual_prefixes_exposes_an_admitted_key
      base vocabulary encoding law cursor stages [] receiver receiver scope choice value different)
    simp only [List.append_nil] at exposed
    have union : (StageQuorum.support (StageReception.run vocabulary encoding law cursor stages receiver stages.length) scope choice ∪
        StageQuorum.support (StageReception.run vocabulary encoding law cursor stages receiver stages.length) scope value).card ≤ base.sites := by
      simpa only [Fintype.card_fin] using
        (StageQuorum.support (StageReception.run vocabulary encoding law cursor stages receiver stages.length) scope choice ∪
          StageQuorum.support (StageReception.run vocabulary encoding law cursor stages receiver stages.length) scope value).card_le_univ
    have counted := Finset.card_union_add_card_inter
      (StageQuorum.support (StageReception.run vocabulary encoding law cursor stages receiver stages.length) scope choice)
      (StageQuorum.support (StageReception.run vocabulary encoding law cursor stages receiver stages.length) scope value)
    dsimp only [AdmissionCode.budget] at budget
    omega
  unfold AdmissionQuorum.produce
  rw [if_pos budget, ← same]
  exact decided

def completeStages (cursor : Cursor code) (pastStages : List (EventHistory.Stage (code := code)))
    (protocols : Nat → Rule code) : List (EventHistory.Stage (code := code)) :=
  let current := EventHistory.execute cursor pastStages
  pastStages ++ StageQueue.stages current protocols (StageQueue.horizon current)

def windowPlan (encoding : StageTransport.Encoding (code := AdmissionCode.lift base))
    (law : StageReception.Law (AdmissionCode.lift base)) (cursor : Cursor (AdmissionCode.lift base))
    (pastStages : List (EventHistory.Stage (code := AdmissionCode.lift base))) (protocols : Nat → Rule (AdmissionCode.lift base))
    (receiver : Fin base.sites) (scope : Scope) (threshold : Nat) : Plan :=
  let current := EventHistory.execute cursor pastStages
  if StageQueue.horizon current ≤ (EventStep.seed current).remaining then
    plan vocabulary base encoding law cursor (completeStages cursor pastStages protocols) receiver scope threshold
  else .blocked .insufficientCuts

theorem a_generated_ready_window_completes_the_online_quorum
    (encoding : StageTransport.Encoding (code := AdmissionCode.lift base))
    (law : StageReception.Law (AdmissionCode.lift base)) (cursor : Cursor (AdmissionCode.lift base))
    (pastStages : List (EventHistory.Stage (code := AdmissionCode.lift base))) (protocols : Nat → Rule (AdmissionCode.lift base))
    (receiver : Fin base.sites) (scope : Scope) (threshold : Nat) (value : Bool)
    (ready : windowPlan vocabulary base encoding law cursor pastStages protocols receiver scope threshold = .ready value) :
    AdmissionQuorum.produce base vocabulary encoding law cursor (completeStages cursor pastStages protocols) receiver scope threshold = .decided value := by
  unfold windowPlan at ready
  dsimp only at ready
  split at ready <;> try contradiction
  exact source_ready_support_generates_an_online_decision vocabulary base encoding law cursor _ receiver scope threshold value ready

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueueProgress
