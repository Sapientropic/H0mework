import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageReception

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQuorum

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def support (observed : StageReception.Receiver (code := code)) (scope : Scope) (value : Bool) : Finset (Fin code.sites) :=
  ((observed.receipts.filter fun receipt => decide
    (receipt.wire.ballot.scope = scope ∧ receipt.wire.ballot.choice = value)).map
      fun receipt => receipt.wire.ballot.key).toFinset

omit [DecidableEq Port] [DecidableEq Technology] in
theorem mem_support_iff (observed : StageReception.Receiver (code := code)) (scope : Scope) (value : Bool)
    (key : Fin code.sites) : key ∈ support observed scope value ↔
    ∃ receipt ∈ observed.receipts,
      receipt.wire.ballot.scope = scope ∧ receipt.wire.ballot.choice = value ∧ receipt.wire.ballot.key = key := by
  simp only [support, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨receipt, ⟨inside, sameScope, choice⟩, sameKey⟩
    exact ⟨receipt, inside, sameScope, choice, sameKey⟩
  · rintro ⟨receipt, inside, sameScope, choice, sameKey⟩
    exact ⟨receipt, ⟨inside, sameScope, choice⟩, sameKey⟩

def readout (observed : StageReception.Receiver (code := code)) (scope : Scope) (threshold : Nat) : Quorum.ReadoutData Bool :=
  if threshold = 0 then .blocked else
  match [false, true].find? (fun value => decide (threshold ≤ (support observed scope value).card)) with
  | none => .blocked
  | some value => .decided value

omit [DecidableEq Port] [DecidableEq Technology] in
theorem decided_has_positive_quorum (observed : StageReception.Receiver (code := code))
    (scope : Scope) (threshold : Nat) (value : Bool)
    (decided : readout observed scope threshold = .decided value) :
    0 < threshold ∧ threshold ≤ (support observed scope value).card := by
  unfold readout at decided
  split at decided <;> try contradiction
  rename_i positive
  split at decided <;> try contradiction
  rename_i found actual
  cases Quorum.ReadoutData.decided.inj decided
  exact ⟨Nat.pos_of_ne_zero positive, of_decide_eq_true
    (List.find?_some (p := fun value => decide (threshold ≤ (support observed scope value).card)) actual)⟩

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))

abbrev observed (receiver : Fin code.sites) (count : Nat) :=
  StageReception.run vocabulary encoding law cursor stages receiver count

theorem supporting_receipt_has_actual_owned_paid_origin
    (receiver : Fin code.sites) (count : Nat) (receipt : StageReception.Receipt (code := code))
    (inside : receipt ∈ (observed vocabulary encoding law cursor stages receiver count).receipts) :
    receipt.wire.ballot ∈ StageBudget.ledger vocabulary cursor stages := by
  obtain ⟨_, _, _, _, _, _, _, owned, _⟩ :=
    StageReception.receipt_has_actual_send_delivery_and_owned_ballot_origin vocabulary encoding law cursor stages receiver count receipt inside
  exact owned

theorem conflicting_received_support_is_in_the_actual_source_budget
    (left right : Fin code.sites) (leftCount rightCount : Nat) (scope : Scope)
    (a b : Bool) (different : a ≠ b) :
    support (observed vocabulary encoding law cursor stages left leftCount) scope a ∩
      support (observed vocabulary encoding law cursor stages right rightCount) scope b ⊆
        StageBudget.capacityKeys vocabulary cursor stages := by
  intro key inside
  obtain ⟨one, first, scope₁, value₁, key₁⟩ := (mem_support_iff _ scope a key).mp (Finset.mem_inter.mp inside).1
  obtain ⟨two, second, scope₂, value₂, key₂⟩ := (mem_support_iff _ scope b key).mp (Finset.mem_inter.mp inside).2
  have origin₁ := supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law cursor stages left leftCount one first
  have origin₂ := supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law cursor stages right rightCount two second
  rw [← key₁]
  apply StageBudget.every_actual_equivocation_is_covered_by_the_source_capacity_budget vocabulary cursor stages
    one.wire.ballot two.wire.ballot origin₁ origin₂ (key₁.trans key₂.symm) (scope₁.trans scope₂.symm)
  intro same
  exact different (value₁.symm.trans (same.trans value₂))

theorem actual_stage_delivery_quorums_agree
    (left right : Fin code.sites) (leftCount rightCount : Nat) (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : readout (observed vocabulary encoding law cursor stages left leftCount) scope threshold = .decided a)
    (two : readout (observed vocabulary encoding law cursor stages right rightCount) scope threshold = .decided b)
    (budget : code.sites + StageBudget.budget vocabulary cursor stages < threshold + threshold) : a = b := by
  by_contra different
  have first := (decided_has_positive_quorum _ scope threshold a one).2
  have second := (decided_has_positive_quorum _ scope threshold b two).2
  have exposed := Finset.card_le_card (conflicting_received_support_is_in_the_actual_source_budget
    vocabulary encoding law cursor stages left right leftCount rightCount scope a b different)
  have unionBound : (support (observed vocabulary encoding law cursor stages left leftCount) scope a ∪
      support (observed vocabulary encoding law cursor stages right rightCount) scope b).card ≤ code.sites := by
    simpa only [Fintype.card_fin] using
      (support (observed vocabulary encoding law cursor stages left leftCount) scope a ∪
        support (observed vocabulary encoding law cursor stages right rightCount) scope b).card_le_univ
  have count := Finset.card_union_add_card_inter
    (support (observed vocabulary encoding law cursor stages left leftCount) scope a)
    (support (observed vocabulary encoding law cursor stages right rightCount) scope b)
  unfold StageBudget.budget at budget
  omega

/-- The public producer computes its safety budget from the same actual history as its receipts. -/
def produce (receiver : Fin code.sites) (count : Nat) (scope : Scope) (threshold : Nat) : Quorum.ReadoutData Bool :=
  if code.sites + StageBudget.budget vocabulary cursor stages < threshold + threshold then
    readout (observed vocabulary encoding law cursor stages receiver count) scope threshold
  else .blocked

theorem produced_decision_has_actual_budget_and_received_quorum
    (receiver : Fin code.sites) (count : Nat) (scope : Scope) (threshold : Nat) (value : Bool)
    (decided : produce vocabulary encoding law cursor stages receiver count scope threshold = .decided value) :
    code.sites + StageBudget.budget vocabulary cursor stages < threshold + threshold ∧
      readout (observed vocabulary encoding law cursor stages receiver count) scope threshold = .decided value ∧
      0 < threshold ∧ threshold ≤ (support (observed vocabulary encoding law cursor stages receiver count) scope value).card := by
  unfold produce at decided
  split at decided <;> try contradiction
  rename_i budget
  exact ⟨budget, decided, decided_has_positive_quorum _ scope threshold value decided⟩

theorem produced_decisions_agree
    (left right : Fin code.sites) (leftCount rightCount : Nat) (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : produce vocabulary encoding law cursor stages left leftCount scope threshold = .decided a)
    (two : produce vocabulary encoding law cursor stages right rightCount scope threshold = .decided b) : a = b := by
  have first := produced_decision_has_actual_budget_and_received_quorum vocabulary encoding law cursor stages left leftCount scope threshold a one
  have second := produced_decision_has_actual_budget_and_received_quorum vocabulary encoding law cursor stages right rightCount scope threshold b two
  exact actual_stage_delivery_quorums_agree vocabulary encoding law cursor stages left right leftCount rightCount scope threshold a b
    first.2.1 second.2.1 first.1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQuorum
