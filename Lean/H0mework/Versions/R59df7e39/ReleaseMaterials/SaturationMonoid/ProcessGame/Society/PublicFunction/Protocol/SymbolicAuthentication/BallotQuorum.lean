import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeviationBudget
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Quorum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BallotQuorum

open Distributed Reaction Reaction.Feedback

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)

def support (observed : AttestationReception.Receiver source) (scope : Scope) (value : Bool) : Finset (Fin source.code.sites) :=
  ((observed.receipts.filter fun receipt => decide
    (receipt.wire.ballot.scope = scope ∧ receipt.wire.ballot.choice = value)).map
      fun receipt => receipt.wire.ballot.key).toFinset

theorem mem_support_iff (observed : AttestationReception.Receiver source) (scope : Scope) (value : Bool)
    (key : Fin source.code.sites) : key ∈ support source observed scope value ↔
    ∃ receipt ∈ observed.receipts,
      receipt.wire.ballot.scope = scope ∧ receipt.wire.ballot.choice = value ∧ receipt.wire.ballot.key = key := by
  simp only [support, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨receipt, ⟨inside, scope, value⟩, key⟩
    exact ⟨receipt, inside, scope, value, key⟩
  · rintro ⟨receipt, inside, scope, value, key⟩
    exact ⟨receipt, ⟨inside, scope, value⟩, key⟩

def readout (observed : AttestationReception.Receiver source) (scope : Scope) (threshold : Nat) : Quorum.ReadoutData Bool :=
  if threshold = 0 then .blocked else
  match [false, true].find? (fun value => decide (threshold ≤ (support source observed scope value).card)) with
  | none => .blocked
  | some value => .decided value

theorem decided_has_positive_quorum (observed : AttestationReception.Receiver source)
    (scope : Scope) (threshold : Nat) (value : Bool)
    (decided : readout source observed scope threshold = .decided value) :
    0 < threshold ∧ threshold ≤ (support source observed scope value).card := by
  unfold readout at decided
  split at decided <;> try contradiction
  rename_i positive
  split at decided <;> try contradiction
  rename_i found actual
  have same := Quorum.ReadoutData.decided.inj decided
  subst found
  exact ⟨Nat.pos_of_ne_zero positive, of_decide_eq_true (List.find?_some (p := fun (v : Bool) => decide (threshold ≤ (support source observed scope v).card)) actual)⟩

variable (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : AttestationTransport.Encoding source) (law : AttestationReception.ReceptionLaw source)

abbrev observed (receiver : Fin source.code.sites) (count : Nat) :=
  AttestationReception.run source input cut protocol rival vocabulary encoding law receiver count

theorem receipt_ballot_has_actual_origin (receiver : Fin source.code.sites) (count : Nat)
    (receipt : AttestationReception.Receipt source)
    (inside : receipt ∈ (observed source input cut protocol rival vocabulary encoding law receiver count).receipts) :
    OwnedAttestation.verify source input cut protocol rival vocabulary receipt.wire.ballot = true ∧
      receipt.wire.ballot.cut < count := by
  obtain ⟨authenticated, _, _, _, sentBefore, deliveredBefore, _⟩ :=
    AttestationReception.receipts_have_actual_communication source input cut protocol rival vocabulary encoding law receiver count receipt inside
  obtain ⟨_, _, owned, originBefore, _⟩ := AttestationTransport.authenticated_wire_has_an_earlier_owned_paid_statement
    source input cut protocol rival vocabulary encoding receipt.wire authenticated
  exact ⟨owned, by omega⟩

theorem decided_has_source_authenticated_support
    (receiver : Fin source.code.sites) (count : Nat) (scope : Scope) (threshold : Nat) (value : Bool)
    (decided : readout source (observed source input cut protocol rival vocabulary encoding law receiver count) scope threshold = .decided value) :
    ∃ receipt ∈ (observed source input cut protocol rival vocabulary encoding law receiver count).receipts,
      receipt.wire.ballot.scope = scope ∧ receipt.wire.ballot.choice = value ∧
      OwnedAttestation.verify source input cut protocol rival vocabulary receipt.wire.ballot = true ∧
      receipt.wire.ballot.cut < count := by
  obtain ⟨positive, enough⟩ := decided_has_positive_quorum source _ scope threshold value decided
  obtain ⟨key, inside⟩ := Finset.card_pos.mp (lt_of_lt_of_le positive enough)
  obtain ⟨receipt, present, scope, value, _⟩ := (mem_support_iff source _ scope value key).mp inside
  exact ⟨receipt, present, scope, value,
    receipt_ballot_has_actual_origin source input cut protocol rival vocabulary encoding law receiver count receipt present⟩

theorem conflicting_intersection_is_in_source_budget
    (left right : Fin source.code.sites) (leftCount rightCount horizon : Nat)
    (leftBound : leftCount ≤ horizon) (rightBound : rightCount ≤ horizon)
    (scope : Scope) (a b : Bool) (different : a ≠ b) :
    support source (observed source input cut protocol rival vocabulary encoding law left leftCount) scope a ∩
        support source (observed source input cut protocol rival vocabulary encoding law right rightCount) scope b ⊆
      DeviationBudget.affectedThrough source input cut protocol rival vocabulary horizon := by
  intro key inside
  obtain ⟨one, first, scope₁, value₁, key₁⟩ := (mem_support_iff source _ scope a key).mp (Finset.mem_inter.mp inside).1
  obtain ⟨two, second, scope₂, value₂, key₂⟩ := (mem_support_iff source _ scope b key).mp (Finset.mem_inter.mp inside).2
  obtain ⟨origin₁, bounded₁⟩ := receipt_ballot_has_actual_origin source input cut protocol rival vocabulary encoding law left leftCount one first
  obtain ⟨origin₂, bounded₂⟩ := receipt_ballot_has_actual_origin source input cut protocol rival vocabulary encoding law right rightCount two second
  rw [← key₁]
  apply DeviationBudget.authenticated_equivocation_is_covered source input cut protocol rival vocabulary horizon
    one.wire.ballot two.wire.ballot origin₁ origin₂ (by omega) (by omega)
    (key₁.trans key₂.symm) (scope₁.trans scope₂.symm)
  intro same
  exact different (value₁.symm.trans (same.trans value₂))

/-- Agreement consumes a budget from the actual selected
work words, independently of the two receiver certificate/readout histories. -/
theorem agreement_of_actual_source_budget
    (left right : Fin source.code.sites) (leftCount rightCount horizon : Nat)
    (leftBound : leftCount ≤ horizon) (rightBound : rightCount ≤ horizon)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : readout source (observed source input cut protocol rival vocabulary encoding law left leftCount) scope threshold = .decided a)
    (two : readout source (observed source input cut protocol rival vocabulary encoding law right rightCount) scope threshold = .decided b)
    (budget : source.code.sites + DeviationBudget.budget source input cut protocol rival vocabulary horizon < threshold + threshold) : a = b := by
  by_contra different
  have first := (decided_has_positive_quorum source _ scope threshold a one).2
  have second := (decided_has_positive_quorum source _ scope threshold b two).2
  have exposed := Finset.card_le_card (conflicting_intersection_is_in_source_budget source input cut protocol rival vocabulary encoding law
    left right leftCount rightCount horizon leftBound rightBound scope a b different)
  have unionBound : (support source (observed source input cut protocol rival vocabulary encoding law left leftCount) scope a ∪
      support source (observed source input cut protocol rival vocabulary encoding law right rightCount) scope b).card ≤ source.code.sites := by
    simpa only [Fintype.card_fin] using
      (support source (observed source input cut protocol rival vocabulary encoding law left leftCount) scope a ∪
        support source (observed source input cut protocol rival vocabulary encoding law right rightCount) scope b).card_le_univ
  have count := Finset.card_union_add_card_inter
    (support source (observed source input cut protocol rival vocabulary encoding law left leftCount) scope a)
    (support source (observed source input cut protocol rival vocabulary encoding law right rightCount) scope b)
  unfold DeviationBudget.budget at budget
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BallotQuorum
