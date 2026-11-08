import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProtocolCapabilityBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCapabilityAdmission
open Distributed Reaction Reaction.Feedback

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev choices (scope : Scope) (key : Fin source.code.sites) :=
  ProtocolCapabilityBudget.choices source source.reference vocabulary scope key
abbrev affected (scope : Scope) := ProtocolCapabilityBudget.affected source source.reference vocabulary scope
abbrev budget (scope : Scope) := ProtocolCapabilityBudget.budget source source.reference vocabulary scope

-- A candidate may change unlabelled work or drop choices. It cannot enlarge this source scope's admitted output capability.
def check (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code) (scope : Scope) : Bool :=
  (List.finRange source.code.sites).all fun key => decide
    (ProtocolCapabilityBudget.choices source protocol.work.val vocabulary scope key ⊆ choices source vocabulary scope key)

theorem original_source_work_is_admitted
    (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code) (scope : Scope)
    (original : protocol.work.val = source.reference) : check source vocabulary protocol scope = true := by
  apply List.all_eq_true.mpr
  intro key _
  simp only [original,Finset.Subset.refl,decide_true]

theorem an_admitted_choice_is_in_the_original_source
    (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code) (scope : Scope)
    (checked : check source vocabulary protocol scope = true) (key : Fin source.code.sites) (value : Bool)
    (member : value ∈ ProtocolCapabilityBudget.choices source protocol.work.val vocabulary scope key) :
    value ∈ choices source vocabulary scope key :=
  (of_decide_eq_true ((List.all_eq_true.mp checked) key (List.mem_finRange _))) member

theorem admitted_capacity_is_within_the_original_source_inventory
    (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code) (scope : Scope)
    (checked : check source vocabulary protocol scope = true) :
    ProtocolCapabilityBudget.affected source protocol.work.val vocabulary scope ⊆ affected source vocabulary scope := by
  intro key member
  obtain ⟨first,second⟩ := (ProtocolCapabilityBudget.mem_affected_iff source protocol.work.val vocabulary scope key).mp member
  exact (ProtocolCapabilityBudget.mem_affected_iff source source.reference vocabulary scope key).mpr
    ⟨an_admitted_choice_is_in_the_original_source source vocabulary protocol scope checked key false first,
      an_admitted_choice_is_in_the_original_source source vocabulary protocol scope checked key true second⟩

theorem every_admitted_actual_window_has_the_same_source_budget
    (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code) (scope : Scope)
    (checked : check source vocabulary protocol scope = true)
    (input : Input source.code) (cut : Nat) (rival : Opponent source.code) (horizon : Nat) :
    ScopeCapabilityBudget.budget source input cut protocol rival vocabulary scope horizon ≤ budget source vocabulary scope :=
  (ProtocolCapabilityBudget.actual_budget_never_exceeds_the_registered_budget source vocabulary protocol input cut rival scope horizon).trans
    (Finset.card_le_card (admitted_capacity_is_within_the_original_source_inventory source vocabulary protocol scope checked))

theorem verified_ballots_have_original_source_admission
    (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
    (input : Input source.code) (cut : Nat) (rival : Opponent source.code)
    (ballot : OwnedAttestation.Ballot source)
    (checked : check source vocabulary protocol ballot.scope = true)
    (verified : OwnedAttestation.verify source input cut protocol rival vocabulary ballot = true) :
    ballot.choice ∈ choices source vocabulary ballot.scope ballot.key :=
  an_admitted_choice_is_in_the_original_source source vocabulary protocol ballot.scope checked ballot.key ballot.choice
    (ProtocolCapabilityBudget.authenticated_choice_has_its_original_registered_work source vocabulary protocol input cut rival ballot verified)

variable (input : Input source.code) (cut : Nat)
  (encoding : AttestationTransport.Encoding source) (law : AttestationReception.ReceptionLaw source)

theorem conflicting_support_in_admitted_actual_branches_exposes_original_capacity
    (leftProtocol rightProtocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
    (leftRival rightRival : Opponent source.code) (left right : Fin source.code.sites) (leftCount rightCount : Nat)
    (scope : Scope) (a b : Bool) (different : a ≠ b)
    (leftAdmitted : check source vocabulary leftProtocol scope = true)
    (rightAdmitted : check source vocabulary rightProtocol scope = true) :
    BallotQuorum.support source (BallotQuorum.observed source input cut leftProtocol leftRival vocabulary encoding law left leftCount) scope a ∩
      BallotQuorum.support source (BallotQuorum.observed source input cut rightProtocol rightRival vocabulary encoding law right rightCount) scope b ⊆
        affected source vocabulary scope := by
  intro key member
  obtain ⟨one,present,scopeOne,valueOne,keyOne⟩ := (BallotQuorum.mem_support_iff source _ scope a key).mp (Finset.mem_inter.mp member).1
  obtain ⟨two,received,scopeTwo,valueTwo,keyTwo⟩ := (BallotQuorum.mem_support_iff source _ scope b key).mp (Finset.mem_inter.mp member).2
  have authOne := (BallotQuorum.receipt_ballot_has_actual_origin source input cut leftProtocol leftRival vocabulary encoding law left leftCount one present).1
  have authTwo := (BallotQuorum.receipt_ballot_has_actual_origin source input cut rightProtocol rightRival vocabulary encoding law right rightCount two received).1
  have first := verified_ballots_have_original_source_admission source vocabulary leftProtocol input cut leftRival one.wire.ballot
    (by simpa only [scopeOne] using leftAdmitted) authOne
  have second := verified_ballots_have_original_source_admission source vocabulary rightProtocol input cut rightRival two.wire.ballot
    (by simpa only [scopeTwo] using rightAdmitted) authTwo
  rw [scopeOne,keyOne,valueOne] at first
  rw [scopeTwo,keyTwo,valueTwo] at second
  apply (ProtocolCapabilityBudget.mem_affected_iff source source.reference vocabulary scope key).mpr
  cases a <;> cases b <;> simp_all

theorem all_admitted_network_branches_agree_under_the_original_source_budget
    (leftProtocol rightProtocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
    (leftRival rightRival : Opponent source.code) (left right : Fin source.code.sites) (leftCount rightCount : Nat)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (leftAdmitted : check source vocabulary leftProtocol scope = true)
    (rightAdmitted : check source vocabulary rightProtocol scope = true)
    (one : BallotQuorum.readout source (BallotQuorum.observed source input cut leftProtocol leftRival vocabulary encoding law left leftCount) scope threshold = .decided a)
    (two : BallotQuorum.readout source (BallotQuorum.observed source input cut rightProtocol rightRival vocabulary encoding law right rightCount) scope threshold = .decided b)
    (safe : source.code.sites + budget source vocabulary scope < threshold + threshold) : a = b := by
  by_contra different
  have first := (BallotQuorum.decided_has_positive_quorum source _ scope threshold a one).2
  have second := (BallotQuorum.decided_has_positive_quorum source _ scope threshold b two).2
  have exposed := Finset.card_le_card (conflicting_support_in_admitted_actual_branches_exposes_original_capacity source vocabulary input cut encoding law
    leftProtocol rightProtocol leftRival rightRival left right leftCount rightCount scope a b different leftAdmitted rightAdmitted)
  have unionBound : (BallotQuorum.support source (BallotQuorum.observed source input cut leftProtocol leftRival vocabulary encoding law left leftCount) scope a ∪
      BallotQuorum.support source (BallotQuorum.observed source input cut rightProtocol rightRival vocabulary encoding law right rightCount) scope b).card ≤ source.code.sites := by
    simpa only [Fintype.card_fin] using (BallotQuorum.support source
      (BallotQuorum.observed source input cut leftProtocol leftRival vocabulary encoding law left leftCount) scope a ∪
        BallotQuorum.support source (BallotQuorum.observed source input cut rightProtocol rightRival vocabulary encoding law right rightCount) scope b).card_le_univ
  have count := Finset.card_union_add_card_inter
    (BallotQuorum.support source (BallotQuorum.observed source input cut leftProtocol leftRival vocabulary encoding law left leftCount) scope a)
    (BallotQuorum.support source (BallotQuorum.observed source input cut rightProtocol rightRival vocabulary encoding law right rightCount) scope b)
  change _ + (affected source vocabulary scope).card < _ at safe
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCapabilityAdmission
