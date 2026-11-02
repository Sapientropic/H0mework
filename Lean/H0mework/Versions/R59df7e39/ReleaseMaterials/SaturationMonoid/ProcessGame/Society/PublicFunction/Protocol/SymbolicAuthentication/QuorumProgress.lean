import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptProgress
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BallotQuorum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QuorumProgress

open Distributed Reaction Reaction.Feedback

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : AttestationTransport.Encoding source) (law : AttestationReception.ReceptionLaw source)

def availableAt (receiver : Fin source.code.sites) (scope : Scope) (value : Bool) (horizon send : Nat) :
    Option (Fin source.code.sites) :=
  match ReceiptProgress.plan source input cut protocol vocabulary encoding law send with
  | .blocked _ => none
  | .ready wire =>
    if wire.recipient = receiver ∧ wire.ballot.scope = scope ∧ wire.ballot.choice = value ∧
        ReceiptProgress.deadline source send ≤ horizon then some wire.ballot.key else none

/-- Distinct support is generated from source sends with checked communication
windows, before looking at the receiver's receipt list or decision. -/
def readySupport (receiver : Fin source.code.sites) (scope : Scope) (value : Bool) (count horizon : Nat) : Finset (Fin source.code.sites) :=
  ((List.range count).filterMap (availableAt source input cut protocol vocabulary encoding law receiver scope value horizon)).toFinset

abbrev observed (receiver : Fin source.code.sites) (horizon : Nat) :=
  AttestationReception.run source input cut protocol (QueueScheduler.environment source input cut) vocabulary encoding law receiver horizon

theorem generated_support_is_in_the_actual_receiver
    (receiver : Fin source.code.sites) (scope : Scope) (value : Bool) (count horizon : Nat) :
    readySupport source input cut protocol vocabulary encoding law receiver scope value count horizon ⊆
      BallotQuorum.support source (observed source input cut protocol vocabulary encoding law receiver horizon) scope value := by
  intro key inside
  obtain ⟨send, _, selected⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp inside)
  unfold availableAt at selected
  split at selected <;> try contradiction
  rename_i wire ready
  split at selected <;> try contradiction
  rename_i aligned
  have keyEq := Option.some.inj selected
  obtain ⟨_, receipt, actual, same⟩ := ReceiptProgress.ready_plan_generates_a_valid_receipt
    source input cut protocol vocabulary encoding law send wire ready
  have received := (ReceiptProgress.receipts_are_preserved source input cut protocol (QueueScheduler.environment source input cut)
    vocabulary encoding law wire.recipient (ReceiptProgress.deadline source send) horizon aligned.2.2.2).subset actual
  apply (BallotQuorum.mem_support_iff source _ scope value key).mpr
  rw [aligned.1] at received
  exact ⟨receipt, received, (congrArg OwnedAttestation.BallotData.scope same).trans aligned.2.1,
    (congrArg OwnedAttestation.BallotData.choice same).trans aligned.2.2.1,
    (congrArg OwnedAttestation.BallotData.key same).trans keyEq⟩

theorem positive_actual_support_generates_a_decision
    (receiver : Fin source.code.sites) (scope : Scope) (value : Bool) (horizon threshold : Nat)
    (positive : 0 < threshold)
    (enough : threshold ≤ (BallotQuorum.support source
      (observed source input cut protocol vocabulary encoding law receiver horizon) scope value).card) :
    ∃ choice, BallotQuorum.readout source
      (observed source input cut protocol vocabulary encoding law receiver horizon) scope threshold = .decided choice := by
  unfold BallotQuorum.readout
  rw [if_neg (by omega)]
  cases found : [false, true].find? (fun choice => decide (threshold ≤ (BallotQuorum.support source
      (observed source input cut protocol vocabulary encoding law receiver horizon) scope choice).card)) with
  | some choice => exact ⟨choice, rfl⟩
  | none =>
    have absent := List.find?_eq_none.mp found value (by cases value <;> simp)
    exact False.elim (absent (decide_eq_true enough))

theorem source_generated_windows_terminate_the_quorum_readout
    (receiver : Fin source.code.sites) (scope : Scope) (value : Bool) (count horizon threshold : Nat)
    (positive : 0 < threshold)
    (enough : threshold ≤ (readySupport source input cut protocol vocabulary encoding law receiver scope value count horizon).card) :
    ∃ choice, BallotQuorum.readout source
      (observed source input cut protocol vocabulary encoding law receiver horizon) scope threshold = .decided choice :=
  positive_actual_support_generates_a_decision source input cut protocol vocabulary encoding law receiver scope value horizon threshold
    positive (le_trans enough (Finset.card_le_card (generated_support_is_in_the_actual_receiver
      source input cut protocol vocabulary encoding law receiver scope value count horizon)))

theorem generated_windows_and_source_budget_decide_the_supported_value
    (receiver : Fin source.code.sites) (scope : Scope) (value : Bool) (count horizon threshold : Nat)
    (positive : 0 < threshold)
    (enough : threshold ≤ (readySupport source input cut protocol vocabulary encoding law receiver scope value count horizon).card)
    (budget : source.code.sites + DeviationBudget.budget source input cut protocol
      (QueueScheduler.environment source input cut) vocabulary horizon < threshold + threshold) :
    BallotQuorum.readout source (observed source input cut protocol vocabulary encoding law receiver horizon) scope threshold = .decided value := by
  obtain ⟨choice, decided⟩ := source_generated_windows_terminate_the_quorum_readout
    source input cut protocol vocabulary encoding law receiver scope value count horizon threshold positive enough
  have same : choice = value := by
    by_contra different
    have first := (BallotQuorum.decided_has_positive_quorum source _ scope threshold choice decided).2
    have second := le_trans enough (Finset.card_le_card (generated_support_is_in_the_actual_receiver
      source input cut protocol vocabulary encoding law receiver scope value count horizon))
    have intersection := Finset.card_le_card (BallotQuorum.conflicting_intersection_is_in_source_budget
      source input cut protocol (QueueScheduler.environment source input cut) vocabulary encoding law
      receiver receiver horizon horizon horizon (Nat.le_refl _) (Nat.le_refl _) scope choice value different)
    have union : (BallotQuorum.support source (observed source input cut protocol vocabulary encoding law receiver horizon) scope choice ∪
        BallotQuorum.support source (observed source input cut protocol vocabulary encoding law receiver horizon) scope value).card ≤ source.code.sites := by
      simpa only [Fintype.card_fin] using
        (BallotQuorum.support source (observed source input cut protocol vocabulary encoding law receiver horizon) scope choice ∪
          BallotQuorum.support source (observed source input cut protocol vocabulary encoding law receiver horizon) scope value).card_le_univ
    have counted := Finset.card_union_add_card_inter
      (BallotQuorum.support source (observed source input cut protocol vocabulary encoding law receiver horizon) scope choice)
      (BallotQuorum.support source (observed source input cut protocol vocabulary encoding law receiver horizon) scope value)
    change (BallotQuorum.support source (observed source input cut protocol vocabulary encoding law receiver horizon) scope choice ∩
      BallotQuorum.support source (observed source input cut protocol vocabulary encoding law receiver horizon) scope value).card ≤
        DeviationBudget.budget source input cut protocol (QueueScheduler.environment source input cut) vocabulary horizon at intersection
    omega
  exact same ▸ decided

theorem a_threshold_above_the_actual_site_domain_is_blocked
    (receiver : Fin source.code.sites) (scope : Scope) (horizon threshold : Nat)
    (tooLarge : source.code.sites < threshold) :
    BallotQuorum.readout source (observed source input cut protocol vocabulary encoding law receiver horizon) scope threshold = .blocked := by
  cases result : BallotQuorum.readout source (observed source input cut protocol vocabulary encoding law receiver horizon) scope threshold with
  | blocked => rfl
  | decided value =>
    have enough := (BallotQuorum.decided_has_positive_quorum source _ scope threshold value result).2
    have capacity := (BallotQuorum.support source (observed source input cut protocol vocabulary encoding law receiver horizon) scope value).card_le_univ
    simp only [Fintype.card_fin] at capacity
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QuorumProgress
