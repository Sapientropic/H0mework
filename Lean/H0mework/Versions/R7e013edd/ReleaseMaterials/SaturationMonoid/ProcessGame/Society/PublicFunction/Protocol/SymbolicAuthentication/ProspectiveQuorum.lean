import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCapabilityAdmission

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProspectiveQuorum
open Distributed Reaction Reaction.Feedback

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : AttestationTransport.Encoding source) (law : AttestationReception.ReceptionLaw source)

inductive Obstruction where
  | unadmittedCapability | unsafeSourceBudget | missingQuorum
  deriving DecidableEq
inductive Result where
  | blocked (reason : Obstruction)
  | decided (choice : Bool)
  deriving DecidableEq

def produce (receiver : Fin source.code.sites) (count : Nat) (scope : Scope) (threshold : Nat) : Result :=
  if SourceCapabilityAdmission.check source vocabulary protocol scope ≠ true then .blocked .unadmittedCapability
  else if ¬ source.code.sites + SourceCapabilityAdmission.budget source vocabulary scope < threshold + threshold then
    .blocked .unsafeSourceBudget
  else match BallotQuorum.readout source
      (BallotQuorum.observed source input cut protocol rival vocabulary encoding law receiver count) scope threshold with
    | .blocked => .blocked .missingQuorum
    | .decided value => .decided value

theorem decision_consumes_source_capability_and_actual_received_quorum
    (receiver : Fin source.code.sites) (count : Nat) (scope : Scope) (threshold : Nat) (value : Bool)
    (done : produce source input cut protocol rival vocabulary encoding law receiver count scope threshold = .decided value) :
    SourceCapabilityAdmission.check source vocabulary protocol scope = true ∧
      source.code.sites + SourceCapabilityAdmission.budget source vocabulary scope < threshold + threshold ∧
      BallotQuorum.readout source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law receiver count) scope threshold = .decided value := by
  unfold produce at done
  split at done <;> try contradiction
  rename_i admitted
  split at done <;> try contradiction
  rename_i safe
  split at done <;> try contradiction
  rename_i choice actual
  cases done
  exact ⟨of_not_not admitted,of_not_not safe,actual⟩

theorem produced_values_agree_across_all_actual_network_histories
    (otherProtocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code) (otherRival : Opponent source.code) (left right : Fin source.code.sites) (leftCount rightCount : Nat)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : produce source input cut protocol rival vocabulary encoding law left leftCount scope threshold = .decided a)
    (two : produce source input cut otherProtocol otherRival vocabulary encoding law right rightCount scope threshold = .decided b) : a = b := by
  obtain ⟨leftAdmitted,safe,first⟩ := decision_consumes_source_capability_and_actual_received_quorum source input cut protocol rival vocabulary encoding law
    left leftCount scope threshold a one
  obtain ⟨rightAdmitted,_,second⟩ := decision_consumes_source_capability_and_actual_received_quorum source input cut otherProtocol otherRival vocabulary encoding law
    right rightCount scope threshold b two
  exact SourceCapabilityAdmission.all_admitted_network_branches_agree_under_the_original_source_budget source vocabulary input cut encoding law
    protocol otherProtocol rival otherRival left right leftCount rightCount scope threshold a b leftAdmitted rightAdmitted first second safe

theorem every_decision_has_an_actual_authenticated_supporting_origin
    (receiver : Fin source.code.sites) (count : Nat) (scope : Scope) (threshold : Nat) (value : Bool)
    (done : produce source input cut protocol rival vocabulary encoding law receiver count scope threshold = .decided value) :
    ∃ receipt ∈ (BallotQuorum.observed source input cut protocol rival vocabulary encoding law receiver count).receipts,
      receipt.wire.ballot.scope = scope ∧ receipt.wire.ballot.choice = value ∧
      OwnedAttestation.verify source input cut protocol rival vocabulary receipt.wire.ballot = true ∧ receipt.wire.ballot.cut < count :=
  BallotQuorum.decided_has_source_authenticated_support source input cut protocol rival vocabulary encoding law receiver count scope threshold value
    (decision_consumes_source_capability_and_actual_received_quorum source input cut protocol rival vocabulary encoding law receiver count scope threshold value done).2.2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProspectiveQuorum
