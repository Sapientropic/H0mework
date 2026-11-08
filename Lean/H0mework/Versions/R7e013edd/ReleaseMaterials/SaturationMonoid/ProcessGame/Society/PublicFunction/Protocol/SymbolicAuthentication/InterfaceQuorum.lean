import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterfaceDeviationEnvelope
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmittedStageQuorum

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterfaceQuorum
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

abbrev observed := AdmittedStageQuorum.observed start vocabulary encoding law

-- Reference-admission failures remain actual rows even when the broader fact quorum is safe.
def admissionFailures (stages : List (EventHistory.Stage (code := code))) (scope : Scope) :=
  (StageTrace.records start stages).filter fun row =>
    !(SourceCapabilityAdmission.check start.source vocabulary row.protocol scope)

theorem mem_admissionFailures_iff
    (stages : List (EventHistory.Stage (code := code))) (scope : Scope) (row : StageTrace.Record (code := code)) :
    row ∈ admissionFailures start vocabulary stages scope ↔
      row ∈ StageTrace.records start stages ∧ SourceCapabilityAdmission.check start.source vocabulary row.protocol scope = false := by
  simp only [admissionFailures,List.mem_filter]
  cases SourceCapabilityAdmission.check start.source vocabulary row.protocol scope <;> simp

def produce (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites)
    (scope : Scope) (threshold : Nat) : ProspectiveQuorum.Result :=
  if ¬ code.sites + InterfaceDeviationEnvelope.budget start.source vocabulary scope < threshold + threshold then
    .blocked .unsafeSourceBudget
  else match StageQuorum.readout (observed start vocabulary encoding law stages receiver) scope threshold with
    | .blocked => .blocked .missingQuorum
    | .decided value => .decided value

theorem an_unsafe_source_interface_is_blocked
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites)
    (scope : Scope) (threshold : Nat)
    (unsafeBudget : ¬ code.sites + InterfaceDeviationEnvelope.budget start.source vocabulary scope < threshold + threshold) :
    produce start vocabulary encoding law stages receiver scope threshold = .blocked .unsafeSourceBudget := by
  unfold produce
  rw [if_pos unsafeBudget]

theorem conflicting_received_support_exposes_source_interface_capacity
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (a b : Bool) (different : a ≠ b) :
    StageQuorum.support (observed start vocabulary encoding law leftStages left) scope a ∩
      StageQuorum.support (observed start vocabulary encoding law rightStages right) scope b ⊆
        InterfaceDeviationEnvelope.affected start.source vocabulary scope := by
  intro key member
  obtain ⟨one,present,scopeOne,valueOne,keyOne⟩ := (StageQuorum.mem_support_iff _ scope a key).mp (Finset.mem_inter.mp member).1
  obtain ⟨two,received,scopeTwo,valueTwo,keyTwo⟩ := (StageQuorum.mem_support_iff _ scope b key).mp (Finset.mem_inter.mp member).2
  have originOne := StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law start leftStages left leftStages.length one present
  have originTwo := StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law start rightStages right rightStages.length two received
  have exposed := InterfaceDeviationEnvelope.conflicting_actual_ballots_expose_a_source_affected_key vocabulary start
    leftStages rightStages scope one.wire.ballot two.wire.ballot originOne originTwo
    (keyOne.trans keyTwo.symm) scopeOne scopeTwo (by intro same; exact different (valueOne.symm.trans (same.trans valueTwo)))
  simpa only [keyOne] using exposed

theorem supported_values_agree
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (first : threshold ≤ (StageQuorum.support (observed start vocabulary encoding law leftStages left) scope a).card)
    (second : threshold ≤ (StageQuorum.support (observed start vocabulary encoding law rightStages right) scope b).card)
    (safe : code.sites + InterfaceDeviationEnvelope.budget start.source vocabulary scope < threshold + threshold) : a = b := by
  by_contra different
  have exposed := Finset.card_le_card (conflicting_received_support_exposes_source_interface_capacity start vocabulary encoding law
    leftStages rightStages left right scope a b different)
  have union : (StageQuorum.support (observed start vocabulary encoding law leftStages left) scope a ∪
      StageQuorum.support (observed start vocabulary encoding law rightStages right) scope b).card ≤ code.sites := by
    simpa only [Fintype.card_fin] using (StageQuorum.support (observed start vocabulary encoding law leftStages left) scope a ∪
      StageQuorum.support (observed start vocabulary encoding law rightStages right) scope b).card_le_univ
  have counted := Finset.card_union_add_card_inter
    (StageQuorum.support (observed start vocabulary encoding law leftStages left) scope a)
    (StageQuorum.support (observed start vocabulary encoding law rightStages right) scope b)
  change _ + (InterfaceDeviationEnvelope.affected start.source vocabulary scope).card < _ at safe
  omega

theorem decision_consumes_source_interface_budget_and_actual_quorum
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites)
    (scope : Scope) (threshold : Nat) (value : Bool)
    (done : produce start vocabulary encoding law stages receiver scope threshold = .decided value) :
    code.sites + InterfaceDeviationEnvelope.budget start.source vocabulary scope < threshold + threshold ∧
      StageQuorum.readout (observed start vocabulary encoding law stages receiver) scope threshold = .decided value := by
  unfold produce at done
  split at done <;> try contradiction
  rename_i safe
  split at done <;> try contradiction
  rename_i choice actual
  cases done
  exact ⟨of_not_not safe,actual⟩

theorem produced_decisions_agree_across_all_generated_protocols_and_networks
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : produce start vocabulary encoding law leftStages left scope threshold = .decided a)
    (two : produce start vocabulary encoding law rightStages right scope threshold = .decided b) : a = b := by
  obtain ⟨safe,first⟩ := decision_consumes_source_interface_budget_and_actual_quorum start vocabulary encoding law leftStages left scope threshold a one
  obtain ⟨_,second⟩ := decision_consumes_source_interface_budget_and_actual_quorum start vocabulary encoding law rightStages right scope threshold b two
  exact supported_values_agree start vocabulary encoding law leftStages rightStages left right scope threshold a b
    (StageQuorum.decided_has_positive_quorum _ scope threshold a first).2
    (StageQuorum.decided_has_positive_quorum _ scope threshold b second).2 safe

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterfaceQuorum
