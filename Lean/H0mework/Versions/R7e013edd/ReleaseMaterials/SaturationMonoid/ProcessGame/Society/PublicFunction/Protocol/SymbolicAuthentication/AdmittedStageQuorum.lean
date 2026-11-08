import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageSourceAdmission
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProspectiveQuorum
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQuorum

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmittedStageQuorum
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

abbrev Result := ProspectiveQuorum.Result
abbrev observed (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) :=
  StageReception.run vocabulary encoding law start stages receiver stages.length

def produce (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) : Result :=
  if StageSourceAdmission.check start vocabulary stages scope ≠ true then .blocked .unadmittedCapability
  else if ¬ code.sites + StageSourceAdmission.budget start vocabulary scope < threshold + threshold then .blocked .unsafeSourceBudget
  else match StageQuorum.readout (observed start vocabulary encoding law stages receiver) scope threshold with
    | .blocked => .blocked .missingQuorum
    | .decided value => .decided value

theorem conflicting_received_support_is_in_the_initial_source_capacity
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (a b : Bool) (different : a ≠ b)
    (firstChecked : StageSourceAdmission.check start vocabulary leftStages scope = true)
    (secondChecked : StageSourceAdmission.check start vocabulary rightStages scope = true) :
    StageQuorum.support (observed start vocabulary encoding law leftStages left) scope a ∩
      StageQuorum.support (observed start vocabulary encoding law rightStages right) scope b ⊆
        SourceCapabilityAdmission.affected start.source vocabulary scope := by
  intro key member
  obtain ⟨one,present,scopeOne,valueOne,keyOne⟩ := (StageQuorum.mem_support_iff _ scope a key).mp (Finset.mem_inter.mp member).1
  obtain ⟨two,received,scopeTwo,valueTwo,keyTwo⟩ := (StageQuorum.mem_support_iff _ scope b key).mp (Finset.mem_inter.mp member).2
  have originOne := StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law start leftStages left leftStages.length one present
  have originTwo := StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law start rightStages right rightStages.length two received
  have exposed := StageSourceAdmission.conflicting_actual_ballots_from_admitted_stage_histories_expose_initial_capacity start vocabulary
    leftStages rightStages scope firstChecked secondChecked one.wire.ballot two.wire.ballot originOne originTwo
    (keyOne.trans keyTwo.symm) scopeOne scopeTwo (by intro same; exact different (valueOne.symm.trans (same.trans valueTwo)))
  simpa only [keyOne] using exposed

theorem supported_values_agree
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (firstChecked : StageSourceAdmission.check start vocabulary leftStages scope = true)
    (secondChecked : StageSourceAdmission.check start vocabulary rightStages scope = true)
    (first : threshold ≤ (StageQuorum.support (observed start vocabulary encoding law leftStages left) scope a).card)
    (second : threshold ≤ (StageQuorum.support (observed start vocabulary encoding law rightStages right) scope b).card)
    (safe : code.sites + StageSourceAdmission.budget start vocabulary scope < threshold + threshold) : a = b := by
  by_contra different
  have exposed := Finset.card_le_card (conflicting_received_support_is_in_the_initial_source_capacity start vocabulary encoding law
    leftStages rightStages left right scope a b different firstChecked secondChecked)
  have union : (StageQuorum.support (observed start vocabulary encoding law leftStages left) scope a ∪
      StageQuorum.support (observed start vocabulary encoding law rightStages right) scope b).card ≤ code.sites := by
    simpa only [Fintype.card_fin] using (StageQuorum.support (observed start vocabulary encoding law leftStages left) scope a ∪
      StageQuorum.support (observed start vocabulary encoding law rightStages right) scope b).card_le_univ
  have counted := Finset.card_union_add_card_inter
    (StageQuorum.support (observed start vocabulary encoding law leftStages left) scope a)
    (StageQuorum.support (observed start vocabulary encoding law rightStages right) scope b)
  change _ + (SourceCapabilityAdmission.affected start.source vocabulary scope).card < _ at safe
  omega

theorem decision_has_original_admission_budget_and_actual_quorum
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) (value : Bool)
    (done : produce start vocabulary encoding law stages receiver scope threshold = .decided value) :
    StageSourceAdmission.check start vocabulary stages scope = true ∧
      code.sites + StageSourceAdmission.budget start vocabulary scope < threshold + threshold ∧
      StageQuorum.readout (observed start vocabulary encoding law stages receiver) scope threshold = .decided value := by
  unfold produce at done
  split at done <;> try contradiction
  rename_i admitted
  split at done <;> try contradiction
  rename_i safe
  split at done <;> try contradiction
  rename_i choice actual
  cases done
  exact ⟨of_not_not admitted,of_not_not safe,actual⟩

theorem produced_decisions_agree_across_adaptive_installations_and_networks
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : produce start vocabulary encoding law leftStages left scope threshold = .decided a)
    (two : produce start vocabulary encoding law rightStages right scope threshold = .decided b) : a = b := by
  obtain ⟨leftAdmitted,safe,first⟩ := decision_has_original_admission_budget_and_actual_quorum start vocabulary encoding law leftStages left scope threshold a one
  obtain ⟨rightAdmitted,_,second⟩ := decision_has_original_admission_budget_and_actual_quorum start vocabulary encoding law rightStages right scope threshold b two
  exact supported_values_agree start vocabulary encoding law leftStages rightStages left right scope threshold a b leftAdmitted rightAdmitted
    (StageQuorum.decided_has_positive_quorum _ scope threshold a first).2
    (StageQuorum.decided_has_positive_quorum _ scope threshold b second).2 safe

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmittedStageQuorum
