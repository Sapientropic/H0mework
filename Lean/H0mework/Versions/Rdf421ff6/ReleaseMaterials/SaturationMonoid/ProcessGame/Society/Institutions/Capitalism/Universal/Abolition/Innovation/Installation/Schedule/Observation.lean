import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule.PreRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule.Programme

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open Abolition.Root.Registered

theorem no_original_pre_read_request_is_a_submitted_code (nature : RequestAt) :
    ∀ raw ∈ beforeReadInputs nature, NonCode raw := by
  rw [the_pre_read_source_inventory_is_the_original_five_requests]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  intro raw member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem the_discovery_prefix_contains_no_prior_local_observation
    (oldPast : List InputAt) (version : Nat) :
    Observation.localHistory input 0 count 0 0 oldPast rule (beforeReadInputs (Control.Scenario.discovery version)) = [] ∧
      Observation.hasOwnAttempt rule (beforeReadInputs (Control.Scenario.discovery version)) = false := by
  rw [the_pre_read_source_inventory_is_the_original_five_requests]
  exact ⟨rfl,rfl⟩

theorem the_discovery_source_actually_requests_its_own_paid_observation
    (oldPast : List InputAt) (version : Nat)
    (noExecute : ∀ raw ∈ oldPast, beforePublic raw = true)
    (noCode : ∀ raw ∈ oldPast, NonCode raw) :
    selected (Control.Scenario.discovery version) (oldPast ++ beforeReadInputs (Control.Scenario.discovery version)) =
      .primitive rule.request := by
  let nature := Control.Scenario.discovery version
  have cuts : sourceCut (oldPast ++ beforeReadInputs nature) = oldPast ∧
      publicPast (oldPast ++ beforeReadInputs nature) = beforeReadInputs nature := by
    rw [the_pre_read_source_inventory_is_the_original_five_requests]
    exact the_first_actual_public_execution_recovers_its_original_source_cut oldPast _ _ noExecute
  have unsubmitted : codeProgress (oldPast ++ beforeReadInputs nature) = none :=
    a_prefix_without_submitted_code_has_no_programme_position _ (fun raw member =>
      (List.mem_append.mp member).elim (noCode raw) (no_original_pre_read_request_is_a_submitted_code nature raw))
  have late : selected nature (oldPast ++ beforeReadInputs nature) = afterPreparation (oldPast ++ beforeReadInputs nature) := by
    unfold selected selectedWith
    rw [the_quote_and_signed_funding_are_fixed_before_any_actual_nature.1, cuts.2,
      the_pre_read_source_inventory_is_the_original_five_requests,
      the_quote_and_signed_funding_are_fixed_before_any_actual_nature.2.2]
    rfl
  rw [late, afterPreparation, afterPreparationWith, unsubmitted]
  unfold localProposal
  rw [cuts.1,cuts.2]
  have empty := the_discovery_prefix_contains_no_prior_local_observation oldPast version
  change Observation.localHistory input 0 count 0 0 oldPast rule (beforeReadInputs nature) = [] ∧
    Observation.hasOwnAttempt rule (beforeReadInputs nature) = false at empty
  simp only [Observation.scheduledProposal, empty.1, Observation.programmeFromSensor,
    List.reverse_nil, Observation.latestReading, empty.2, Bool.false_eq_true, ↓reduceIte]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
