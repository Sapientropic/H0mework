import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule.Observation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open Abolition.Root.Registered

theorem the_source_paid_read_generates_its_own_submitted_code
    (oldPast : List InputAt) (version : Nat)
    (noExecute : ∀ raw ∈ oldPast, beforePublic raw = true)
    (noCode : ∀ raw ∈ oldPast, NonCode raw)
    (paid : (Observation.originalResult input 0 count 0 0 oldPast rule
      (beforeReadInputs (Control.Scenario.discovery version))).isAccepted = true) :
    selected (Control.Scenario.discovery version) (oldPast ++ readInputs (Control.Scenario.discovery version)) =
      .code ⟨observedCode oldPast (Control.Scenario.discovery version)⟩ := by
  let nature := Control.Scenario.discovery version
  have cuts : sourceCut (oldPast ++ readInputs nature) = oldPast ∧
      publicPast (oldPast ++ readInputs nature) = readInputs nature := by
    rw [readInputs, the_pre_read_source_inventory_is_the_original_five_requests]
    exact the_first_actual_public_execution_recovers_its_original_source_cut oldPast _ _ noExecute
  have noSubmitted : ∀ raw ∈ readInputs nature, NonCode raw := by
    intro raw member
    rcases List.mem_append.mp member with original | final
    · exact no_original_pre_read_request_is_a_submitted_code nature raw original
    · obtain rfl := List.mem_singleton.mp final
      trivial
  have unsubmitted := a_prefix_without_submitted_code_has_no_programme_position
    (oldPast ++ readInputs nature) (fun raw member =>
      (List.mem_append.mp member).elim (noCode raw) (noSubmitted raw))
  have late : selected nature (oldPast ++ readInputs nature) = afterPreparation (oldPast ++ readInputs nature) := by
    unfold selected selectedWith
    rw [the_quote_and_signed_funding_are_fixed_before_any_actual_nature.1, cuts.2,
      readInputs, the_pre_read_source_inventory_is_the_original_five_requests,
      the_quote_and_signed_funding_are_fixed_before_any_actual_nature.2.2]
    rfl
  have history := Observation.a_paid_original_read_adds_just_its_one_local_signal
    input 0 count 0 0 oldPast rule (beforeReadInputs nature) paid
  have empty := (the_discovery_prefix_contains_no_prior_local_observation oldPast version).1
  change Observation.localHistory input 0 count 0 0 oldPast rule (beforeReadInputs nature) = [] at empty
  have generated : Observation.programmeFromSensor rule programme
      (Observation.localHistory input 0 count 0 0 oldPast rule (readInputs nature)) =
        some (observedCode oldPast nature) := by
    change Observation.programmeFromSensor rule programme
      (Observation.localHistory input 0 count 0 0 oldPast rule
        (beforeReadInputs nature ++ [.primitive rule.request])) = _
    rw [history,empty,List.nil_append]
    exact Observation.a_new_paid_signal_drives_the_fixed_rule rule programme [] _
  rw [late, afterPreparation, afterPreparationWith, unsubmitted]
  unfold localProposal
  rw [cuts.1,cuts.2]
  simp only [Observation.scheduledProposal, generated]
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
