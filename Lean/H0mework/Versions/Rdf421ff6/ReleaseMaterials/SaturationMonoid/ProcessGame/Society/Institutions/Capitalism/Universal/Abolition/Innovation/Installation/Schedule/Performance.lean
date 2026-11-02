import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule.Code

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open Abolition.Root.Registered
open Source.Program

theorem all_submitted_performance_positions_are_actual_noncode_attempts
    (word : RawEvent Party Good Bool Nat Unit) :
    ∀ raw ∈ executionInputs word, NonCode raw := by
  intro raw member
  unfold executionInputs at member
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with (⟨request, _, rfl⟩ | rfl) | ⟨request, _, rfl⟩ <;> trivial

theorem the_submitted_programme_selects_its_original_unspent_attempt
    (oldPast : List InputAt) (nature : RequestAt) (attempts : List InputAt)
    (noExecute : ∀ raw ∈ oldPast, beforePublic raw = true)
    (original : ∀ raw ∈ attempts, NonCode raw) :
    selected nature (oldPast ++ submittedInputs oldPast nature ++ attempts) =
      ((executionInputs (observedCode oldPast nature))[attempts.length]?).getD (.execute Control.Scenario.commonWork) := by
  have cuts : publicPast (oldPast ++ submittedInputs oldPast nature ++ attempts) =
      submittedInputs oldPast nature ++ attempts := by
    let tail := [.primitive Control.Scenario.issue,.primitive Control.Scenario.payout,
          .primitive quotedMechanism.investmentRequest,.primitive nature,
          .primitive (Control.Scenario.production 0),.primitive rule.request,
          .code ⟨observedCode oldPast nature⟩] ++ attempts
    have shape : submittedInputs oldPast nature ++ attempts = .execute Control.Scenario.commonWork :: tail := by
      unfold submittedInputs readInputs beforeReadInputs
      rw [the_quote_and_signed_funding_are_fixed_before_any_actual_nature.2.2]
      rfl
    exact (congrArg publicPast (List.append_assoc oldPast (submittedInputs oldPast nature) attempts)).trans
      ((congrArg (fun suffix : List InputAt => publicPast (oldPast ++ suffix)) shape).trans
        ((the_first_actual_public_execution_recovers_its_original_source_cut oldPast Control.Scenario.commonWork tail noExecute).2.trans shape.symm))
  have late : selected nature (oldPast ++ submittedInputs oldPast nature ++ attempts) =
      afterPreparation (oldPast ++ submittedInputs oldPast nature ++ attempts) := by
    unfold selected selectedWith
    rw [the_quote_and_signed_funding_are_fixed_before_any_actual_nature.1, cuts,
      submittedInputs, readInputs, the_pre_read_source_inventory_is_the_original_five_requests,
      the_quote_and_signed_funding_are_fixed_before_any_actual_nature.2.2]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.reduceAdd, if_true]
    rfl
  rw [late]
  simpa only [submittedInputs, List.append_assoc] using
    the_finite_submitted_programme_generates_its_exact_next_attempt
      (oldPast ++ readInputs nature) (observedCode oldPast nature) attempts original

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
