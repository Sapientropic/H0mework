import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Regression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.FutureRegression

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

abbrev need := Reaction.Regression.need
def waste : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .use true [((), 2)] .contribution⟩
abbrev code : Code Bool Unit Unit Unit Unit := {Reaction.Regression.code with
  initial := {Reaction.Regression.code.initial with claims := fun _ _ _ => 0}
  bootstrap := []
  historyAlphabet := [[need]]
  historyLimit := 1
  actions := [waste]
  actionLimit := 1
  eligible := fun _ => true}
def reference : code.Policy := fun _ _ => [waste]
theorem reference_generated : reference ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [reference])
def rival : Opponent code := fun history _ _ =>
  if history.length = 1 then none else some ⟨.activate 0, by decide +kernel⟩
abbrev input : Input code := ⟨rival, 1⟩
def source : Machine Bool Unit Unit Unit Unit where
  code := code
  reference := reference
  reference_generated := reference_generated
  history := [[need]]
  original := by decide +kernel
  opponent := rival
  side := .original
  feedback? := some input

abbrev quiet : Term source input 0 := ⟨[none], (mem_sequences_iff _ _ _).mpr
  ⟨by decide +kernel, by simp [Residual.controlMenu]⟩⟩

theorem original_is_feasible : Feasible source input 0 (baseline source input 0) := by
  unfold Feasible LocalValidity Service
  decide +kernel

theorem quiet_is_feasible : Feasible source input 0 quiet := by
  unfold Feasible LocalValidity Service
  decide +kernel

theorem quiet_is_a_strict_improvement_against_the_same_future_opponents : Better source input 0 (baseline source input 0) quiet := by
  apply (strictness_comes_from_actual_values source input 0 _ _).mpr
  exact ⟨by unfold Improves NoWorse; decide +kernel, by decide +kernel⟩

abbrev chosen := selection source input 0 original_is_feasible
abbrev candidate := replacement source input 0 original_is_feasible
abbrev candidateInput := replacementInput source input 0

private def isNoPolicy : List (Option code.Policy) → Bool
  | [none] => true | _ => false

theorem the_actual_selection_emits_no_waste : chosen.policy.term.val = [none] := by
  have tag : isNoPolicy chosen.policy.term.val = true := by decide +kernel
  cases controls : chosen.policy.term.val with
  | nil => simp [controls, isNoPolicy] at tag
  | cons head tail =>
    cases head <;> cases tail <;> simp_all [isNoPolicy]

theorem the_actual_candidate_is_the_quiet_source : candidate = machine source input 0 rival quiet := by
  exact congrArg (machine source input 0 rival) (Subtype.ext the_actual_selection_emits_no_waste)

theorem the_actual_candidate_keeps_resources_with_its_own_native_accounts :
    (candidate.actualExecution 2).submitted = [] ∧
      (candidate.actualExecution 2).after.stock true () = 2 ∧
      ((machine source input 0 rival (baseline source input 0)).actualExecution 2).after.stock true () = 0 ∧
      Financial.outstanding candidate.input (Native.generate candidate 2).finance.current = 0 ∧
      received source input 0 rival chosen.policy.term 0 false = 0 ∧
      verify source input 0 (baseline source input 0) chosen.policy.term = true := by
  refine ⟨?_, ?_, by decide +kernel, ?_, ?_, independent_replay_accepts_selection source input 0 _ chosen⟩
  · rw [the_actual_candidate_is_the_quiet_source]; decide +kernel
  · rw [the_actual_candidate_is_the_quiet_source]; decide +kernel
  · rw [the_actual_candidate_is_the_quiet_source]; decide +kernel
  · rw [show chosen.policy.term = quiet from Subtype.ext the_actual_selection_emits_no_waste]
    decide +kernel


abbrev debtSource := Feedback.Execution.Regression.source.withFeedback Feedback.Execution.Regression.opponent 4
abbrev debtInput : Input debtSource.code := ⟨Feedback.Execution.Regression.opponent, 4⟩
abbrev debtRival := Feedback.Future.Regression.opponent
abbrev debtTerm := baseline debtSource debtInput 2

theorem the_nonzero_original_slot_reads_actual_receipts_and_remaining_separately :
    remaining debtSource debtInput 2 debtRival debtTerm 0 false = 0 ∧
      received debtSource debtInput 2 debtRival debtTerm 0 false = 2 := by
  constructor <;> decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Regression
