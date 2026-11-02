import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Regression

/-! Actual scheduled candidates with explicit no-policy cuts and delayed repayment. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Execution.Regression

open Institutions.Capitalism.Universal.Root

abbrev code := Feedback.Regression.code
abbrev policy := Feedback.Regression.policy

def opponent : Opponent code := fun history past _ =>
  if history.length = 1 then
    if past.isEmpty then some ⟨.activate 0, by decide +kernel⟩ else none
  else if history.length = 2 then some ⟨.send 0 0, by decide +kernel⟩
  else if history.length = 3 then some ⟨.deliver 0, by decide +kernel⟩
  else some ⟨.activate 0, by decide +kernel⟩

abbrev source := Feedback.Regression.base.withFeedback opponent 8
abbrev input : Input code := ⟨opponent, 8⟩
abbrev term : List (Option code.Policy) := [none, some policy]
abbrev candidate := target source 2 term

theorem the_schedule_is_generated_from_the_actual_cut : term ∈ Residual.scheduleTerms source input 2 := by
  apply (mem_sequences_iff _ _ _).mpr
  constructor
  · decide +kernel
  · intro control member
    simp only [term, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem the_candidate_really_pauses_then_pays_its_own_original_debt :
    (candidate.actualExecution 4).submitted = [] ∧
      (candidate.actualExecution 5).submitted = [Feedback.Regression.repay] ∧
      Financial.outstanding candidate.input (Native.generate candidate 4).finance.current = 2 ∧
      Financial.outstanding candidate.input (Native.generate candidate 5).finance.current = 0 ∧
      (candidate.actualExecution 5).after.stock false () = 2 ∧
      (candidate.feedbackState input 4).remaining = 4 ∧
      (candidate.feedbackState input 3).history.length = 5 := by
  decide +kernel

abbrev quiet : code.Policy := fun _ _ => []
abbrev quietCandidate := target source 2 [some quiet, some policy]

theorem no_policy_and_an_empty_policy_have_different_actual_observations :
    (candidate.actualExecution 4).submitted = (quietCandidate.actualExecution 4).submitted ∧
      (candidate.feedbackState input 3).past.length = 3 ∧
      (quietCandidate.feedbackState input 3).past.length = 4 := by
  decide +kernel

theorem all_original_financial_images_are_generated_before_the_scheduled_cut :
    Native.Coupling.Match source.code source.input candidate.input
      (Financial.accountAt source.input 5) (Financial.accountAt candidate.input 5) :=
  complete_finance_before source 2 term 5 (by decide +kernel)

theorem the_independent_financial_prefix_verifier_accepts :
    Native.Coupling.verify source.code source.input candidate.input
      (Financial.accountAt source.input 5) (Financial.accountAt candidate.input 5) = true :=
  (Native.Coupling.verify_iff _ _ _ _ _).mpr all_original_financial_images_are_generated_before_the_scheduled_cut

theorem an_omitted_schedule_does_not_change_the_future_overrides :
    (target (source.atFeedbackControlCut 4 none) 2 [some policy]).feedbackPolicy 4 = none := by
  exact (policy_at (source.atFeedbackControlCut 4 none) 2 [some policy] 2).trans
    (source.scheduled_control_is_used_at_its_own_cut 4 none)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Execution.Regression
