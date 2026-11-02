import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Regression

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual.Regression

abbrev source := Feedback.Regression.source
abbrev input := Feedback.Regression.input
abbrev code := Feedback.Regression.code

def quiet : code.Policy := fun _ _ => []
abbrev revised := source.atFeedbackCut 5 quiet

theorem an_omitted_suffix_keeps_the_actual_future_override :
    scheduleAt revised 2 [] 3 = some quiet ∧
      scheduleAt revised 2 [some Feedback.Regression.policy] 3 = some quiet := ⟨rfl, rfl⟩

theorem explicit_none_does_not_mean_an_omitted_schedule_entry :
    scheduleAt revised 2 [none, some Feedback.Regression.policy] 0 = none ∧
      scheduleAt revised 2 [none, some Feedback.Regression.policy] 1 = some Feedback.Regression.policy ∧
      scheduleAt revised 2 [none, some Feedback.Regression.policy] 3 = some quiet := ⟨rfl, rfl, rfl⟩

theorem the_original_future_override_is_inside_the_generated_menu :
    some quiet ∈ controlMenu revised := by
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨(5, some quiet), by simp [revised, Machine.atFeedbackCut, source], rfl⟩

theorem the_revised_baseline_is_the_complete_actual_future :
    run code (scheduleAt revised 2 []) input (seed revised input 2) 4 = revised.feedbackState input 6 :=
  baseline_is_the_complete_actual_successor revised input 2 4

def recoveringOpponent : Opponent code := fun history _ _ =>
  if history.length = (source.feedbackState input 2).history.length then none
  else some ⟨.activate 0, by decide +kernel⟩

abbrev recoveringRun := run code (fun _ => some Feedback.Regression.policy) ⟨recoveringOpponent, 0⟩
  (source.feedbackState input 2)

theorem an_empty_response_can_resume_without_resetting_history_or_budget :
    (recoveringRun 1).history = (source.feedbackState input 2).history ++ [[]] ∧
      (recoveringRun 1).past = (source.feedbackState input 2).past ∧
      (recoveringRun 2).current.stock false () = 2 ∧
      (recoveringRun 2).history.length = (source.feedbackState input 2).history.length + 2 ∧
      (recoveringRun 2).remaining = 4 := by
  decide +kernel

theorem changing_only_visible_history_changes_the_opponent_key :
    key code {source.feedbackState input 2 with history := (source.feedbackState input 2).history ++ [[]]} ≠
      key code (source.feedbackState input 2) := by
  intro same
  have lengths := congrArg (fun observed => observed.1.length) same
  simp only [key, List.length_append, List.length_singleton] at lengths
  omega

theorem exhausted_actual_seed_generates_no_decision_authority :
    keys code (seed source input 8) (schedules source input 8) = [] :=
  exhausted_seed_has_no_decision_keys code _ _ (by decide +kernel)

theorem the_same_actual_cut_covers_every_future_opponent : FutureCoverage source input 2 :=
  (generate source input 2).future_coverage

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual.Regression
