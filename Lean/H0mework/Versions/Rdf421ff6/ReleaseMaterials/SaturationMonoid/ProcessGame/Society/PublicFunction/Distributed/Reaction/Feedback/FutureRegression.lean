import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Future
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.ExecutionRegression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Future.Regression

open Institutions.Capitalism.Universal.Root

abbrev source := Execution.Regression.source
abbrev input := Execution.Regression.input
abbrev policy := Execution.Regression.policy

def opponent : Opponent source.code := fun history _ _ =>
  if history.length < 5 then none else some ⟨.activate 0, by decide +kernel⟩

abbrev term : List (Option source.code.Policy) := []
abbrev candidate := target source input 2 opponent term
abbrev candidateInput := takeover source input 2 opponent
abbrev replayed := source.withFeedback opponent input.budget
abbrev stalled := target source input 2 (fun _ _ _ => none) term

theorem the_baseline_term_is_generated : term ∈ Residual.scheduleTerms source input 2 :=
  (mem_sequences_iff _ _ _).mpr ⟨Nat.zero_le _, by simp [term]⟩

theorem the_future_opponent_cannot_rewrite_its_actual_past_or_reset_its_budget :
    candidate.responseFrame.word = source.responseFrame.word ∧
      (candidate.actualExecution 4).submitted = [] ∧
      (candidate.actualExecution 5).submitted = [Feedback.Regression.repay] ∧
      (candidate.feedbackState candidateInput 2).remaining = 6 ∧
      (candidate.feedbackState candidateInput 4).remaining = 4 ∧
      Financial.outstanding candidate.input (Native.generate candidate 4).finance.current = 2 ∧
      Financial.outstanding candidate.input (Native.generate candidate 5).finance.current = 0 ∧
      (candidate.actualExecution 5).after.stock false () = 2 ∧
      (replayed.actualExecution 1).submitted = [] ∧
      Financial.outstanding stalled.input (Native.generate stalled 5).finance.current = 2 := by
  refine ⟨rfl, ?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact (future_word_is_actually_submitted source input 2 opponent term rfl 0).trans (by rfl)
  · exact (future_word_is_actually_submitted source input 2 opponent term rfl 1).trans (by decide +kernel)

theorem every_original_financial_image_survives_the_actual_takeover :
    Native.Coupling.Match source.code source.input candidate.input
      (Financial.accountAt source.input 5) (Financial.accountAt candidate.input 5) :=
  complete_finance_before source input 2 opponent term rfl 5 (by decide +kernel)

theorem the_independent_financial_verifier_accepts_the_takeover :
    Native.Coupling.verify source.code source.input candidate.input
      (Financial.accountAt source.input 5) (Financial.accountAt candidate.input 5) = true :=
  (Native.Coupling.verify_iff _ _ _ _ _).mpr every_original_financial_image_survives_the_actual_takeover

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Future.Regression
