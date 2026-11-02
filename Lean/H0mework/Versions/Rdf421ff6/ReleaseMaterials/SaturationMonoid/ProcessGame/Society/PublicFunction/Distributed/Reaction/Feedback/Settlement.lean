import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (seed : Machine Party Good Port Technology Instrument) (feasible : seed.code.feasible seed.reference)

def selectedSource (budget : Nat) := (Settlement.replacement seed feasible).withFeedback seed.opponent budget

theorem selected_response_is_preserved (budget : Nat) :
    ((selectedSource seed feasible budget).actualExecution seed.history.length).submitted =
      ((Settlement.replacement seed feasible).actualExecution seed.history.length).submitted := by
  have actual := (selectedSource seed feasible budget).actual_reaction_word_and_next
    (Settlement.selection seed feasible).policy.policy.val rfl
  exact actual.1.trans
    (Settlement.original_opponent_response_is_actually_emitted seed
      (Settlement.selection seed feasible).policy.policy).symm

theorem selected_source_keeps_the_original_history_adaptive_opponent (budget : Nat) :
    ((selectedSource seed feasible budget).actualExecution seed.history.length).submitted =
      (execution seed.code (Settlement.selection seed feasible).policy.policy.val seed.history seed.opponent).word ∧
      (selectedSource seed feasible budget).feedback? = some ⟨seed.opponent, budget⟩ := by
  exact ⟨(selected_response_is_preserved seed feasible budget).trans
    (Settlement.original_opponent_response_is_actually_emitted seed
      (Settlement.selection seed feasible).policy.policy), rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback
