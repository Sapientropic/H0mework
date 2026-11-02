import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Machine

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument)

def actualScore : Metric Party Good Instrument → ℚ
  | .raw component =>
    let actual := source.actualExecution source.history.length
    match component with
    | .debit p g => source.code.law.totalDebit actual.interpreted.items p g
    | .credit p g => - source.code.law.totalCredit actual.interpreted.items p g
    | .inventory p g => - actual.after.stock p g
    | .liability i d c => actual.after.claims i d c
    | .claim i d c => - actual.after.claims i d c
    | .clock => actual.after.clock
  | .admissibility => if source.code.eligible
      (source.emissionEvents (source.actualExecution source.history.length).before) then 0 else 1

theorem opponent_payoff_is_the_actual_receipt_vector (policy : source.code.Policy)
    (chosen : source.policy? = some policy) (metric : Metric Party Good Instrument) :
    source.actualScore metric = payoff source.code policy source.history source.opponent metric := by
  have actual := source.actual_reaction_word_and_next policy chosen
  have items : (source.actualExecution source.history.length).interpreted.items = source.code.law.rawItems
      (source.code.historyCurrent source.history) (execution source.code policy source.history source.opponent).word := by
    rw [(source.actualExecution source.history.length).interpreted_exact, actual.2.1, actual.1]
    rfl
  cases metric with
  | raw component =>
    cases component <;>
      simp only [actualScore, payoff, Code.cost, Code.executed, items, actual.2.2.1, execution]
  | admissibility =>
    simp only [actualScore, actual.2.1, payoff, emissionEvents, chosen, trace]
    rfl

theorem original_policy_is_emitted : (source.withSide .original).policy? = some source.reference := rfl

theorem selected_policy_is_emitted (choice : Selection source.code source.reference)
    (generated : source.answer = .selected choice) :
    (source.withSide .replacement).policy? = some choice.policy.policy := by
  simp only [policy?, policyForSide, withSide, answer] at *
  rw [generated]

/-- Two source executions, with their own receipts and literal next, share
one opponent function. No equality of root occurrences is asserted. -/
theorem same_opponent_compares_both_actual_sources (choice : Selection source.code source.reference)
    (generated : source.answer = .selected choice) :
    ∀ metric, (source.withSide .replacement).actualScore metric ≤ (source.withSide .original).actualScore metric := by
  intro metric
  rw [(source.withSide .replacement).opponent_payoff_is_the_actual_receipt_vector choice.policy.policy
      (source.selected_policy_is_emitted choice generated),
    (source.withSide .original).opponent_payoff_is_the_actual_receipt_vector source.reference
      source.original_policy_is_emitted]
  exact (finite_comparison_iff_every_same_opponent source.code _ _ choice.policy.generated
    source.reference_generated).mp choice.policy.no_regression source.opponent source.history source.original metric

theorem both_actual_sources_pay_when_the_original_task_is_admissible
    (choice : Selection source.code source.reference) (generated : source.answer = .selected choice)
    (originalFeasible : source.code.feasible source.reference)
    (eligible : source.code.eligible (trace source.code source.reference source.history source.opponent) = true) :
    ServiceAdequate source.code.law ((source.withSide .original).actualExecution source.history.length).before
        source.code.task ((source.withSide .original).actualExecution source.history.length).submitted ∧
      ServiceAdequate source.code.law ((source.withSide .replacement).actualExecution source.history.length).before
        source.code.task ((source.withSide .replacement).actualExecution source.history.length).submitted := by
  have newEligible := no_loss_of_task_admissibility source.code choice.policy.policy source.reference
    choice.policy.generated source.reference_generated choice.policy.no_regression source.opponent source.history source.original eligible
  exact ⟨(source.withSide .original).actual_reaction_pays_the_original_task source.reference
      source.original_policy_is_emitted originalFeasible eligible,
    (source.withSide .replacement).actual_reaction_pays_the_original_task choice.policy.policy
      (source.selected_policy_is_emitted choice generated) choice.policy.feasible newEligible⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Machine
