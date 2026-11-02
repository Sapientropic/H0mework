import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

def AgainstEveryOpponent (new old : code.Policy) : Prop :=
  ∀ opponent : Opponent code, ∀ history ∈ code.histories, ∀ metric : Metric Party Good Instrument,
    payoff code new history opponent metric ≤ payoff code old history opponent metric

def StrictAgainstEveryOpponent (old new : code.Policy) : Prop :=
  AgainstEveryOpponent code new old ∧ ¬ AgainstEveryOpponent code old new

/-- Finite selection quantifies over all history-adaptive opponent functions,
with exactly the same function on both feedback-dependent paths. -/
theorem finite_comparison_iff_every_same_opponent (new old : code.Policy)
    (newGenerated : new ∈ code.policies) (oldGenerated : old ∈ code.policies) :
    NonRegression code new old ↔ AgainstEveryOpponent code new old := by
  constructor
  · intro bounded opponent history original metric
    obtain ⟨table, generated, same⟩ := every_history_adaptive_opponent_has_one_joint_table code opponent
    have inside : (history, table, metric) ∈ axes code :=
      List.mem_product.mpr ⟨original, List.mem_product.mpr ⟨generated, all_metrics_are_present code metric⟩⟩
    have checked := bounded (history, table, metric) inside
    change payoff code new history (respond code table) metric ≤ payoff code old history (respond code table) metric at checked
    simpa only [payoff, same new newGenerated history original, same old oldGenerated history original] using checked
  · intro bounded axis inside
    have original := (List.mem_product.mp inside).1
    exact bounded (respond code axis.2.1) axis.1 original axis.2.2

theorem finite_strictness_iff_every_same_opponent (old new : code.Policy)
    (oldGenerated : old ∈ code.policies) (newGenerated : new ∈ code.policies) :
    Better code old new ↔ StrictAgainstEveryOpponent code old new := by
  exact and_congr (finite_comparison_iff_every_same_opponent code new old newGenerated oldGenerated)
    (not_congr (finite_comparison_iff_every_same_opponent code old new oldGenerated newGenerated))

theorem selected_is_nondominated_against_all_history_adaptive_opponents
    (reference : code.Policy) (choice : Selection code reference)
    (other : code.Policy) (generated : other ∈ code.policies) (feasible : code.feasible other) :
    ¬ StrictAgainstEveryOpponent code choice.policy.policy other := by
  intro improves
  exact selected_has_no_feasible_dominator code reference choice other generated feasible
    ((finite_strictness_iff_every_same_opponent code _ _ choice.policy.generated generated).mpr improves)

theorem any_universal_improvement_is_actually_selected (reference : code.Policy)
    (original : reference ∈ code.policies) (choice : Selection code reference)
    (available : ∃ policy ∈ code.policies, code.feasible policy ∧ StrictAgainstEveryOpponent code reference policy) :
    StrictAgainstEveryOpponent code reference choice.policy.policy := by
  apply (finite_strictness_iff_every_same_opponent code _ _ original choice.policy.generated).mp
  apply every_available_improvement_is_realized code reference choice
  obtain ⟨policy, generated, feasible, improves⟩ := available
  exact ⟨policy, generated, feasible,
    (finite_strictness_iff_every_same_opponent code _ _ original generated).mpr improves⟩

theorem no_loss_of_task_admissibility (new old : code.Policy)
    (newGenerated : new ∈ code.policies) (oldGenerated : old ∈ code.policies)
    (bounded : NonRegression code new old) (opponent : Opponent code)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (original : history ∈ code.histories)
    (oldEligible : code.eligible (trace code old history opponent) = true) :
    code.eligible (trace code new history opponent) = true := by
  have compared := (finite_comparison_iff_every_same_opponent code new old newGenerated oldGenerated).mp
    bounded opponent history original .admissibility
  simp only [payoff, oldEligible, if_true] at compared
  split at compared
  next => assumption
  next => norm_num at compared

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction
