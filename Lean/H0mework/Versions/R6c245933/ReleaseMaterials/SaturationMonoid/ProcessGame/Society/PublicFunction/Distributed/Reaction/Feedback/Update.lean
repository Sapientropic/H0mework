import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Machine

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument)

/-- Override one cut without changing the earlier emitter history. -/
abbrev atFeedbackControlCut (index : Nat) (control : Option source.code.Policy) :
    Machine Party Good Port Technology Instrument :=
  {source with feedbackOverrides := source.feedbackOverrides ++ [(index, control)]}

theorem scheduled_control_is_used_at_its_own_cut (index : Nat) (control : Option source.code.Policy) :
    (source.atFeedbackControlCut index control).feedbackPolicy index = control := by
  simp [feedbackPolicy, atFeedbackControlCut, List.foldl_append]

theorem scheduled_control_does_not_change_other_cuts (index cut : Nat) (control : Option source.code.Policy)
    (different : cut ≠ index) :
    (source.atFeedbackControlCut index control).feedbackPolicy cut = source.feedbackPolicy cut := by
  unfold feedbackPolicy
  rw [show (source.atFeedbackControlCut index control).policy? = source.policy? from rfl]
  simp [atFeedbackControlCut, List.foldl_append, Ne.symm different]

theorem scheduled_control_keeps_the_entire_prior_state (input : Feedback.Input source.code)
    (index : Nat) (control : Option source.code.Policy) (count : Nat) (bounded : count ≤ index) :
    (source.atFeedbackControlCut index control).feedbackState input count = source.feedbackState input count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [feedbackState, source.scheduled_control_does_not_change_other_cuts index count control (by omega), ih (by omega)]
    rfl

abbrev atFeedbackCut (index : Nat) (policy : source.code.Policy) :
    Machine Party Good Port Technology Instrument :=
  {source with feedbackOverrides := source.feedbackOverrides ++ [(index, some policy)]}

theorem scheduled_policy_keeps_the_initial_program (index : Nat) (policy : source.code.Policy) :
    (source.atFeedbackCut index policy).policy? = source.policy? := rfl

theorem scheduled_policy_is_used_at_its_own_cut (index : Nat) (policy : source.code.Policy) :
    (source.atFeedbackCut index policy).feedbackPolicy index = some policy := by
  simp [feedbackPolicy, atFeedbackCut, List.foldl_append]

theorem scheduled_policy_does_not_change_other_cuts (index cut : Nat) (policy : source.code.Policy)
    (different : cut ≠ index) :
    (source.atFeedbackCut index policy).feedbackPolicy cut = source.feedbackPolicy cut := by
  unfold feedbackPolicy
  rw [source.scheduled_policy_keeps_the_initial_program]
  simp [atFeedbackCut, List.foldl_append, Ne.symm different]

theorem scheduled_policy_keeps_the_entire_prior_state (input : Feedback.Input source.code)
    (index : Nat) (policy : source.code.Policy) (count : Nat) (bounded : count ≤ index) :
    (source.atFeedbackCut index policy).feedbackState input count = source.feedbackState input count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [feedbackState, source.scheduled_policy_does_not_change_other_cuts index count policy (by omega),
        ih (by omega)]
      rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Machine
