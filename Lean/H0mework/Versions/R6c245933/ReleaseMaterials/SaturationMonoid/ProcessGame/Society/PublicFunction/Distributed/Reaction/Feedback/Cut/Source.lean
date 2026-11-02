import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Quantified

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code) (cut : Nat)

def Realization : Outcome source input cut (baseline source input cut) → Type
  | .selected choice => (rival : Opponent source.code) → Future.Execution source input cut rival choice.policy.term.val
  | .blocked _ => Unit

structure Disposition where
  outcome : Outcome source input cut (baseline source input cut)
  generated : outcome = compile source input cut (baseline source input cut)
  realization : Realization source input cut outcome

variable (active : source.feedback? = some input) (empty : source.continuation = [])

def AnswerSound : Outcome source input cut (baseline source input cut) → Prop
  | .selected choice => FeasibleAgainstEveryOpponent source input cut choice.policy.term ∧
      AgainstEveryOpponent source input cut choice.policy.term (baseline source input cut) ∧
      verify source input cut (baseline source input cut) choice.policy.term = true ∧
      ∀ other : Term source input cut, FeasibleAgainstEveryOpponent source input cut other →
        ¬ StrictAgainstEveryOpponent source input cut choice.policy.term other
  | .blocked rejected => ∀ term, (rejected term).row ∈ rows source input cut ∧
      ¬ Holds source input cut (baseline source input cut) term (rejected term).row

include active empty in
theorem answer_sound (outcome : Outcome source input cut (baseline source input cut)) :
    AnswerSound source input cut outcome := by
  cases outcome with
  | selected choice =>
    exact ⟨(feasibility_iff_every_future_opponent source input cut active empty _).mp choice.policy.feasible,
      selected_protects_every_actual_future_opponent source input cut active empty _ choice,
      independent_replay_accepts_selection source input cut _ choice,
      selected_has_no_feasible_dominator_under_all_future_opponents source input cut active empty _ choice⟩
  | blocked rejected => exact fun term => ⟨(rejected term).original, (rejected term).broken⟩

include active empty in
def generate : Disposition source input cut where
  outcome := compile source input cut (baseline source input cut)
  generated := rfl
  realization := match compile source input cut (baseline source input cut) with
    | .selected choice => fun rival => Future.execute source input cut rival choice.policy.term.val active empty
    | .blocked _ => ()

def selectionFrom (result : Outcome source input cut (baseline source input cut))
    (feasible : Feasible source input cut (baseline source input cut)) : Selection source input cut (baseline source input cut) :=
  match result with
  | .selected choice => choice
  | .blocked rejected => False.elim (feasible_original_cannot_be_blocked source input cut _ feasible rejected)

def selectedExecution (result : Disposition source input cut)
    (feasible : Feasible source input cut (baseline source input cut)) (rival : Opponent source.code) :
    Future.Execution source input cut rival (selectionFrom source input cut result.outcome feasible).policy.term.val := by
  rcases result with ⟨outcome, generated, realization⟩
  cases outcome with
  | selected choice => exact realization rival
  | blocked rejected => exact False.elim (feasible_original_cannot_be_blocked source input cut _ feasible rejected)

def selection (feasible : Feasible source input cut (baseline source input cut)) : Selection source input cut (baseline source input cut) :=
  selectionFrom source input cut (compile source input cut (baseline source input cut)) feasible

abbrev replacement (feasible : Feasible source input cut (baseline source input cut)) :=
  machine source input cut input.opponent (selection source input cut feasible).policy.term

abbrev replacementInput := Future.takeover source input cut input.opponent

include active empty in
theorem selected_actual_source_protects_the_original_holders
    (feasible : Feasible source input cut (baseline source input cut)) (index : Nat)
    (inside : index < originalSlots source cut) (holder : Party) :
    received source input cut input.opponent (baseline source input cut) index holder ≤
      received source input cut input.opponent (selection source input cut feasible).policy.term index holder :=
  selected_protects_every_original_holders_actual_receipts source input cut active empty _
    (selection source input cut feasible) input.opponent index inside holder

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut
