import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Selection.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Selection

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat) (active : bound.source.feedback? = some input)

variable (empty : bound.source.continuation = [])

def AnswerSound (reference : Term bound input cut) : Outcome bound input cut active reference → Prop
  | .selected choice => Cut.FeasibleAgainstEveryOpponent bound.source input cut choice.policy.term ∧
      AgainstEveryOpponent bound input cut active choice.policy.term reference ∧
      verify bound input cut active reference choice.policy.term = true ∧
      (∀ other : Term bound input cut, Cut.FeasibleAgainstEveryOpponent bound.source input cut other →
        ¬ (AgainstEveryOpponent bound input cut active other choice.policy.term ∧
          ¬ BenefitAgainstEveryOpponent bound input cut active choice.policy.term other)) ∧
      ((∃ other : Term bound input cut, Cut.FeasibleAgainstEveryOpponent bound.source input cut other ∧
        AgainstEveryOpponent bound input cut active other reference ∧
          ¬ BenefitAgainstEveryOpponent bound input cut active reference other) →
        AgainstEveryOpponent bound input cut active choice.policy.term reference ∧
          ¬ BenefitAgainstEveryOpponent bound input cut active reference choice.policy.term)
  | .blocked rejected => ∀ term, (rejected term).row ∈ rows bound input cut ∧
      ¬ Holds bound input cut active reference term (rejected term).row

include empty in
theorem answer_sound (reference : Term bound input cut) (outcome : Outcome bound input cut active reference) :
    AnswerSound bound input cut active reference outcome := by
  cases outcome with
  | selected choice =>
    obtain ⟨feasible, bounded, maximal⟩ := selected_is_nondominated_against_every_future_opponent bound input cut active empty reference choice
    exact ⟨feasible, bounded, independent_replay_accepts_selection bound input cut active reference choice, maximal,
      every_future_improvement_is_realized bound input cut active empty reference choice⟩
  | blocked rejected => exact fun term => ⟨(rejected term).original, (rejected term).broken⟩

def Realization (reference : Term bound input cut) : Outcome bound input cut active reference → Type
  | .selected choice => (rival : Opponent bound.source.code) → Future.Execution bound.source input cut rival choice.policy.term.val
  | .blocked _ => Unit

structure Disposition (reference : Term bound input cut) where
  outcome : Outcome bound input cut active reference
  generated : outcome = compile bound input cut active reference
  realization : Realization bound input cut active reference outcome
  verified_realization : (term : Term bound input cut) → verify bound input cut active reference term = true →
    (rival : Opponent bound.source.code) → Future.Execution bound.source input cut rival term.val

include empty in
def generateSelection (reference : Term bound input cut) : Disposition bound input cut active reference where
  outcome := compile bound input cut active reference
  generated := rfl
  realization := match compile bound input cut active reference with
    | .selected choice => fun rival => Future.execute bound.source input cut rival choice.policy.term.val active empty
    | .blocked _ => ()
  verified_realization := fun term _ rival => Future.execute bound.source input cut rival term.val active empty

def choiceFrom (reference : Term bound input cut) (result : Outcome bound input cut active reference)
    (feasible : Cut.Feasible bound.source input cut reference) : Choice bound input cut active reference :=
  match result with
  | .selected choice => choice
  | .blocked rejected => False.elim (feasible_original_cannot_be_blocked bound input cut active reference feasible rejected)

def selectedExecution (reference : Term bound input cut) (result : Disposition bound input cut active reference)
    (feasible : Cut.Feasible bound.source input cut reference) (rival : Opponent bound.source.code) :
    Future.Execution bound.source input cut rival (choiceFrom bound input cut active reference result.outcome feasible).policy.term.val := by
  rcases result with ⟨outcome, generated, realization, _⟩
  cases outcome with
  | selected choice => exact realization rival
  | blocked rejected => exact False.elim (feasible_original_cannot_be_blocked bound input cut active reference feasible rejected)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Selection
