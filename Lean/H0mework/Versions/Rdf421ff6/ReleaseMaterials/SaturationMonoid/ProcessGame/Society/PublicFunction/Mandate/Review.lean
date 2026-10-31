import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Response

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Review

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (current : RawCurrent Party Good (State Party Technology) Instrument)

/-- A review remains an attempted command when every current member lacks
its execution cost. The refusal is about these current one-step requests. -/
inductive Outcome where
  | private paid (actor : {actor // actor ∈ Delegation.members scope.task})
      (accepted : (law base scope).Valid current (request scope current actor.val .review))
  | private blocked (actor : {actor // actor ∈ Delegation.members scope.task})
      (refused : ∀ actor ∈ Delegation.members scope.task,
        ¬ (law base scope).Valid current (request scope current actor .review))

def produce : Outcome base scope current :=
  match found : (Delegation.members scope.task).find?
      (fun actor => decide ((law base scope).Valid current (request scope current actor .review))) with
  | some actor => .paid ⟨actor, List.mem_of_find?_eq_some found⟩
      (of_decide_eq_true (List.find?_some
        (p := fun actor => decide ((law base scope).Valid current (request scope current actor .review))) found))
  | none => .blocked (Response.firstMember scope) (by
      intro actor member valid
      have denied := List.find?_eq_none.mp found actor member
      simp [valid] at denied)

variable {base scope current}

def Outcome.actor : Outcome base scope current → {actor // actor ∈ Delegation.members scope.task}
  | .paid actor _ | .blocked actor _ => actor

def Outcome.word (outcome : Outcome base scope current) :=
  [request scope current outcome.actor.val .review]

def Outcome.report (outcome : Outcome base scope current) :
    ProgrammeSource.ProgrammeReport Party Good Port (State Party Technology) Instrument :=
  .original current outcome.word

theorem Outcome.actual_disposition (outcome : Outcome base scope current) :
    (law base scope).Valid current (request scope current outcome.actor.val .review) ∨
    (¬ (law base scope).Valid current (request scope current outcome.actor.val .review) ∧
      (law base scope).step current (request scope current outcome.actor.val .review) = current ∧
      ∀ actor ∈ Delegation.members scope.task,
        ¬ (law base scope).Valid current (request scope current actor .review)) := by
  rcases outcome with ⟨actor, accepted⟩ | ⟨actor, refused⟩
  · exact Or.inl accepted
  · exact Or.inr ⟨refused actor.val actor.property,
      (law base scope).rejected_preserves_current _ _ (refused actor.val actor.property), refused⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Review
