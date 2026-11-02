import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Actual
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeSource

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Response

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (current : RawCurrent Party Good (State Party Technology) Instrument)

def Active : Prop := current.technology.holder.isSome = true ∨ current.technology.offered.isSome = true

instance : Decidable (Active current) := inferInstanceAs (Decidable (_ ∨ _))

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] in
theorem members_nonempty : Delegation.members scope.task ≠ [] := by
  intro empty
  obtain ⟨slot, inside, _⟩ := scope.task.demand
  have member : slot.bearer ∈ Delegation.members scope.task := List.mem_map.mpr ⟨slot, inside, rfl⟩
  rw [empty] at member
  exact List.not_mem_nil member

def firstMember : {actor // actor ∈ Delegation.members scope.task} :=
  match members : Delegation.members scope.task with
  | [] => False.elim (members_nonempty scope members)
  | actor :: _rest => ⟨actor, List.mem_cons_self⟩

/-- Refusal covers exactly the original task's one-step revocation requests.
It is not a no-go for financing, multi-step words, or other tasks. -/
inductive Outcome where
  | private inactive (inactive : ¬ Active current)
  | private paid (actor : {actor // actor ∈ Delegation.members scope.task})
      (active : Active current)
      (accepted : (law base scope).Valid current (request scope current actor.val .revoke))
  | private blocked (actor : {actor // actor ∈ Delegation.members scope.task})
      (active : Active current)
      (refused : ∀ actor ∈ Delegation.members scope.task,
        ¬ (law base scope).Valid current (request scope current actor .revoke))

def produce : Outcome base scope current :=
  if active : Active current then
    match found : (Delegation.members scope.task).find?
        (fun actor => decide ((law base scope).Valid current (request scope current actor .revoke))) with
    | some actor => .paid ⟨actor, List.mem_of_find?_eq_some found⟩ active
        (of_decide_eq_true (List.find?_some
          (p := fun actor => decide ((law base scope).Valid current (request scope current actor .revoke))) found))
    | none => .blocked (firstMember scope) active (by
        intro actor member valid
        have denied := List.find?_eq_none.mp found actor member
        simp [valid] at denied)
  else .inactive active

variable {base scope current}

def Outcome.word : Outcome base scope current → RawEvent Party Good Port (State Party Technology) Instrument
  | .inactive _ => []
  | .paid actor _ _ | .blocked actor _ _ => [request scope current actor.val .revoke]

def Outcome.report (outcome : Outcome base scope current) :
    ProgrammeSource.ProgrammeReport Party Good Port (State Party Technology) Instrument :=
  .original current outcome.word

def Outcome.isBlocked : Outcome base scope current → Bool
  | .blocked .. => true
  | _ => false

omit [DecidableEq Instrument] in
theorem Outcome.blockage_covers_current_revocations (outcome : Outcome base scope current)
    (blocked : outcome.isBlocked = true) :
    ∀ actor ∈ Delegation.members scope.task,
      ¬ (law base scope).Valid current (request scope current actor .revoke) := by
  rcases outcome with ⟨inactive⟩ | ⟨actor, active, accepted⟩ | ⟨actor, active, refused⟩
  · cases blocked
  · cases blocked
  · exact refused

omit [DecidableEq Instrument] in
theorem Outcome.report_word (outcome : Outcome base scope current) : outcome.report.word = outcome.word := rfl

omit [DecidableEq Instrument] in
theorem Outcome.active_emits_an_actual_attempt (outcome : Outcome base scope current)
    (active : Active current) :
    ∃ actor ∈ Delegation.members scope.task, outcome.word = [request scope current actor .revoke] := by
  rcases outcome with ⟨inactive⟩ | ⟨actor, _, accepted⟩ | ⟨actor, _, refused⟩
  · exact False.elim (inactive active)
  · exact ⟨actor.val, actor.property, rfl⟩
  · exact ⟨actor.val, actor.property, rfl⟩

theorem Outcome.actual_disposition (outcome : Outcome base scope current) :
    (¬ Active current ∧ outcome.word = []) ∨
    (∃ actor ∈ Delegation.members scope.task,
      outcome.word = [request scope current actor .revoke] ∧
      (((law base scope).Valid current (request scope current actor .revoke) ∧
        ((law base scope).step current (request scope current actor .revoke)).technology.holder = none ∧
        ((law base scope).step current (request scope current actor .revoke)).claims = current.claims) ∨
      (¬ (law base scope).Valid current (request scope current actor .revoke) ∧
        (law base scope).step current (request scope current actor .revoke) = current ∧
        ∀ candidate ∈ Delegation.members scope.task,
          ¬ (law base scope).Valid current (request scope current candidate .revoke)))) := by
  rcases outcome with ⟨inactive⟩ | ⟨actor, active, accepted⟩ | ⟨actor, active, refused⟩
  · exact Or.inl ⟨inactive, rfl⟩
  · have effect := paid_command_effect base scope current actor.val .revoke accepted
    exact Or.inr ⟨actor.val, actor.property, rfl, Or.inl ⟨accepted, congrArg State.holder effect.1, effect.2⟩⟩
  · have denied := refused actor.val actor.property
    exact Or.inr ⟨actor.val, actor.property, rfl, Or.inr ⟨denied,
      (law base scope).rejected_preserves_current current _ denied, refused⟩⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Response
