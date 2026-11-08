import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Review.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency

open Capitalism.Universal.Source.Program
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Base" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)

private theorem tail_keeps_authority_and_claims (base : Base) (scope : J)
    (cut : Raw) (index : Nat) (word : Word) (safe : LocalTail word) :
    ((law base scope).execute cut index word).final.technology = cut.technology ∧
      ((law base scope).execute cut index word).final.claims = cut.claims := by
  induction word generalizing cut index with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    have keep := safe head List.mem_cons_self
    have headEffect : ((law base scope).step cut head).technology = cut.technology ∧
        ((law base scope).step cut head).claims = cut.claims := by
      unfold RawLaw.step
      split
      · cases operation : head.operation <;>
          simp_all only [KeepsReview, RawLaw.paidStep, RawLaw.nextClaims, and_self]
      · exact ⟨rfl, rfl⟩
    have rest := ih ((law base scope).step cut head) (index + 1)
      (fun req member => safe req (List.mem_cons_of_mem _ member))
    exact ⟨rest.1.trans headEffect.1, rest.2.trans headEffect.2⟩

/-- The raw route verifies both actual original payments at their own stocks
and the effect of the expired release. -/
structure RawReview (base : Base) (scope : J) (cut : Raw) (first second : Party) (tail : Word) : Prop where
  firstCost :
    let head := request scope cut first .review
    ((law base scope).step cut head).stock first =
      fun good => cut.stock first good - amount Good scope.revisionCost good
  secondCost :
    let head := request scope cut first .review
    let middle := (law base scope).step cut head
    let independent := request scope middle second .review
    ((law base scope).step middle independent).stock second =
      fun good => middle.stock second good - amount Good scope.revisionCost good
  members : first ∈ PublicFunction.Delegation.members scope.task ∧ second ∈ PublicFunction.Delegation.members scope.task
  released :
    let final := ((law base scope).execute cut 0 (reviewPair base scope cut first second ++ tail)).final
    final.technology.holder = none ∧ final.technology.offered = none ∧ final.claims = cut.claims

theorem raw_review (base : Base) (scope : J) (cut : Raw) (first second : Party) {tail : Word}
    (late : scope.task.deadline < cut.clock) (safe : LocalTail tail)
    (firstAccepted : (law base scope).Valid cut (request scope cut first .review))
    (secondAccepted : (law base scope).Valid
      ((law base scope).step cut (request scope cut first .review))
      (request scope ((law base scope).step cut (request scope cut first .review)) second .review)) :
    RawReview base scope cut first second tail := by
  let head := request scope cut first .review
  let middle := (law base scope).step cut head
  let independent := request scope middle second .review
  let after := (law base scope).step middle independent
  have clock : middle.clock = cut.clock := by
    change ((law base scope).step cut head).clock = _
    unfold RawLaw.step
    split <;> rfl
  have firstEffect := paid_command_effect base scope cut first .review firstAccepted
  have secondEffect := paid_command_effect base scope middle second .review secondAccepted
  have closed : after.technology.holder = none ∧ after.technology.offered = none := by
    change ((law base scope).step middle independent).technology.holder = none ∧
      ((law base scope).step middle independent).technology.offered = none
    rw [secondEffect.1, advance, if_pos (clock.symm ▸ late)]
    exact ⟨rfl, rfl⟩
  have rest := tail_keeps_authority_and_claims base scope after 2 tail safe
  constructor
  · funext good
    apply eq_sub_of_add_eq
    rw [← flow_at_own_address scope.revisionCost first good]
    exact review_cost_at_original_address base scope cut first firstAccepted first good
  · funext good
    apply eq_sub_of_add_eq
    rw [← flow_at_own_address scope.revisionCost second good]
    exact review_cost_at_original_address base scope middle second secondAccepted second good
  · exact ⟨(command_policy base scope cut first .review).mp firstAccepted.1.2,
      (command_policy base scope middle second .review).mp secondAccepted.1.2⟩
  · change (((law base scope).execute after 2 tail).final.technology.holder = none) ∧
      (((law base scope).execute after 2 tail).final.technology.offered = none) ∧
      ((law base scope).execute after 2 tail).final.claims = cut.claims
    rw [rest.1, rest.2]
    exact ⟨closed.1, closed.2, secondEffect.2.trans firstEffect.2⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency
