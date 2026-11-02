import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Prefix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Quota
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Supported

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code)
  (cut : Nat) (position : Repayment.Position Party Instrument)

def account := Financial.accountAt source.input (source.history.length + 2 + cut)

def support : ℚ := Financial.BalanceConservation.ledgerClaims source.input (account source cut).current
  position.instrument position.debtor position.creditor

def amount := Repayment.Quota.quantity source.code.law position
  (source.feedbackState input cut).current (support source cut position)

def candidate := Repayment.Quota.candidate source.code.law position
  (source.feedbackState input cut).current (support source cut position)

def proposal := Repayment.Quota.generate source.code.law position
  (source.feedbackState input cut).current (support source cut position)

def emitted := if 0 < amount source input cut position then candidate source input cut position else []

def policy (site : Fin source.code.sites) : source.code.Policy := fun key member =>
  if key.1 = site then emitted source input cut position else
    match source.feedbackPolicy cut with | some prior => prior key member | none => []

abbrev planned (site : Fin source.code.sites) (_owner : source.code.siteParty site = position.debtor) :=
  source.atFeedbackCut cut (policy source input cut position site)

theorem amount_is_native_supported : amount source input cut position ≤ support source cut position :=
  Repayment.Quota.quantity_is_supported _ _ _ _ (by
    unfold support Financial.BalanceConservation.ledgerClaims
    apply List.sum_nonneg
    intro value member
    obtain ⟨slot, present, rfl⟩ := List.mem_map.mp member
    exact Financial.BalanceConservation.slotClaims_nonnegative source.input (account source cut)
      slot present _ _ _)

theorem plan_keeps_the_complete_current_cut (site : Fin source.code.sites)
    (owner : source.code.siteParty site = position.debtor) :
    (planned source input cut position site owner).feedbackState input cut = source.feedbackState input cut :=
  source.scheduled_policy_keeps_the_entire_prior_state input cut _ cut (Nat.le_refl _)

theorem actual_activation_submits_the_generated_candidate
    (active : source.feedback? = some input) (empty : source.continuation = [])
    (site : Fin source.code.sites) (owner : source.code.siteParty site = position.debtor)
    (move : Choice source.code) (activation : move.val = .activate site)
    (chosen : decision source.code input (source.feedbackState input cut) = some move) :
    ((planned source input cut position site owner).actualExecution (source.history.length + 1 + cut)).submitted =
      if source.code.memoryReady ((source.feedbackState input cut).frame.inbox site) then
        emitted source input cut position else [] := by
  rw [(planned source input cut position site owner).feedback_word_is_actual input active empty,
    plan_keeps_the_complete_current_cut, Machine.scheduled_policy_is_used_at_its_own_cut]
  simp only [word, chosen, stepLocal, activation, Code.step, policy, Code.action,
    List.nil_append]
  simp

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota
