import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Review

/-! A finite decoder extracts four paid openings from one actual word.
The certificate retains the accepted Grant, independent signature and
holder-signed exit before the later review, all with original item indices. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (fresh : Handoff.Ready bound inputs)
  (before : Current) (word : List Action)

structure PaidOpening where
  private mk ::
  grant : Mandate.Grant base fresh.scope before word
  grant_actual : grant ∈ Mandate.grantsAt base fresh.scope before word
  withdrawal : Mandate.ActualCommand base fresh.scope before word
  withdrawal_actual : withdrawal ∈ Mandate.commandsAt base fresh.scope before word
  withdrawal_kind : withdrawal.command = .exit
  withdrawal_signed : withdrawal.item.val.request.signer = grant.candidate
  review : Mandate.ActualCommand base fresh.scope before word
  review_actual : review ∈ Mandate.commandsAt base fresh.scope before word
  review_kind : review.command = .review
  exit_before_review : withdrawal.item.val.index < review.item.val.index
  challenge : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  challenge_actual : challenge ∈ (Mandate.law base fresh.scope).rawItems before word
  challenge_signed : Mandate.Challenge.Submission (scope := fresh.scope) challenge.request
  challenge_paid : (Mandate.law base fresh.scope).Valid challenge.before challenge.request
  challenge_holder : challenge.before.technology.holder = some grant.candidate
  independent : challenge.request.signer ≠ grant.candidate
  admission_before_challenge : grant.acceptance.item.val.index < challenge.index
  challenge_before_exit : challenge.index < withdrawal.item.val.index

def paidOpenings : List (PaidOpening fresh before word) :=
  (Mandate.grantsAt base fresh.scope before word).attach.flatMap fun grant =>
    (Mandate.commandsAt base fresh.scope before word).attach.flatMap fun withdrawal =>
      if correctExit : withdrawal.val.command = .exit ∧ withdrawal.val.item.val.request.signer = grant.val.candidate then
        (Mandate.commandsAt base fresh.scope before word).attach.flatMap fun review =>
          if correctReview : review.val.command = .review ∧ withdrawal.val.item.val.index < review.val.item.val.index then
            ((Mandate.law base fresh.scope).rawItems before word).attach.filterMap fun item =>
              if signed : Mandate.Challenge.Submission (scope := fresh.scope) item.val.request then
                if paid : (Mandate.law base fresh.scope).Valid item.val.before item.val.request then
                  if ordered : item.val.before.technology.holder = some grant.val.candidate ∧
                      item.val.request.signer ≠ grant.val.candidate ∧
                      grant.val.acceptance.item.val.index < item.val.index ∧ item.val.index < withdrawal.val.item.val.index then
                    some ⟨grant.val,grant.property,withdrawal.val,withdrawal.property,correctExit.1,correctExit.2,
                      review.val,review.property,correctReview.1,correctReview.2,
                      item.val,item.property,signed,paid,ordered.1,ordered.2.1,ordered.2.2.1,ordered.2.2.2⟩
                  else none
                else none
              else none
          else []
      else []

def decodePaidOpening := (paidOpenings fresh before word).head?

variable {fresh before word}
def PaidOpening.appendRight (opening : PaidOpening fresh before word) (suffix : List Action) :
    PaidOpening fresh before (word ++ suffix) :=
  ⟨opening.grant.appendRight suffix,(opening.grant.appendRight suffix).is_enumerated,
    opening.withdrawal.appendRight suffix,(opening.withdrawal.appendRight suffix).is_enumerated,
    opening.withdrawal_kind,opening.withdrawal_signed,
    opening.review.appendRight suffix,(opening.review.appendRight suffix).is_enumerated,
    opening.review_kind,opening.exit_before_review,
    opening.challenge,(by
      unfold RawLaw.rawItems
      rw [(Mandate.law base fresh.scope).execute_append]
      exact List.mem_append_left _ opening.challenge_actual),
    opening.challenge_signed,opening.challenge_paid,opening.challenge_holder,opening.independent,
    opening.admission_before_challenge,opening.challenge_before_exit⟩

theorem PaidOpening.is_enumerated (opening : PaidOpening fresh before word) :
    opening ∈ paidOpenings fresh before word := by
  unfold paidOpenings
  apply List.mem_flatMap.mpr
  refine ⟨⟨opening.grant,opening.grant_actual⟩,by simp,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨opening.withdrawal,opening.withdrawal_actual⟩,by simp,?_⟩
  simp only [dif_pos (And.intro opening.withdrawal_kind opening.withdrawal_signed)]
  apply List.mem_flatMap.mpr
  refine ⟨⟨opening.review,opening.review_actual⟩,by simp,?_⟩
  simp only [dif_pos (And.intro opening.review_kind opening.exit_before_review)]
  apply List.mem_filterMap.mpr
  refine ⟨⟨opening.challenge,opening.challenge_actual⟩,by simp,?_⟩
  simp only [dif_pos opening.challenge_signed,dif_pos opening.challenge_paid,
    dif_pos (And.intro opening.challenge_holder (And.intro opening.independent
      (And.intro opening.admission_before_challenge opening.challenge_before_exit)))]

theorem PaidOpening.decoder_succeeds (opening : PaidOpening fresh before word) :
    (decodePaidOpening fresh before word).isSome = true := by
  have member := opening.is_enumerated
  cases listed : paidOpenings fresh before word with
  | nil => simp only [listed,List.not_mem_nil] at member
  | cons head tail => simp only [decodePaidOpening,listed,List.head?_cons,Option.isSome_some]

theorem PaidOpening.withdrawal_is_the_actual_holders_own_exit (opening : PaidOpening fresh before word) :
    opening.withdrawal.item.val.before.technology.holder = some opening.grant.candidate ∧
    opening.withdrawal.after.technology.holder = none ∧ opening.withdrawal.after.technology.offered = none := by
  have own := opening.withdrawal.authorization.2.2.2.2.2
  rw [opening.withdrawal_kind] at own
  have effect := opening.withdrawal.actual_effect.1
  rw [opening.withdrawal_kind] at effect
  refine ⟨?_,?_,?_⟩
  · simpa only [Mandate.CanRun,opening.withdrawal_signed] using own
  · rw [effect]; rfl
  · rw [effect]; rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
