import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Events
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Invariants

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Source.ProgrammeFace

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

theorem NewClaim.quantity_nonnegative (claim : NewClaim input depth count) : 0 ≤ claim.quantity := by
  have guarded := claim.accepted.2.2.1
  simpa only [RawLaw.ClaimGuard, claim.operation] using guarded

def Review.toHolder {claim : Claim input depth count}
    (review : Review input depth count claim) : Party :=
  match review.kind with | .payment holder => holder | .assignment _ receiver => receiver

def Review.senderBirth {claim : Claim input depth count}
    (review : Review input depth count claim) :
    Interface.Actors.At input depth count review.origin.tag review.origin.visit (review.fromHolder input depth count) :=
  Interface.Actors.generate input depth count review.origin.tag review.origin.visit _
    (review.origin.participant_is_actual input depth count _ (by
      rw [review.operation]
      cases kind : review.kind <;> simp [reviewOperation, Review.fromHolder, kind, operationParties]))

def Review.receiverBirth {claim : Claim input depth count}
    (review : Review input depth count claim) :
    Interface.Actors.At input depth count review.origin.tag review.origin.visit (review.toHolder input depth count) :=
  Interface.Actors.generate input depth count review.origin.tag review.origin.visit _
    (review.origin.participant_is_actual input depth count _ (by
      rw [review.operation]
      cases kind : review.kind <;> simp [reviewOperation, Review.toHolder, kind, operationParties]))

theorem Review.quantity_nonnegative {claim : Claim input depth count}
    (review : Review input depth count claim) : 0 ≤ review.quantity := by
  have guard := review.accepted.2.2.1
  unfold RawLaw.ClaimGuard at guard
  rw [review.operation] at guard
  cases kind : review.kind <;> simp only [reviewOperation, kind] at guard <;> exact guard.1

theorem Review.after_nonnegative {claim : Claim input depth count}
    (review : Review input depth count claim) (balance : Financial.Balance input) (available : ℚ)
    (nonnegative : Financial.Nonnegative input balance) (funded : 0 ≤ available) :
    Financial.Nonnegative input (review.after input depth count balance available) := by
  have positive : 0 ≤ review.allocated input depth count balance available :=
    le_min funded (nonnegative _)
  have bounded : review.allocated input depth count balance available ≤
      balance (review.fromHolder input depth count) := min_le_right _ _
  cases kind : review.kind with
  | payment holder =>
      simp only [Review.after, kind]
      exact Financial.pay_nonnegative input balance holder _ nonnegative (by
        simpa only [Review.fromHolder, kind] using bounded)
  | assignment sender receiver =>
      simp only [Review.after, kind]
      exact Financial.assign_nonnegative input balance sender receiver _ nonnegative positive (by
        simpa only [Review.fromHolder, kind] using bounded)

theorem Event.after_nonnegative (event : Event input depth count)
    (lawful : event.Lawful input depth count) :
    Financial.Nonnegative input (event.after input depth count) := by
  cases event with
  | legacy original => exact Financial.Event.after_nonnegative input original lawful
  | birth claim =>
      intro party
      change 0 ≤ claimInitial input depth count (.inr claim) party
      rw [new_initial_balance_is_the_same_single]
      rw [Finsupp.single_apply]
      split
      · exact claim.quantity_nonnegative input depth count
      · exact le_refl _
  | review claim receipt balance remaining =>
      exact receipt.after_nonnegative input depth count balance remaining lawful.1 lawful.2.1

theorem old_loan_accepts_its_actual_epoch_payment
    (old : Financial.IssuedClaim input) (origin : ActualItem input depth count)
    (holder : Party) (quantity : ℚ)
    (operation : (origin.instruction input depth count).request.operation =
      .settle old.instrument old.debtor holder quantity)
    (accepted : (origin.interpreter input depth count).Valid (origin.instruction input depth count).before
      (origin.instruction input depth count).request) :
    ∃ receipt, readReview input depth count (.inl old) origin = some receipt ∧
      receipt.origin = origin ∧ receipt.kind = .payment holder ∧ receipt.quantity = quantity := by
  unfold readReview
  rw [dif_pos accepted]
  split <;> rename_i observed
  all_goals cases (operation.symm.trans observed)
  split
  · split
    · exact ⟨_, rfl, rfl, rfl, rfl⟩
    · contradiction
  · contradiction

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.old_loan_accepts_its_actual_epoch_payment
