import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Invariants
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Migration

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

/-- Retirement is read from the original event, including its original
payment quota. An assignment never counts as a second payment. -/
def actualPaid : Epoch.Finance.Event input depth count → ℚ
  | .legacy original => Financial.Migration.retired input original
  | .birth _ => 0
  | .review _ receipt balance available => match receipt.kind with
      | .payment _ => receipt.allocated input depth count balance available
      | .assignment .. => 0

theorem every_original_event_accounts_for_principal_and_real_payment
    (event : Epoch.Finance.Event input depth count) :
    Financial.total input (event.after input depth count) + actualPaid input depth count event =
      Financial.total input (event.before input depth count) := by
  cases event with
  | legacy original => exact Financial.Migration.event_conservation input original
  | birth => simp only [Epoch.Finance.Event.after,Epoch.Finance.Event.before,actualPaid,add_zero]
  | review claim receipt balance available =>
      cases kind : receipt.kind <;>
        simp only [Epoch.Finance.Event.after,Epoch.Finance.Event.before,actualPaid,
          Epoch.Finance.Review.after,kind,Financial.pay_total,Financial.assign_total] <;> ring

theorem a_lawful_actual_payment_is_nonnegative
    (event : Epoch.Finance.Event input depth count) (lawful : event.Lawful input depth count) :
    0 ≤ actualPaid input depth count event := by
  cases event with
  | legacy original => exact Financial.Migration.retired_nonnegative input original lawful
  | birth => exact le_rfl
  | review claim receipt balance available =>
      cases kind : receipt.kind with
      | payment holder =>
          simp only [actualPaid,kind,Epoch.Finance.Review.allocated]
          exact le_min lawful.2.1 (lawful.1 _)
      | assignment => simp only [actualPaid,kind,le_refl]

theorem an_actual_boundary_cannot_refill_its_original_principal
    (obligation : AdmittedObligation (Epoch.Finance.vocabulary input depth count))
    (boundary : Epoch.Finance.Boundary input depth count obligation) :
    Financial.total input (Epoch.Finance.slotBalance input depth count
      (Epoch.Finance.boundaryDisposition input depth count boundary).targetSlot) +
        actualPaid input depth count boundary.event = Financial.total input obligation.residual := by
  rw [Epoch.Finance.boundary_balance]
  exact (every_original_event_accounts_for_principal_and_real_payment input depth count boundary.event).trans
    (congrArg (Financial.total input) boundary.before_eq.symm)

theorem every_original_admission_has_its_source_quantity
    (claim : Epoch.Finance.Claim input depth count) :
    Financial.total input (Epoch.Finance.admission input depth count claim).toObligation.residual =
      claim.quantity input depth count := by
  cases claim with
  | inl original => exact Financial.initial_total input original
  | inr actual =>
      change Financial.total input (Epoch.Finance.claimInitial input depth count (.inr actual)) = actual.quantity
      rw [Epoch.Finance.new_initial_balance_is_the_same_single]
      simp [Financial.total]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution
