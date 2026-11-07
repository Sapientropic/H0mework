import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Lifecycle
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Review

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat)

theorem Review.after_nonnegative {claim : Claim sources depths counts}
    (review : Review sources depths counts claim) (before : Balance (Party := Party)) (cap : ℚ)
    (positive : ∀ holder, 0 ≤ before holder) (funded : 0 ≤ cap) :
    ∀ holder, 0 ≤ review.after sources depths counts before cap holder := by
  have used := le_min funded (positive review.movement.sender)
  have bounded : min cap (before review.movement.sender) ≤ before review.movement.sender := min_le_right _ _
  cases kind : review.movement.kind with
  | payment =>
      simp only [Review.after, kind]
      exact Financial.pay_nonnegative (sources claim.1) before review.movement.sender _ positive bounded
  | assignment =>
      simp only [Review.after, kind]
      exact Financial.assign_nonnegative (sources claim.1) before review.movement.sender review.movement.receiver _
        positive used bounded

theorem Event.after_nonnegative (event : Event sources depths counts)
    (lawful : event.Lawful sources depths counts) :
    ∀ holder, 0 ≤ event.after sources depths counts holder := by
  cases event with
  | original index old =>
      exact Finance.Event.after_nonnegative (sources index) (depths index) (counts index) old lawful
  | review claim receipt before cap =>
      exact receipt.after_nonnegative sources depths counts before cap lawful.1 lawful.2.1

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family
