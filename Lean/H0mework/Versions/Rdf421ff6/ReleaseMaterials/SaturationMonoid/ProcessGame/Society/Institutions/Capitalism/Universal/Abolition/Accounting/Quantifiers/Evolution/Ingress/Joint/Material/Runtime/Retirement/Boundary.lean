import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Receipt
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Invariants

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
  (obligation : AdmittedObligation (Epoch.Finance.vocabulary input depth count))
  (coherent : Epoch.Finance.Coherent input depth count obligation)
  (receipt : Epoch.Finance.Review input depth count obligation.content)
  (holder : Party) (quantity : ℚ) (payment : receipt.kind = .payment holder)
  (sameQuantity : receipt.quantity = quantity) (balance : obligation.residual = Finsupp.single holder quantity)

private theorem quantity_nonnegative (sameQuantity : receipt.quantity = quantity) : 0 ≤ quantity :=
  sameQuantity ▸ receipt.quantity_nonnegative input depth count

private theorem balance_nonnegative (sameQuantity : receipt.quantity = quantity)
    (balance : obligation.residual = Finsupp.single holder quantity) : Financial.Nonnegative input obligation.residual := by
  rw [balance]
  intro actor
  rw [Finsupp.single_apply]
  split
  · exact quantity_nonnegative input depth count obligation receipt quantity sameQuantity
  · exact le_refl _

def boundary : Epoch.Finance.Boundary input depth count obligation :=
  Epoch.Finance.reviewBoundary input depth count obligation coherent receipt quantity
    (balance_nonnegative input depth count obligation receipt holder quantity sameQuantity balance)
    (quantity_nonnegative input depth count obligation receipt quantity sameQuantity) (by rw [sameQuantity])

include payment in
theorem the_actual_full_payment_generates_the_original_terminal_archive :
    ∃ archive : TerminalArchive (Epoch.Finance.vocabulary input depth count),
      (Epoch.Finance.boundaryDisposition input depth count
        (boundary input depth count obligation coherent receipt holder quantity sameQuantity balance)).targetSlot = .terminal archive ∧
      archive.obligation = obligation ∧ archive.sourceEvent =
        (boundary input depth count obligation coherent receipt holder quantity sameQuantity balance).event := by
  have cleared : (boundary input depth count obligation coherent receipt holder quantity sameQuantity balance).event.after input depth count = 0 := by
    change receipt.after input depth count obligation.residual quantity = 0
    rw [balance]
    exact the_full_original_review_clears_the_single_share input depth count receipt holder quantity payment
  unfold Epoch.Finance.boundaryDisposition
  rw [dif_pos cleared]
  exact ⟨_,rfl,rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement
