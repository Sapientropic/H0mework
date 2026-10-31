import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Movement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem an_actual_payment_generates_its_original_movement
    (item : Epoch.Finance.ActualItem input depth count)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request) :
    ∃ movement, Epoch.Finance.readMovement input depth count item = some movement ∧
      movement.kind = .payment ∧ movement.quantity = quantity := by
  unfold Epoch.Finance.readMovement
  rw [dif_pos accepted]
  split
  · rename_i observed
    cases (operation.symm.trans observed)
    exact ⟨_,rfl,rfl,rfl⟩
  · rename_i observed
    cases (operation.symm.trans observed)
  · rename_i noPayment noAssignment
    exact (noPayment instrument debtor holder quantity operation).elim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement
