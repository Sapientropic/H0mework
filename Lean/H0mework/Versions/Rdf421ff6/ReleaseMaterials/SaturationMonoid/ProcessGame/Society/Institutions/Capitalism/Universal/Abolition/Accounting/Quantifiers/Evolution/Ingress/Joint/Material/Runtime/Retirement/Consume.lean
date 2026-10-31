import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Allocation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Movement
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Instruction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem the_actual_matching_full_payment_retires_its_original_native_slot
    (before : (Epoch.Finance.process input depth count).GeneratedState)
    (obligation : AdmittedObligation (Epoch.Finance.vocabulary input depth count))
    (single : before.current.slots = [.live obligation])
    (item : Epoch.Finance.ActualItem input depth count) (holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation =
      .settle (obligation.content.instrument input depth count) (obligation.content.debtor input depth count) holder quantity)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request)
    (balance : obligation.residual = Finsupp.single holder quantity) :
    ∃ archive : TerminalArchive (Epoch.Finance.vocabulary input depth count),
      ((Epoch.Finance.consume input depth count item before).next input depth count).current.slots = [.terminal archive] ∧
      archive.obligation = obligation ∧
      before.current.history <+: ((Epoch.Finance.consume input depth count item before).next input depth count).current.history := by
  obtain ⟨movement,generated,_,amount⟩ := an_actual_payment_generates_its_original_movement
    input depth count item _ _ holder quantity operation accepted
  obtain ⟨receipt,review,_,payment,receiptQuantity⟩ := an_actual_matching_payment_generates_its_original_review
    input depth count obligation.content item holder quantity operation accepted
  have original : obligation.residual = Finsupp.single holder movement.quantity := by rw [amount]; exact balance
  obtain ⟨archive,terminal,identity⟩ := the_original_single_slot_allocator_generates_its_terminal_archive
    input depth count before obligation single item movement receipt review holder payment
      (receiptQuantity.trans amount.symm) original
  refine ⟨archive,?_,identity,(Epoch.Finance.consume input depth count item before).history_retained input depth count⟩
  have noClaim : Epoch.Finance.readNewClaim input depth count item = none := by
    unfold Epoch.Finance.readNewClaim
    split
    · rename_i observed
      cases operation.symm.trans observed
    · rfl
  unfold Epoch.Finance.consume
  rw [dif_neg (not_not_intro accepted)]
  split
  · rename_i fresh issued
    cases noClaim.symm.trans issued
  · rw [generated]
    exact terminal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement
