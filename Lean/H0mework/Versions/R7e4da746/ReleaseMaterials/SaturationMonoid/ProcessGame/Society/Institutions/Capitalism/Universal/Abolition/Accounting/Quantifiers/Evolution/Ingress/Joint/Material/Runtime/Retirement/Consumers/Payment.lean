import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Consumers.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Tail

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Consumers

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Quantifiers.Joint

noncomputable section

theorem the_actual_original_settlement_tail_retires_its_same_native_slot :
    ∃ (obligation : AdmittedObligation (Epoch.Finance.vocabulary Original.input 0 19))
      (archive : TerminalArchive (Epoch.Finance.vocabulary Original.input 0 19)),
      (Execution.Selected.before Original.seed).current.slots = [.live obligation] ∧
      (Execution.Selected.after Original.seed Original.grossClaim).current.slots = [.terminal archive] ∧
      archive.obligation = obligation ∧ obligation.residual = Finsupp.single true 1 ∧
      (Execution.Selected.before Original.seed).current.history <+:
        (Execution.Selected.after Original.seed Original.grossClaim).current.history := by
  obtain ⟨obligation,single,balance,debtor⟩ :=
    the_original_live_slot_is_generated_from_the_retained_native_account
  have original : (Execution.Selected.items Original.seed Original.grossClaim).map
      (fun item => (item.instruction Original.seed.input Original.seed.depth Original.seed.count).request) =
        Planning.Menu.materialPlan Original.seed Original.grossClaim
          Quantifiers.Joint.Consumers.Compact.shared true () ++ [Execution.Consumers.originalSettlement] := by
    rw [Execution.Selected.every_actual_requested_instruction_is_the_same_selected_instruction Original.seed Original.grossClaim]
    rw [Execution.Consumers.the_selected_source_word_is_the_original_funded_plan]
    change Planning.Menu.materialPlan Original.seed Original.grossClaim
      Quantifiers.Joint.Consumers.Compact.shared true () ++ Settlement.word Original.seed = _
    rw [Quantifiers.Joint.Consumers.Compact.original_financial_tail]
    rfl
  have instrument : obligation.content.instrument Original.input 0 19 = () := Subsingleton.elim _ _
  have operation : Execution.Consumers.originalSettlement.operation =
      .settle (obligation.content.instrument Original.input 0 19)
        (obligation.content.debtor Original.input 0 19) true 1 := by
    rw [instrument,debtor]
    rfl
  obtain ⟨archive,terminal,identity,history⟩ :=
    the_actual_material_and_financial_tail_retires_its_original_native_slot
      Original.seed.input Original.seed.depth Original.seed.count (Execution.Selected.tag Original.seed Original.grossClaim)
        (Execution.Selected.visit Original.seed Original.grossClaim)
        (Execution.Selected.before Original.seed) obligation single _ Execution.Consumers.originalSettlement true 1
        operation original the_original_material_prefix_is_nonfinancial
        (Execution.Selected.no_actual_item_is_rejected_by_its_native_financial_interpreter Original.seed Original.grossClaim)
        balance
  exact ⟨obligation,archive,single,terminal,identity,balance,history⟩

theorem actual_retirement_keeps_the_original_address_and_archive :
    ∃ archive : TerminalArchive (Epoch.Finance.vocabulary Original.input 0 19),
      (Execution.Selected.after Original.seed Original.grossClaim).current.slots = [.terminal archive] ∧
      (Epoch.Finance.slotBalance Original.input 0 19 (.terminal archive)) = 0 ∧
      archive.obligation.residual = Finsupp.single true 1 := by
  obtain ⟨obligation,archive,_,terminal,identity,balance,_⟩ :=
    the_actual_original_settlement_tail_retires_its_same_native_slot
  refine ⟨archive,terminal,rfl,?_⟩
  rw [identity]
  exact balance

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Consumers
