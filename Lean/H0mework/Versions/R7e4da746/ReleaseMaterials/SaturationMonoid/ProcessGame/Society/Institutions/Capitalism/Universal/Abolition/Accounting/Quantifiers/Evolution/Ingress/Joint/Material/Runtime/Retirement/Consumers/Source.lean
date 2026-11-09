import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Consumers.Payment

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Consumers

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Quantifiers.Joint

noncomputable section

namespace Original
export Execution.Consumers.Fixture (seed grossClaim input)
end Original

theorem the_original_live_slot_is_generated_from_the_retained_native_account :
    ∃ obligation : AdmittedObligation (Epoch.Finance.vocabulary Original.input 0 19),
      (Execution.Selected.before Original.seed).current.slots = [.live obligation] ∧
      obligation.residual = Finsupp.single true 1 ∧
      obligation.content.debtor Original.input 0 19 = false := by
  have inherited := (Epoch.Finance.Legacy.every_slot_and_history_entry_is_retained
    Original.input 0 19 (Background.account Original.seed)).1
  change (Execution.Selected.before Original.seed).current.slots = _ at inherited
  rw [Quantifiers.Joint.Consumers.Compact.live_native_account,
    Quantifiers.Joint.Consumers.Compact.original_slots] at inherited
  have balance := Quantifiers.Joint.Consumers.Compact.original_balance
  have debtor := Quantifiers.Joint.Consumers.Compact.original_debtor
  cases original : Quantifiers.Joint.Consumers.Compact.originalSlot with
  | live obligation =>
      rw [original] at inherited balance debtor
      exact ⟨Epoch.Finance.Legacy.obligation Original.input 0 19 obligation,inherited,balance,debtor⟩
  | terminal archive =>
      rw [original] at balance
      have impossible := congrArg (fun quantity : Financial.Balance Original.input => quantity true) balance
      have contradiction : (0 : ℚ) = 1 := by
        simpa only [Financial.slotBalance,Finsupp.zero_apply,Finsupp.single_eq_same] using impossible
      exact (zero_ne_one contradiction).elim

theorem the_original_material_prefix_is_nonfinancial :
    ∀ request ∈ Planning.Menu.materialPlan Original.seed Original.grossClaim
      Quantifiers.Joint.Consumers.Compact.shared true (),
      Responsibility.NonFinancialOperation request.operation := by
  unfold Planning.Menu.materialPlan
  split
  · exact Planning.Menu.current_need_bills_are_nonfinancial _ _ _
  · apply Planning.Menu.productive_repairs_preserve_the_original_nonfinancial_prefix
    apply Planning.Menu.gross_refunds_preserve_the_original_nonfinancial_prefix
    intro request inside
    rcases List.mem_append.mp inside with funded | needed
    · exact Planning.Menu.funding_preserves_the_original_nonfinancial_prefix _ _ _ true _ _
        (Planning.Menu.current_production_is_nonfinancial _ _ _ true ()) request funded
    · exact Planning.Menu.current_need_bills_are_nonfinancial _ _ _ request needed

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Consumers
