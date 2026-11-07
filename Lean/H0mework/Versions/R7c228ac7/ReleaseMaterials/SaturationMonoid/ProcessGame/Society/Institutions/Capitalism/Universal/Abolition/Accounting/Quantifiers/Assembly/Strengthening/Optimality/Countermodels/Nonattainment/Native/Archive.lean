import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native.Fold

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (accountAfter tag visit oneItems events actualNativeRun)
noncomputable section

theorem every_candidate_retires_the_same_original_slot_and_preserves_its_native_claim (n : Nat) :
    ∃ archive : TerminalArchive (Abolition.Root.Epoch.Finance.vocabulary input 0 0),
      (afterAccount n).current.slots = [.terminal archive] ∧ archive.obligation = originalObligation ∧
      archive.obligation.content = .inr originalClaim ∧
      originalAccount.current.history <+: (afterAccount n).current.history := by
  have actual := every_family_inventory_is_its_original_actual_requests n
  have original : (events input 0 0 initialHistory (word n)).map
      (fun item => (item.instruction input 0 0).request) = [upgrade n,produce] ++ [repay] := actual.1
  have material : ∀ instruction ∈ [upgrade n,produce],Responsibility.NonFinancialOperation instruction.operation := by
    intro instruction member
    rcases List.mem_cons.mp member with rfl | later
    · trivial
    · cases List.mem_singleton.mp later
      trivial
  obtain ⟨last,member,same,tail⟩ := Evolution.Ingress.Joint.Material.Runtime.Retirement.the_original_material_prefix_reaches_its_same_actual_financial_tail
    input 0 0 [upgrade n,produce] repay _ original material originalAccount
  have operation : (last.instruction input 0 0).request.operation = .settle
      (originalObligation.content.instrument input 0 0) (originalObligation.content.debtor input 0 0) true 1 := by
    rw [same,the_original_borrower_is_still_the_same_source_party]
    rfl
  obtain ⟨archive,terminal,identity,history⟩ := Evolution.Ingress.Joint.Material.Runtime.Retirement.the_actual_matching_full_payment_retires_its_original_native_slot
    input 0 0 originalAccount originalObligation the_same_original_live_slot_is_not_replaced last true 1 operation
      (actual.2 last member) the_original_live_slot_has_its_actual_single_share
  have after : afterAccount n = (Abolition.Root.Epoch.Finance.consume input 0 0 last originalAccount).next input 0 0 :=
    (the_original_sequential_account_is_its_ordered_actual_item_fold initialHistory (word n) originalAccount).trans tail
  rw [after]
  exact ⟨archive,terminal,identity,by rw [identity]; rfl,history⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native
