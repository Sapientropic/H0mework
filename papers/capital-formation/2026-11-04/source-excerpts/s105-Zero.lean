import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Consumers.Scene
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Zero

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Consumers.Zero

open ResponsibilityLifecycle Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

def birthWord : RawEvent Original.Party Unit Unit Unit Unit := [Original.request 0 (.issue () 0 1 0)]
def history := submitted birthWord
def before := accountAfter Original.input 0 0 [] birthWord genesis

theorem the_actual_zero_issue_has_no_positive_principal_and_is_still_live :
    before.current.slots.map Original.isTerminal = [false] ∧
      ∀ slot ∈ before.current.slots, Epoch.Finance.slotBalance Original.input 0 0 slot = 0 := by
  have matrix : ∀ instrument debtor holder,
      ledgerClaims Original.input 0 0 before.current instrument debtor holder = 0 := by decide +kernel
  exact ⟨by decide +kernel,fun slot listed =>
    a_zero_full_matrix_clears_every_original_slot_balance Original.input 0 0 before matrix slot listed⟩

theorem a_positive_payment_scan_does_not_fabricate_an_archive :
    Native.word Original.input 0 0 before = [] ∧
      (accountAfter Original.input 0 0 history [] before).current.slots.map Original.isTerminal = [false] :=
  ⟨zero_balances_cannot_generate_another_positive_payment Original.input 0 0 _ before
      the_actual_zero_issue_has_no_positive_principal_and_is_still_live.2,
    the_actual_zero_issue_has_no_positive_principal_and_is_still_live.1⟩

theorem the_source_generates_a_real_zero_boundary_primitive :
    word Original.input 0 0 before = [Original.request 0 (.settle () 0 0 0)] := by
  change Native.word Original.input 0 0 before ++ archiveWord Original.input 0 0 (Physical.Public.interpreter Original.input) before = _
  rw [a_positive_payment_scan_does_not_fabricate_an_archive.1]
  have borrower : ∀ slot ∈ before.current.slots,
      (Epoch.Finance.slotClaim Original.input 0 0 slot).debtor Original.input 0 0 = 0 := by decide +kernel
  rw [SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Consumers.fixed_address_zero_boundaries_read_only_the_actual_live_flags before borrower,
    the_actual_zero_issue_has_no_positive_principal_and_is_still_live.1]
  rfl

theorem the_original_current_has_the_primitive_resources_for_the_zero_touch :
    ArchiveNative.Conditions Original.input 0 0 history before := by
  unfold ArchiveNative.Conditions
  change Priority.Adequacy.Capacity.RecipeFacts (Physical.Public.interpreter Original.input)
      (Priority.Adequacy.Primitive.execute (Physical.Public.interpreter Original.input)
        (ArchiveNative.sourceState Original.input 0 0 history).raw 0 (word Original.input 0 0 before)).items ∧
    Priority.Adequacy.Capacity.Startup (Physical.Public.interpreter Original.input)
      (ArchiveNative.sourceState Original.input 0 0 history).raw (word Original.input 0 0 before)
  rw [the_source_generates_a_real_zero_boundary_primitive]
  decide +kernel

theorem the_real_zero_primitive_generates_the_original_row_archive :
    (nextAccount Original.input 0 0 history before).current.slots.map Original.isTerminal = [true] := by
  unfold nextAccount
  rw [the_source_generates_a_real_zero_boundary_primitive]
  decide +kernel

theorem archival_preserves_the_original_zero_claim_and_actual_history :
    (nextAccount Original.input 0 0 history before).current.slots.map (Epoch.Finance.slotClaim Original.input 0 0) =
      before.current.slots.map (Epoch.Finance.slotClaim Original.input 0 0) ∧
      before.current.history <+: (nextAccount Original.input 0 0 history before).current.history :=
  (actual_primitive_resources_pay_all_original_shares_and_keep_the_whole_ledger
    Original.input 0 0 history before the_original_current_has_the_primitive_resources_for_the_zero_touch).2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Consumers.Zero
