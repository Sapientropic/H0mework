import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Trace
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Accounts
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Control

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive

open ResponsibilityLifecycle Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open private consumeItems from
  H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold

variable (history : List (Compile.RawInput Party Good Port Technology Instrument))
  (before : (Epoch.Finance.process input depth count).GeneratedState)

def word := completeWord input depth count (Physical.Public.interpreter input) before

def nextHistory := history ++ submitted (word input depth count before)

def nextAccount := accountAfter input depth count history (word input depth count before) before

theorem primitive_resources_generate_the_same_requested_word_and_actual_native_inventory
    (resources : ArchiveNative.Conditions input depth count history before) :
    (events input depth count history (word input depth count before)).map
        (fun item => (item.instruction input depth count).request) = word input depth count before ∧
    (∀ item ∈ events input depth count history (word input depth count before),
      (item.interpreter input depth count).Valid (item.instruction input depth count).before
        (item.instruction input depth count).request) ∧
    (state input depth count (nextHistory input depth count history before)).raw =
      ((Physical.Public.interpreter input).execute (state input depth count history).raw 0 (word input depth count before)).final :=
  the_actual_primitive_prefixes_retain_the_whole_original_word input depth count history 0 (word input depth count before)
    (ArchiveNative.every_actual_request_uses_its_original_debtor_without_extra_consent input depth count before)
    (ArchiveNative.primitive_source_resources_generate_all_actual_items input depth count history before resources)

theorem actual_primitive_resources_pay_all_original_shares_and_keep_the_whole_ledger
    (resources : ArchiveNative.Conditions input depth count history before) :
    (∀ instrument debtor holder,
      ledgerClaims input depth count (nextAccount input depth count history before).current instrument debtor holder = 0) ∧
    (nextAccount input depth count history before).current.slots.map (Epoch.Finance.slotClaim input depth count) =
      before.current.slots.map (Epoch.Finance.slotClaim input depth count) ∧
    before.current.history <+: (nextAccount input depth count history before).current.history := by
  have actual := primitive_resources_generate_the_same_requested_word_and_actual_native_inventory input depth count history before resources
  have payments : PaymentWord ((events input depth count history (word input depth count before)).map
      (fun item => (item.instruction input depth count).request)) := by
    rw [actual.1]
    exact the_complete_source_word_is_a_nonnegative_payment_inventory input depth count _ before
  have matched : ∀ instrument debtor holder, ledgerClaims input depth count before.current instrument debtor holder =
      wordValue ((events input depth count history (word input depth count before)).map
        (fun item => (item.instruction input depth count).request)) instrument debtor holder := by
    intro instrument debtor holder
    rw [actual.1]
    exact (the_complete_source_word_has_exactly_the_original_principal input depth count _ before instrument debtor holder).symm
  have paid := the_original_item_fold_exhausts_the_entire_source_settlement_inventory input depth count _ payments actual.2.1 before matched
  unfold nextAccount
  rw [the_actual_sequential_native_account_is_the_same_original_item_fold]
  exact ⟨paid.1,paid.2,the_original_finite_settlement_history_is_preserved input depth count _ before⟩

theorem actual_primitive_resources_preserve_the_clock_until_the_real_period_boundary
    (resources : ArchiveNative.Conditions input depth count history before) :
    (state input depth count (nextHistory input depth count history before)).raw.clock = (state input depth count history).raw.clock ∧
      (state input depth count (nextHistory input depth count history before)).raw.round = (state input depth count history).raw.round := by
  rw [(primitive_resources_generate_the_same_requested_word_and_actual_native_inventory input depth count history before resources).2.2]
  exact a_whole_instruction_word_preserves_the_clock_until_the_period_boundary _ _ _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
