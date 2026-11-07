import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Archive.Native.Acceptance
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Archive.Fold
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Balances
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Replay
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Realization
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open Abolition.Root.Registered Source.Program

variable (history : List (Compile.RawInput Party Good Port Technology Instrument))
  (before : (process input depth count).GeneratedState)

open private consumeItems from
  H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold

theorem primitive_resources_pay_every_original_share_and_preserve_the_whole_ledger
    (resources : Conditions input depth count history before) :
    (∀ instrument debtor holder,
      ledgerClaims input depth count (after input depth count history before).current instrument debtor holder = 0) ∧
    (after input depth count history before).current.slots.map (slotClaim input depth count) =
      before.current.slots.map (slotClaim input depth count) ∧
    before.current.history <+: (after input depth count history before).current.history := by
  have requested := the_native_inventory_requests_exactly_the_original_source_word input depth count history before resources
  have payments : PaymentWord ((items input depth count history before).map (fun item => (item.instruction input depth count).request)) := by
    rw [requested]
    exact the_complete_source_word_is_a_nonnegative_payment_inventory input depth count _ before
  have matched : ∀ instrument debtor holder, ledgerClaims input depth count before.current instrument debtor holder =
      wordValue ((items input depth count history before).map (fun item => (item.instruction input depth count).request)) instrument debtor holder := by
    intro instrument debtor holder
    rw [requested]
    exact (the_complete_source_word_has_exactly_the_original_principal input depth count _ before instrument debtor holder).symm
  have complete := the_original_item_fold_exhausts_the_entire_source_settlement_inventory input depth count
    (items input depth count history before) payments
    (every_original_native_financial_item_is_actually_accepted input depth count history before resources) before matched
  exact ⟨complete.1,complete.2,the_original_finite_settlement_history_is_preserved input depth count _ before⟩

theorem primitive_resources_generate_real_archives_for_every_original_slot
    (resources : Conditions input depth count history before)
    (slot : ObligationSlot (vocabulary input depth count))
    (listed : slot ∈ (after input depth count history before).current.slots) :
    ∃ archive, slot = .terminal archive := by
  cases slot with
  | terminal archive => exact ⟨archive,rfl⟩
  | live survivor =>
      have zero : survivor.residual = 0 := a_zero_full_matrix_clears_every_original_slot_balance input depth count _
        (primitive_resources_pay_every_original_share_and_preserve_the_whole_ledger input depth count history before resources).1 _ listed
      obtain ⟨index,present⟩ := List.mem_iff_getElem?.mp listed
      have requested := the_native_inventory_requests_exactly_the_original_source_word input depth count history before resources
      have payments : PaymentWord ((items input depth count history before).map (fun item => (item.instruction input depth count).request)) := by
        rw [requested]
        exact the_complete_source_word_is_a_nonnegative_payment_inventory input depth count _ before
      have survivorTrace := a_zero_survives_the_complete_actual_payment_inventory_only_if_untouched input depth count
        (items input depth count history before) payments
        (every_original_native_financial_item_is_actually_accepted input depth count history before resources)
        before index survivor zero present
      have original : .live survivor ∈ before.current.slots := List.mem_of_getElem? survivorTrace.1
      have touched := the_original_live_row_generates_its_own_zero_boundary_request input depth count
        (Physical.Public.interpreter input) before survivor original
      have full : archiveRequest input depth count (Physical.Public.interpreter input) survivor ∈
          (items input depth count history before).map (fun item => (item.instruction input depth count).request) := by
        rw [requested]
        exact List.mem_append.mpr (Or.inr touched)
      obtain ⟨item,member,same⟩ := List.mem_map.mp full
      have operation : (item.instruction input depth count).request.operation =
          .settle (survivor.content.instrument input depth count) (survivor.content.debtor input depth count)
            (survivor.content.debtor input depth count) 0 := by rw [same]; rfl
      obtain ⟨receipt,selected,_,_,_⟩ := an_actual_matching_payment_generates_its_original_review
        input depth count survivor.content item (survivor.content.debtor input depth count) 0 operation
        (every_original_native_financial_item_is_actually_accepted input depth count history before resources item member)
      rw [survivorTrace.2 item member] at selected
      cases selected

def actualNativeRun : (process input depth count).Run before.current (after input depth count history before).current :=
  consumeVisit_run input depth count (tag input depth count history before) (visit input depth count history before) before

theorem the_complete_financial_batch_is_one_actual_original_material_occurrence
    (resources : Conditions input depth count history before) :
    (result input depth count history before).isAccepted = true ∧
      (result input depth count history before).next.raw =
        (Physical.Public.interpreter input).next (sourceState input depth count history).raw (word input depth count before) :=
  Execution.Prefix.the_original_public_compiler_accepts_its_checked_word input _ _
    (every_actual_request_uses_its_original_debtor_without_extra_consent input depth count before)
    (primitive_source_resources_generate_all_actual_items input depth count history before resources)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative
