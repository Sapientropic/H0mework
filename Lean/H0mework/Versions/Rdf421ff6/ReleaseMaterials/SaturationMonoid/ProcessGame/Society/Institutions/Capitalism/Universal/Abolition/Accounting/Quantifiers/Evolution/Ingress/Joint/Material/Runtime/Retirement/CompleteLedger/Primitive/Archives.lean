import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Control

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
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold

variable (history : List (Compile.RawInput Party Good Port Technology Instrument))
  (before : (Epoch.Finance.process input depth count).GeneratedState)

theorem actual_primitive_resources_generate_a_real_archive_for_every_original_slot
    (resources : ArchiveNative.Conditions input depth count history before)
    (slot : ObligationSlot (Epoch.Finance.vocabulary input depth count))
    (listed : slot ∈ (nextAccount input depth count history before).current.slots) :
    ∃ archive, slot = .terminal archive := by
  cases slot with
  | terminal archive => exact ⟨archive,rfl⟩
  | live survivor =>
      have zero : survivor.residual = 0 := a_zero_full_matrix_clears_every_original_slot_balance input depth count _
        (actual_primitive_resources_pay_all_original_shares_and_keep_the_whole_ledger input depth count history before resources).1 _ listed
      obtain ⟨index,present⟩ := List.mem_iff_getElem?.mp listed
      unfold nextAccount at present
      rw [the_actual_sequential_native_account_is_the_same_original_item_fold] at present
      have actual := primitive_resources_generate_the_same_requested_word_and_actual_native_inventory input depth count history before resources
      have payments : PaymentWord ((events input depth count history (word input depth count before)).map
          (fun item => (item.instruction input depth count).request)) := by
        rw [actual.1]
        exact the_complete_source_word_is_a_nonnegative_payment_inventory input depth count _ before
      have survivorTrace := a_zero_survives_the_complete_actual_payment_inventory_only_if_untouched input depth count
        (events input depth count history (word input depth count before)) payments actual.2.1 before index survivor zero present
      have original : .live survivor ∈ before.current.slots := List.mem_of_getElem? survivorTrace.1
      have touched := the_original_live_row_generates_its_own_zero_boundary_request input depth count
        (Physical.Public.interpreter input) before survivor original
      have full : archiveRequest input depth count (Physical.Public.interpreter input) survivor ∈
          (events input depth count history (word input depth count before)).map
            (fun item => (item.instruction input depth count).request) := by
        rw [actual.1]
        exact List.mem_append.mpr (Or.inr touched)
      obtain ⟨item,member,same⟩ := List.mem_map.mp full
      have operation : (item.instruction input depth count).request.operation =
          .settle (survivor.content.instrument input depth count) (survivor.content.debtor input depth count)
            (survivor.content.debtor input depth count) 0 := by rw [same]; rfl
      obtain ⟨receipt,selected,_,_,_⟩ := an_actual_matching_payment_generates_its_original_review
        input depth count survivor.content item (survivor.content.debtor input depth count) 0 operation (actual.2.1 item member)
      rw [survivorTrace.2 item member] at selected
      cases selected

theorem each_original_index_has_its_own_actual_primitive_archive
    (resources : ArchiveNative.Conditions input depth count history before)
    (index : Fin before.current.slots.length) :
    ∃ archive, (nextAccount input depth count history before).current.slots[index.val]? = some (.terminal archive) := by
  have claims := (actual_primitive_resources_pay_all_original_shares_and_keep_the_whole_ledger input depth count history before resources).2.1
  have length : (nextAccount input depth count history before).current.slots.length = before.current.slots.length := by
    simpa only [List.length_map] using congrArg List.length claims
  have within : index.val < (nextAccount input depth count history before).current.slots.length := by rw [length]; exact index.isLt
  obtain ⟨archive,same⟩ := actual_primitive_resources_generate_a_real_archive_for_every_original_slot input depth count history before resources
    ((nextAccount input depth count history before).current.slots[index.val]) (List.getElem_mem within)
  exact ⟨archive,(List.getElem?_eq_getElem within).trans (congrArg some same)⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
