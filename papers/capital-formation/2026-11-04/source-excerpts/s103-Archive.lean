import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Consumers.Source
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Archive.Native.Complete

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Consumers

open ResponsibilityLifecycle Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem the_stronger_source_word_contains_the_same_principal_and_real_zero_touches :
    ArchiveNative.word input 0 0 before =
      [request 0 (.settle () 0 2 1),request 0 (.settle () 0 1 1),
       request 0 (.settle () 0 0 0),request 0 (.settle () 0 0 0)] := by
  change Native.word input 0 0 before ++ archiveWord input 0 0 (Physical.Public.interpreter input) before = _
  rw [the_actual_generated_word_is_the_original_two_share_settlement]
  have borrower : ∀ slot ∈ before.current.slots,
      (Epoch.Finance.slotClaim input 0 0 slot).debtor input 0 0 = 0 := by decide +kernel
  rw [fixed_address_zero_boundaries_read_only_the_actual_live_flags before borrower]
  have flags : before.current.slots.map isTerminal = [false,false] := by decide +kernel
  rw [flags]
  rfl

theorem the_complete_batch_has_its_own_sufficient_primitive_resources :
    ArchiveNative.Conditions input 0 0 history before := by
  unfold ArchiveNative.Conditions
  rw [the_stronger_source_word_contains_the_same_principal_and_real_zero_touches]
  decide +kernel

theorem every_original_slot_has_an_actual_archive_from_the_same_source
    (slot : ObligationSlot (Epoch.Finance.vocabulary input 0 0))
    (listed : slot ∈ (ArchiveNative.after input 0 0 history before).current.slots) :
    ∃ archive, slot = .terminal archive :=
  ArchiveNative.primitive_resources_generate_real_archives_for_every_original_slot input 0 0 history before
    the_complete_batch_has_its_own_sufficient_primitive_resources slot listed

theorem the_same_complete_batch_preserves_all_original_claims_and_history :
    (ArchiveNative.after input 0 0 history before).current.slots.map (Epoch.Finance.slotClaim input 0 0) =
      before.current.slots.map (Epoch.Finance.slotClaim input 0 0) ∧
      before.current.history <+: (ArchiveNative.after input 0 0 history before).current.history :=
  (ArchiveNative.primitive_resources_pay_every_original_share_and_preserve_the_whole_ledger
    input 0 0 history before the_complete_batch_has_its_own_sufficient_primitive_resources).2

theorem zero_boundary_requests_do_not_create_a_second_material_payment :
    (ArchiveNative.result input 0 0 history before).next.raw.stock 0 () = 0 ∧
      (ArchiveNative.result input 0 0 history before).next.raw.stock 1 () = 1 ∧
      (ArchiveNative.result input 0 0 history before).next.raw.stock 2 () = 1 := by
  unfold ArchiveNative.result
  rw [the_stronger_source_word_contains_the_same_principal_and_real_zero_touches]
  decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Consumers
