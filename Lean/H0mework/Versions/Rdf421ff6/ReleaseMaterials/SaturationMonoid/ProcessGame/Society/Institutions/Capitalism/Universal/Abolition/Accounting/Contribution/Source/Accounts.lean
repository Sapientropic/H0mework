import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source.Issued

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

theorem each_actual_account_has_at_most_one_slot_per_original_contribution (cut : Nat) :
    ((Financial.accountAt input cut).current.slots.map
      (fun slot => (Financial.slotClaim input slot).origin)).Nodup := by
  have unique := the_actual_source_never_reissues_an_original_contribution input cut
  rw [← Financial.account_claims_are_exactly_the_source_issues input cut,List.map_map] at unique
  exact unique

theorem every_actual_inventory_prefix_has_unique_original_contributions (cut position : Nat) :
    ((Financial.consumeOrigins input
      ((Financial.inventoryAt input (ProgrammeHistory.visitAt input cut)).take position)
      (Financial.accountAt input cut)).current.slots.map
        (fun slot => (Financial.slotClaim input slot).origin)).Nodup := by
  have keeps := Financial.consumeOrigins_preserves_original_claims input
    ((Financial.inventoryAt input (ProgrammeHistory.visitAt input cut)).drop position)
    (Financial.consumeOrigins input
      ((Financial.inventoryAt input (ProgrammeHistory.visitAt input cut)).take position)
      (Financial.accountAt input cut))
  rw [← Financial.consumeOrigins_append,List.take_append_drop,← Financial.accountAt_successor] at keeps
  have full := each_actual_account_has_at_most_one_slot_per_original_contribution input (cut + 1)
  have mapped := keeps.map Financial.IssuedClaim.origin
  rw [List.map_map,List.map_map] at mapped
  exact full.sublist mapped.sublist

private theorem aligned_cursor_has_unique_original_contributions
    (cursor : Cursor.State input) (aligned : Cursor.PrefixAligned input cursor) :
    (cursor.account.current.slots.map (fun slot => (Financial.slotClaim input slot).origin)).Nodup := by
  rw [aligned.2]
  exact every_actual_inventory_prefix_has_unique_original_contributions input cursor.cycle cursor.position

theorem every_actual_entering_continuation_has_unique_original_contributions (physical steps : Nat) :
    (((Cursor.next input)^[steps] (Cursor.enteringAt input physical)).account.current.slots.map
      (fun slot => (Financial.slotClaim input slot).origin)).Nodup := by
  apply aligned_cursor_has_unique_original_contributions input
  induction steps with
  | zero => exact Cursor.entering_prefix_aligned input physical
  | succ steps inherited =>
      rw [Function.iterate_succ_apply']
      exact Cursor.next_prefix_aligned input _ inherited

theorem every_registered_old_account_has_unique_original_contributions (depth count : Nat) :
    ((Runtime.frames input depth count).cursor input).account.current.slots.map
      (fun slot => (Financial.slotClaim input slot).origin) |>.Nodup :=
  aligned_cursor_has_unique_original_contributions input _ (Runtime.frames_prefix_aligned input depth count)

theorem two_registered_slots_cannot_be_the_same_original_contribution (depth count : Nat)
    (first second : Fin ((Runtime.frames input depth count).cursor input).account.current.slots.length)
    (same : (Financial.slotClaim input (((Runtime.frames input depth count).cursor input).account.current.slots.get first)).origin =
      (Financial.slotClaim input (((Runtime.frames input depth count).cursor input).account.current.slots.get second)).origin) :
    first = second := by
  have unique := every_registered_old_account_has_unique_original_contributions input depth count
  apply Fin.ext
  apply (unique.getElem_inj_iff (hi := by simpa only [List.length_map] using first.isLt)
    (hj := by simpa only [List.length_map] using second.isLt)).mp
  simp only [List.getElem_map]
  simpa only [List.getElem_map,List.get_eq_getElem] using same

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source
