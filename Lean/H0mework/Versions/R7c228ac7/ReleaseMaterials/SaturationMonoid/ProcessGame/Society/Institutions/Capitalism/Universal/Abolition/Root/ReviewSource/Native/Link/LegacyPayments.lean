import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.LegacyDeclaration
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Legacy

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.Legacy

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument) (depth count : Nat)

private theorem original_native_cut_is_the_next_declaration_ordinal :
    Settlement.physicalIndex source.input depth count = ordinal source depth count + 1 := by
  have enough := Macro.Services.Native.actual_cut_includes_original_request source depth count
  change 2 ≤ Settlement.physicalIndex source.input depth count at enough
  unfold ordinal
  omega

theorem original_native_payment_is_the_next_declaration_update (index : source.Slot) :
    Macro.Services.originalPayments source depth count index =
      source.update (payments source depth count) (source.currentAt (ordinal source depth count))
        (ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input (ordinal source depth count)).current)
        (ordinal source depth count) index := by
  change (source.frameAt (Settlement.physicalIndex source.input depth count)).payments index = _
  rw [original_native_cut_is_the_next_declaration_ordinal source depth count]
  change source.update (payments source depth count) (source.frameAt (ordinal source depth count)).raw
    (source.frameWord (ordinal source depth count) (source.frameAt (ordinal source depth count)))
    (ordinal source depth count) index = _
  rw [(source.canonical_frame (ordinal source depth count)).1,
    (source.canonical_frame (ordinal source depth count)).2]

variable (prefixLimit renewalLimit : Nat)
  {task : Material.OriginalTask source.input depth count}
  (identity : PlanningIdentity source depth count task)
  (current : Physical.Cursor Party Good Port Technology Instrument)

namespace PlanningIdentity

theorem declaration_payment_is_on_the_original_native_index
    (index : Material.Slot source.input depth count task)
    (paid : Material.DeclarationPaid source.input depth count task index) :
    source.SlotPaid (source.currentAt (ordinal source depth count))
      (ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input (ordinal source depth count)).current)
      (identity.originalIndex index) := by
  unfold Material.DeclarationPaid Material.SlotPaid at paid
  rw [identity.mapped_slot_is_the_original_indexed_slot index,
    show task.val.earliest = source.seed.task.earliest from (congrArg PublicTaskSpec.earliest identity.task_eq).trans rfl,
    show task.val.deadline = source.seed.task.deadline from (congrArg PublicTaskSpec.deadline identity.task_eq).trans rfl] at paid
  exact paid

theorem physical_payment_is_on_the_original_native_index
    (position : Fin current.past.length) (index : Material.Slot source.input depth count task)
    (paid : Material.PhysicalPaid source.input depth count prefixLimit renewalLimit task current.past position index) :
    Macro.Services.PaidOn source depth count prefixLimit renewalLimit current.past position (identity.originalIndex index) := by
  unfold Material.PhysicalPaid Material.EventPaid at paid
  rw [identity.mapped_slot_is_the_original_indexed_slot index,
    show task.val.earliest = source.seed.task.earliest from (congrArg PublicTaskSpec.earliest identity.task_eq).trans rfl,
    show task.val.deadline = source.seed.task.deadline from (congrArg PublicTaskSpec.deadline identity.task_eq).trans rfl] at paid
  exact paid

theorem declaration_payment_is_recorded_at_the_original_native_cut
    (index : Material.Slot source.input depth count task)
    (paid : Material.DeclarationPaid source.input depth count task index) :
    (Macro.Services.originalPayments source depth count (identity.originalIndex index)).isSome = true := by
  rw [original_native_payment_is_the_next_declaration_update]
  have actual := identity.declaration_payment_is_on_the_original_native_index source depth count index paid
  unfold OutstandingSource.update
  split
  · rfl
  · rw [if_pos actual]
    rfl

theorem material_payment_is_recorded_for_the_original_native_index
    (index : Material.Slot source.input depth count task)
    (paid : (Material.payment? source.input depth count prefixLimit renewalLimit task current index).isSome = true) :
    (Macro.Services.payments source depth count prefixLimit renewalLimit current.past (identity.originalIndex index)).isSome = true := by
  cases original : Macro.Services.payments source depth count prefixLimit renewalLimit current.past (identity.originalIndex index) with
  | some occurrence => rfl
  | none =>
      have missing := (Macro.Services.an_unpaid_slot_has_no_hidden_original_or_actual_receipt
        source depth count prefixLimit renewalLimit current.past (identity.originalIndex index)).mp original
      rcases Material.recorded_payment_has_its_exact_original_source source.input depth count prefixLimit renewalLimit task current index paid with canonical | ⟨position, actual⟩
      · have found :=  identity.declaration_payment_is_recorded_at_the_original_native_cut source depth count index canonical
        rw [missing.1] at found
        cases found
      · exact (missing.2 position (identity.physical_payment_is_on_the_original_native_index source depth count prefixLimit renewalLimit current position index actual)).elim

end PlanningIdentity

#print axioms original_native_payment_is_the_next_declaration_update
#print axioms PlanningIdentity.declaration_payment_is_recorded_at_the_original_native_cut
#print axioms PlanningIdentity.material_payment_is_recorded_for_the_original_native_index

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.Legacy
