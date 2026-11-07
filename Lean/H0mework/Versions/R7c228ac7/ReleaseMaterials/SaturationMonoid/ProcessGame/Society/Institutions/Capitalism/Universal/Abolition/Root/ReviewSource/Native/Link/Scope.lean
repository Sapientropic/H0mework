import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.Payments

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (code : SourceCode Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  {task : Material.OriginalTask code.input depth count}
  (identity : SameBirth code depth count task)
  (current : Physical.Cursor Party Good Port Technology Instrument)

namespace SameBirth

theorem declaration_payment_is_the_original_native_payment
    (index : Material.Slot code.input depth count task)
    (paid : Material.DeclarationPaid code.input depth count task index) :
    SlotPaid code 0 (identity.nativeSlot index) := by
  have originalVisit : Settlement.committedVisit code.input depth count =
      ProgrammeHistory.visitAt code.input 1 := congrArg (ProgrammeHistory.visitAt code.input) identity.originalOrdinal
  have sameBefore := congrArg (fun visit => ProgrammeSource.rawCurrent code.input visit.current) originalVisit
  have sameWord := congrArg (fun visit => ProgrammeSource.rawEvent code.input visit.current) originalVisit
  unfold Material.DeclarationPaid Material.SlotPaid at paid
  rw [identity.native_slot_is_the_same_original_incidence index,
    congrArg PublicTaskSpec.earliest identity.task_eq, congrArg PublicTaskSpec.deadline identity.task_eq,
    sameBefore, sameWord] at paid
  exact paid

theorem physical_payment_is_the_original_native_payment
    (position : Fin current.past.length) (index : Material.Slot code.input depth count task)
    (paid : Material.PhysicalPaid code.input depth count prefixLimit renewalLimit task current.past position index) :
    (actualInput depth count prefixLimit renewalLimit (current.past.take position.val)
      (current.past.get position)).Paid (code := code) (identity.nativeSlot index) := by
  unfold Material.PhysicalPaid Material.EventPaid at paid
  rw [identity.native_slot_is_the_same_original_incidence index,
    congrArg PublicTaskSpec.earliest identity.task_eq, congrArg PublicTaskSpec.deadline identity.task_eq] at paid
  exact paid

theorem an_observed_payment_consumes_its_same_original_native_slot
    (index : Material.Slot code.input depth count task)
    (paid : (Material.payment? code.input depth count prefixLimit renewalLimit task current index).isSome = true) :
    ((OriginAt.source code).state depth count
      (atPast (.source code) depth count prefixLimit renewalLimit current.past (identity.nativeSlot index))).current.TerminalAt 0 := by
  rcases Material.recorded_payment_has_its_exact_original_source code.input depth count prefixLimit renewalLimit
      task current index paid with canonical | ⟨position, actual⟩
  · exact the_original_declaration_payment_is_retained_in_the_same_native_fold code depth count prefixLimit renewalLimit
      identity.originalOrdinal current.past _ (identity.declaration_payment_is_the_original_native_payment code depth count index canonical)
  · exact an_original_actual_payment_terminates_the_same_recorded_native_slot code depth count prefixLimit renewalLimit
      current.past position _ (identity.physical_payment_is_the_original_native_payment code depth count prefixLimit renewalLimit current position index actual)

theorem every_original_native_slot_is_covered_by_the_same_declaration
    (index : Slot code) : ∃ declared : Material.Slot code.input depth count task,
      identity.nativeSlot declared = index := by
  let declared : Material.Slot code.input depth count task :=
    ⟨index.val, by rw [identity.task_eq]; exact index.isLt⟩
  exact ⟨declared, Fin.ext rfl⟩

include identity in
theorem the_whole_paid_material_scope_consumes_the_whole_original_native_scope
    (paid : ∀ index : Material.Slot code.input depth count task,
      (Material.payment? code.input depth count prefixLimit renewalLimit task current index).isSome = true) :
    ∀ index : Slot code,
      ((OriginAt.source code).state depth count
        (atPast (.source code) depth count prefixLimit renewalLimit current.past index)).current.TerminalAt 0 := by
  intro index
  obtain ⟨declared, same⟩ := SameBirth.every_original_native_slot_is_covered_by_the_same_declaration code depth count identity index
  rw [← same]
  exact identity.an_observed_payment_consumes_its_same_original_native_slot code depth count prefixLimit renewalLimit current declared (paid declared)

end SameBirth

#print axioms SameBirth.declaration_payment_is_the_original_native_payment
#print axioms SameBirth.physical_payment_is_the_original_native_payment
#print axioms SameBirth.an_observed_payment_consumes_its_same_original_native_slot
#print axioms SameBirth.the_whole_paid_material_scope_consumes_the_whole_original_native_scope

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link
