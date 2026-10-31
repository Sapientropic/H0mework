import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.LegacyPayments
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.Legacy

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument) (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)

private theorem terminal_of_original_service_readout (index : source.Slot)
    (paid : (Macro.Services.payments source depth count prefixLimit renewalLimit current.past index).isSome = true) :
    ((OriginAt.outstanding source).state depth count
      (atPast (.outstanding source) depth count prefixLimit renewalLimit current.past index)).current.TerminalAt 0 := by
  rw [existing_complete_state_archive_and_run_are_unchanged]
  exact (Macro.Services.Native.Micro.terminal_iff_the_original_service_readout_is_paid
    source depth count prefixLimit renewalLimit current.past index).mpr paid

private theorem unpaid_at_the_native_cut_was_unpaid_at_the_declaration
    (index : source.Slot) (unpaid : Macro.Services.originalPayments source depth count index = none) :
    payments source depth count index = none := by
  cases prior : payments source depth count index with
  | none => rfl
  | some paid =>
      have preserved := source.payment_preserved (payments source depth count)
        (source.currentAt (ordinal source depth count))
        (ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input (ordinal source depth count)).current)
        (ordinal source depth count) index paid prior
      have original := (original_native_payment_is_the_next_declaration_update source depth count index).trans preserved
      rw [unpaid] at original
      cases original

namespace PlanningIdentity
variable {task : Material.OriginalTask source.input depth count}
  (identity : PlanningIdentity source depth count task)

theorem every_unpaid_original_index_has_its_original_declared_position
    (index : source.Slot) (unpaid : payments source depth count index = none) :
    ∃ declared : Material.Slot source.input depth count task, identity.originalIndex declared = index := by
  have member := (source.pending_index_iff (payments source depth count) index).mpr unpaid
  obtain ⟨position, within, same⟩ := List.mem_iff_getElem.mp member
  let declared : Material.Slot source.input depth count task :=
    ⟨position, by simpa [identity.task_eq, OutstandingSource.pendingTask, OutstandingSource.pendingSlots] using within⟩
  refine ⟨declared, ?_⟩
  change (source.pendingIndices (payments source depth count)).get ⟨position, _⟩ = index
  exact same

include identity in
theorem all_material_payments_settle_the_whole_original_legacy_native_scope
    (paid : ∀ index : Material.Slot source.input depth count task,
      (Material.payment? source.input depth count prefixLimit renewalLimit task current index).isSome = true) :
    ∀ index : source.Slot,
      ((OriginAt.outstanding source).state depth count
        (atPast (.outstanding source) depth count prefixLimit renewalLimit current.past index)).current.TerminalAt 0 := by
  intro index
  apply terminal_of_original_service_readout source depth count prefixLimit renewalLimit current index
  cases original : Macro.Services.payments source depth count prefixLimit renewalLimit current.past index with
  | some occurrence => rfl
  | none =>
      have missing := (Macro.Services.an_unpaid_slot_has_no_hidden_original_or_actual_receipt
        source depth count prefixLimit renewalLimit current.past index).mp original
      have declarationUnpaid := unpaid_at_the_native_cut_was_unpaid_at_the_declaration source depth count index missing.1
      obtain ⟨declared, same⟩ := identity.every_unpaid_original_index_has_its_original_declared_position source depth count index declarationUnpaid
      have actual := identity.material_payment_is_recorded_for_the_original_native_index source depth count prefixLimit renewalLimit current declared (paid declared)
      rw [same, original] at actual
      cases actual

include identity in
theorem the_already_recorded_legacy_scope_consumes_its_actual_material_payments
    (scope : RecordedAt source.input depth count prefixLimit renewalLimit current)
    (sameCreator : scope.origin = .outstanding source)
    (paid : ∀ index : Material.Slot source.input depth count task,
      (Material.payment? source.input depth count prefixLimit renewalLimit task current index).isSome = true) :
    OriginalScopePaid source.input depth count prefixLimit renewalLimit current (.recorded scope) := by
  rcases scope with ⟨origin, state, generated⟩
  change origin = .outstanding source at sameCreator
  cases sameCreator
  intro index
  change (state index).current.TerminalAt 0
  rw [generated index]
  exact all_material_payments_settle_the_whole_original_legacy_native_scope
    source depth count prefixLimit renewalLimit current identity paid index

end PlanningIdentity

namespace CompletionDeclaration

include current in
theorem the_original_completed_scope_stays_complete
    (residual : CompletionDeclaration source depth count) :
    ∀ index : source.Slot,
      ((OriginAt.outstanding source).state depth count
        (atPast (.outstanding source) depth count prefixLimit renewalLimit current.past index)).current.TerminalAt 0 := by
  intro index
  obtain ⟨paid, original⟩ := source.complete_all_recorded (ordinal source depth count) residual.oldScopeComplete index
  have native : Macro.Services.originalPayments source depth count index = some paid :=
    (original_native_payment_is_the_next_declaration_update source depth count index).trans
      (source.payment_preserved (payments source depth count) (source.currentAt (ordinal source depth count))
        (ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input (ordinal source depth count)).current)
        (ordinal source depth count) index paid original)
  apply terminal_of_original_service_readout source depth count prefixLimit renewalLimit current index
  rw [Macro.Services.an_original_payment_keeps_its_original_ordinal source depth count prefixLimit renewalLimit current.past index paid native]
  rfl

theorem the_already_recorded_completed_scope_keeps_its_original_archive
    (residual : CompletionDeclaration source depth count)
    (scope : RecordedAt source.input depth count prefixLimit renewalLimit current)
    (sameCreator : scope.origin = .outstanding source) :
    OriginalScopePaid source.input depth count prefixLimit renewalLimit current (.recorded scope) := by
  rcases scope with ⟨origin, state, generated⟩
  change origin = .outstanding source at sameCreator
  cases sameCreator
  intro index
  change (state index).current.TerminalAt 0
  rw [generated index]
  exact the_original_completed_scope_stays_complete source depth count prefixLimit renewalLimit current residual index

end CompletionDeclaration

#print axioms CompletionDeclaration.the_already_recorded_completed_scope_keeps_its_original_archive
#print axioms PlanningIdentity.every_unpaid_original_index_has_its_original_declared_position
#print axioms PlanningIdentity.all_material_payments_settle_the_whole_original_legacy_native_scope
#print axioms PlanningIdentity.the_already_recorded_legacy_scope_consumes_its_actual_material_payments

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.Legacy
