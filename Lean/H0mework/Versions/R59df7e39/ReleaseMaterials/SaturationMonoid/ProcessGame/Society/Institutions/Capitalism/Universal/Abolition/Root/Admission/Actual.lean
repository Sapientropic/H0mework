import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.Registry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Datum input (frame input depth count))

def actualSourceEvent := (ask input depth count datum).receipt.1

theorem actual_source_whole_ledger_is_original :
    HEq (actualSourceEvent input depth count datum).wholeLedgerWriteBack
      ((frame input depth count).native.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (frame input depth count).visit.current) :=
  (actualSourceEvent input depth count datum).wholeLedgerWriteBack_eq

theorem every_original_row_has_actual_disposition
    (row : OpenResponsibilityAt (frame input depth count).native.N
      (Continuation.oldSupport input (frame input depth count))) :
    (actualSourceEvent input depth count datum).wholeLedgerWriteBack.entryDisposition row =
      .evolved (((frame input depth count).native.program.emit
        (frame input depth count).visit.current).evolution.destination row).2 := by
  change ((frame input depth count).native.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
    (frame input depth count).visit.current).entryDisposition row = _
  rw [((frame input depth count).native.program.emit (frame input depth count).visit.current).generated_eq]
  rfl

theorem actual_first_write_keeps_every_old_row
    (row : OpenResponsibilityAt (frame input depth count).native.N
      (Continuation.oldSupport input (frame input depth count))) :
    (((generated input depth count datum).target.firstSuccessor.ledgerEvolution).destination
      ((generated input depth count datum).target.initialOpenLedger.forward row)).1 = row :=
  Continuation.destination_is_original_entry input (frame input depth count)
    (code input depth count datum).request (Continuation.initial input (frame input depth count)) row

theorem actual_first_write_has_no_unaccounted_origin
    (row : OpenResponsibilityAt (Continuation.N input (frame input depth count))
      (Continuation.supportAt input (frame input depth count)
        (generated input depth count datum).target.firstSuccessor.targetCurrent)) :
    (((generated input depth count datum).target.firstSuccessor.ledgerEvolution).origin row).1 = row :=
  Continuation.origin_is_original_entry input (frame input depth count)
    (code input depth count datum).request (Continuation.initial input (frame input depth count)) row

theorem actual_answer_has_the_source_result_receipt :
    ResultReceipt input depth count datum (ask input depth count datum).answer :=
  (ask input depth count datum).receipt.2.down.down

theorem actual_action_keeps_the_generated_target_law :
    (RootInquiryProcessNode.active (presentation input depth count datum)).PreservesGeneratedLivingLawAt
      (activation input depth count datum).query
      ((ask input depth count datum).next.node) :=
  (ask input depth count datum).next_preservesGeneratedLivingLaw

#print axioms actual_source_whole_ledger_is_original
#print axioms every_original_row_has_actual_disposition
#print axioms actual_first_write_keeps_every_old_row
#print axioms actual_first_write_has_no_unaccounted_origin
#print axioms actual_answer_has_the_source_result_receipt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission
