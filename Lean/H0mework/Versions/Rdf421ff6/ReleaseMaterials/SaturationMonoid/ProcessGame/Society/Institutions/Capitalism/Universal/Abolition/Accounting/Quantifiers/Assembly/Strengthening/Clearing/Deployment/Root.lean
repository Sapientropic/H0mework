import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.History.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {oldReader : Macro.Raw.Reader input depth count}
  (source : Position input depth count oldReader)
  (resources : Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
    input depth count (history source) (before source))

local notation "done" => completed source resources

theorem every_original_slot_is_archived_in_the_actual_root
    (slot : ObligationSlot (Epoch.Finance.vocabulary input depth count))
    (listed : slot ∈ (nativeAccountFace done).rootRead.current.slots) : ∃ archive, slot = .terminal archive := by
  change slot ∈ (completedPosition source resources).actual.actual.account.current.slots at listed
  rw [the_whole_clearing_has_the_same_original_native_account] at listed
  exact Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.actual_primitive_resources_generate_a_real_archive_for_every_original_slot
    input depth count (history source) (before source) resources slot listed

theorem the_root_keeps_the_entire_original_native_ledger :
    (nativeAccountFace done).rootRead.current.slots.map (Epoch.Finance.slotClaim input depth count) =
      (before source).current.slots.map (Epoch.Finance.slotClaim input depth count) ∧
    (before source).current.history <+: (nativeAccountFace done).rootRead.current.history := by
  change (completedPosition source resources).actual.actual.account.current.slots.map _ = _ ∧
    _ <+: (completedPosition source resources).actual.actual.account.current.history
  rw [the_whole_clearing_has_the_same_original_native_account]
  exact (Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.actual_primitive_resources_pay_all_original_shares_and_keep_the_whole_ledger
    input depth count (history source) (before source) resources).2

theorem the_root_has_no_unpaid_original_principal :
    ∀ instrument debtor holder, Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ledgerClaims input depth count
      (nativeAccountFace done).rootRead.current instrument debtor holder = 0 := by
  change ∀ instrument debtor holder, Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ledgerClaims input depth count
    (completedPosition source resources).actual.actual.account.current instrument debtor holder = 0
  rw [the_whole_clearing_has_the_same_original_native_account]
  exact (Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.actual_primitive_resources_pay_all_original_shares_and_keep_the_whole_ledger
    input depth count (history source) (before source) resources).1

structure CompleteAt : Prop where
  source_root_preserved : (position source).frame.root = source.native.full.root
  actual_selected_history : done = Evolving.History.currentAt (position source).native (2 * (plan source).length)
  root_account_literal : (nativeAccountFace done).rootRead = (completedPosition source resources).actual.actual.account
  every_original_slot_archived : ∀ slot ∈ (nativeAccountFace done).rootRead.current.slots, ∃ archive, slot = .terminal archive
  literal_original_claims : (nativeAccountFace done).rootRead.current.slots.map (Epoch.Finance.slotClaim input depth count) =
    (before source).current.slots.map (Epoch.Finance.slotClaim input depth count)
  entire_original_history : (before source).current.history <+: (nativeAccountFace done).rootRead.current.history
  no_unpaid_original_principal : ∀ instrument debtor holder, Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ledgerClaims input depth count
    (nativeAccountFace done).rootRead.current instrument debtor holder = 0
  whole_original_root_ledger : Evolving.History.ClosedAt (position source).native (2 * (plan source).length)
  productive_paid : (done).rows.productive.progressBudget = 0
  gross_paid : (done).rows.gross.progressBudget = 0
  no_capital_root_face : Global.NoCapital (done).handlerFace.rootRead
  no_pending_native_head : ¬ Public.Inquiry.HasWork (done).frame (done).actual.actual
  original_reader_selected : (completedPosition source resources).actual.proposal (reader source) =
    oldReader (completedPosition source resources).actual.readerCursor (completedPosition source resources).actual.actual.account
  next_raw_action_selected :
    (Factory.Direct.state (done).frame (done).reader (done).visit (done).actual (done).authority).compileInquiry PUnit.unit =
      .actualAction (Factory.Direct.rawCore (done).frame (done).reader (done).visit (done).actual (done).authority
        (completedPosition source resources).ready)
  actual_living_next : ((done).advance).inquiry.erase = (RootInquiryProcessNode.answered (done).inquiry PUnit.unit).erase ∧
    (RootInquiryProcessNode.active (done).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
      (RootInquiryProcessNode.active (done).advance.inquiry)

theorem the_original_current_clears_its_entire_native_ledger_and_continues : CompleteAt source resources where
  source_root_preserved := the_source_installer_extends_the_same_current_root source
  actual_selected_history := the_whole_clearing_is_the_original_selected_root_history source resources
  root_account_literal := the_financial_readout_is_the_same_current_root_account _
  every_original_slot_archived := every_original_slot_is_archived_in_the_actual_root source resources
  literal_original_claims := (the_root_keeps_the_entire_original_native_ledger source resources).1
  entire_original_history := (the_root_keeps_the_entire_original_native_ledger source resources).2
  no_unpaid_original_principal := the_root_has_no_unpaid_original_principal source resources
  whole_original_root_ledger := Evolving.History.the_source_generates_its_whole_ledger_evolving_closure _ _
  productive_paid := (done).rows.productive_zero
  gross_paid := (done).rows.gross_zero
  no_capital_root_face := Evolving.NativeCurrent.the_actual_root_interpreter_excludes_every_capital_relation done
  no_pending_native_head := (completedPosition source resources).ready
  original_reader_selected := the_original_reader_is_selected_after_the_finite_plan source resources
  next_raw_action_selected := the_ready_root_really_compiles_its_next_raw_action done (completedPosition source resources).ready
  actual_living_next := Evolving.NativeCurrent.advance_is_the_actual_source_successor done

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment
