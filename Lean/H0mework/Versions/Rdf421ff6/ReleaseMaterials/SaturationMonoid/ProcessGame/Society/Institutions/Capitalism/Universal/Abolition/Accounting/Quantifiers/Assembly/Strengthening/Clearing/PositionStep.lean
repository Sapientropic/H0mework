import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Position
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Accounts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Position

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {reader : Macro.Raw.Reader input depth count}
  (position : Position input depth count reader)
  (request : Request Party Good Port Technology Instrument)
  (selected : position.actual.proposal reader = .primitive request)
  (noConsents : request.consents = [])
  (valid : (Physical.Public.interpreter input).Valid
    (Physical.Public.stateAt input depth count 0 0 [] position.past).raw request)

private theorem snapshot_past : position.actual.snapshot.past = position.past := by
  unfold past Public.Inquiry.ActualAt.readerCursor
  simp only [Physical.receive,Physical.Prefix.past_readback,List.nil_append]

include selected in
theorem selected_start_is_the_same_original_primitive :
    Factory.Direct.selectedStart position.native.full position.native.sourceActual reader =
      Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.start position.past request := by
  refine (the_current_primitive_uses_the_original_scope_delegate position.native request selected).trans ?_
  change Physical.receive position.actual.snapshot (.primitive request) = _
  unfold Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.start
  rw [← snapshot_past position]
  exact (Physical.Prefix.reconstructs_the_same_cursor (Physical.receive position.actual.snapshot (.primitive request))).symm

include selected noConsents valid

theorem step_records_exactly_this_original_primitive :
    (step position request selected noConsents valid).past = position.past ++ [.primitive request] := by
  have rawPast := the_actual_raw_records_the_original_submitted_primitive position.native request selected position.ready
  change ((position.native.raw position.ready).ordinary).actual.readerCursor.past = _
  refine Eq.trans ?_ rawPast
  unfold Public.Inquiry.ActualAt.readerCursor Public.Inquiry.ActualAt.snapshot
  rw [((position.native.raw position.ready).ordinary).bodyPaid,(position.native.raw position.ready).bodyPaid]
  rfl

theorem step_consumes_the_same_original_native_inventory :
    (step position request selected noConsents valid).actual.actual.account =
      Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.accountAfter input depth count
        position.past [request] position.actual.actual.account := by
  have checked : (Physical.Public.interpreter input).Valid
      (Public.Scope.actualState input depth count 0 0 [] position.actual.snapshot).raw request := by
    rw [raw_state_is_read_from_its_actual_past]
    exact valid
  have account := one_actual_native_step_consumes_the_whole_primitive_account position.native request selected
    position.ready noConsents checked
  change ((position.native.raw position.ready).ordinary).actual.actual.account = _
  refine account.trans ?_
  change Epoch.Finance.consumeVisit input depth count
      (Public.Accounting.tag input depth count 0 0 [] (Factory.Direct.selectedStart position.native.full position.native.sourceActual reader))
      (Public.Accounting.visit input depth count 0 0 [] (Factory.Direct.selectedStart position.native.full position.native.sourceActual reader))
      position.actual.actual.account = _
  unfold Public.Accounting.tag Public.Accounting.visit
  rw [selected_start_is_the_same_original_primitive position request selected]
  rfl

theorem step_of_a_payment_is_two_actual_source_advances
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (settlement : request.operation = .settle instrument debtor holder quantity) :
    (step position request selected noConsents valid).native = position.native.advance.advance := by
  have checked : (Physical.Public.interpreter input).Valid
      (Public.Scope.actualState input depth count 0 0 [] position.actual.snapshot).raw request := by
    rw [raw_state_is_read_from_its_actual_past]
    exact valid
  rw [step_native_is_the_original_raw_and_financial_successor,
    Evolving.NativeCurrent.advance_eq_raw position.native position.ready]
  have pending := the_actual_primitive_must_consume_its_financial_head position.native request selected
    position.ready noConsents checked
  have none := an_actual_settlement_has_no_new_claim_admission position.native request selected
    position.ready noConsents checked instrument debtor holder quantity settlement
  unfold Evolving.NativeCurrent.advance Evolving.NativeCurrent.selected
  rw [dif_pos pending,none]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Position
