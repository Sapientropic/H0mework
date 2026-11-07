import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure.Carrier
import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure.Evidence

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure
open Institutions.Capitalism.Universal.Source.Program

theorem original_slot_is_the_public_claim : Cell.source.seed.slot originalSlot = publicClaim := rfl

private theorem matched_operation (operation : Operation Party Good Technology Unit)
    (matched : Institutions.Capitalism.Universal.Exit.Necessity.UseMatches operation 0 [(.life,1)] .necessity) :
    operation = .use 0 [(.life,1)] .necessity := by
  cases operation <;> simp_all [Institutions.Capitalism.Universal.Exit.Necessity.UseMatches]

theorem original_request : originalPayment.item.request = necessity 0 := by
  have fields : originalPayment.item.request.signer = 0 ∧ originalPayment.item.request.consents = [] ∧
      originalPayment.item.request.purpose = .common ∧ originalPayment.item.request.gates = [] := by decide +kernel
  have operation := matched_operation originalPayment.item.request.operation originalPayment.use
  generalize originalPayment.item.request = request at fields operation ⊢
  rcases request with ⟨signer,consents,purpose,gates,kind⟩
  simp only at fields operation
  rcases fields with ⟨rfl,rfl,rfl,rfl⟩
  subst kind
  rfl

def originalEvidence : Evidence :=
  ⟨some ⟨originalSlot.val,0⟩, some ⟨originalPayment.visit.ordinal,originalPayment.item.index,
    min 1 (originalPayment.item.before.stock 0 .life),
    originalPayment.visit.before.clock,originalPayment.visit.after.clock⟩⟩

/-- Provenance is a server-side proposition. It is not a packet field or verifier argument. -/
def Origin (evidence : Evidence) : Prop :=
  ∃ item ∈ (Audit.visitData 1).items, item.request = necessity 0 ∧
    (∀ payment, evidence.payment = some payment →
      payment.available ≤ item.before.stock 0 .life ∧
      payment.start = (Audit.visitData 1).before.clock ∧
      payment.finish = (Audit.visitData 1).after.clock)

theorem original_evidence_has_origin : Origin originalEvidence := by
  refine ⟨originalPayment.item, ?_, original_request, ?_⟩
  · have inside := originalPayment.original_item
    rw [original_delivery_has_its_original_occurrence.1] at inside
    exact inside
  · intro payment same
    have equal := Option.some.inj same
    subst payment
    exact ⟨min_le_right _ _,
      congrArg (fun visit : Audit.VisitData => visit.before.clock) original_delivery_has_its_original_occurrence.1,
      congrArg (fun visit : Audit.VisitData => visit.after.clock) original_delivery_has_its_original_occurrence.1⟩

theorem restrict_has_origin (fields : List Field) (evidence : Evidence) (bound : Origin evidence) :
    Origin (restrict fields evidence) := by
  obtain ⟨item,inside,request,projection⟩ := bound
  refine ⟨item,inside,request,?_⟩
  intro payment same
  by_cases permitted : Field.payment ∈ fields
  · exact projection payment (by simpa [restrict, permitted] using same)
  · simp [restrict, permitted] at same

theorem scoped_conditions_prove_the_original_payment (evidence : Evidence)
    (bound : Origin evidence) (checked : Sufficient evidence) :
    Cell.source.ActualSlotPaid 1 originalSlot := by
  obtain ⟨item,inside,request,projection⟩ := bound
  obtain ⟨admission,payment,_admitted,present,_slot,_registration,_visit,_row,stock,early,late⟩ := checked
  obtain ⟨balance,start,finish⟩ := projection payment present
  apply (Cell.source.prefix_payment_is_actual 1 originalSlot).mp
  refine ⟨?_,?_,Or.inr ⟨item,inside,?_,?_⟩⟩
  · change 1 ≤ (Audit.visitData 1).before.clock
    exact start ▸ early
  · change (Audit.visitData 1).after.clock ≤ 12
    exact finish ▸ late
  · rw [request]
    exact (original_use_valid_iff _).mpr (stock.trans balance)
  · rw [request, original_slot_is_the_public_claim]
    exact ⟨rfl,rfl,rfl⟩

theorem trace_verifies_original_delivery (evidence : Evidence) (bound : Origin evidence)
    (checked : traceCheck evidence = .verified) : Cell.source.ActualSlotPaid 1 originalSlot :=
  scoped_conditions_prove_the_original_payment evidence bound (trace_sound evidence checked)

theorem lifecycle_verifies_original_delivery (evidence : Evidence) (bound : Origin evidence)
    (checked : lifecycleCheck evidence = .verified) : Cell.source.ActualSlotPaid 1 originalSlot := by
  obtain ⟨admission,payment,_admitted,present,_slot,_registration,_visit,_row,stock,early,late⟩ :=
    lifecycle_sound evidence checked
  obtain ⟨item,inside,request,projection⟩ := bound
  obtain ⟨balance,start,finish⟩ := projection payment present
  apply (Cell.source.prefix_payment_is_actual 1 originalSlot).mp
  refine ⟨?_,?_,Or.inr ⟨item,inside,?_,?_⟩⟩
  · change 1 ≤ (Audit.visitData 1).before.clock
    exact start ▸ early
  · change (Audit.visitData 1).after.clock ≤ 12
    exact finish ▸ late
  · rw [request]
    exact (original_use_valid_iff _).mpr (stock.trans balance)
  · rw [request, original_slot_is_the_public_claim]
    exact ⟨rfl,rfl,rfl⟩

theorem both_scoped_clients_accept :
    traceCheck originalEvidence = .verified ∧ lifecycleCheck originalEvidence = .verified := by
  decide +kernel

def nativeFulfillment : OutstandingSource.NativeService.FulfilledAt Cell.source
    ⟨originalSlot,1⟩ originalSlot originalSlot :=
  ⟨rfl,rfl,OutstandingSource.NativeService.visitReceipt Cell.source originalSlot 0,
    lifecycle_verifies_original_delivery originalEvidence original_evidence_has_origin
      both_scoped_clients_accept.2⟩

def nativeReplay : (OutstandingSource.NativeService.process Cell.source).Run
    (ResponsibilityLifecycle.ResponsibilityState.empty (OutstandingSource.NativeService.V Cell.source))
    (OutstandingSource.NativeService.reviewEdge Cell.source originalSlot 0).target :=
  .step (.step .nil (OutstandingSource.NativeService.admissionEdge Cell.source originalSlot))
    (OutstandingSource.NativeService.reviewEdge Cell.source originalSlot 0)

theorem lifecycle_projects_actual_admission_and_review :
    originalEvidence.admission = some
      ⟨(OutstandingSource.NativeService.admissionPayload Cell.source originalSlot).sourceEvent.index.val,
        (OutstandingSource.NativeService.admissionPayload Cell.source originalSlot).sourceEvent.ordinal⟩ ∧
    (originalEvidence.payment.map PaymentSlice.visit) = some
      (OutstandingSource.NativeService.reviewSource Cell.source
        (OutstandingSource.NativeService.review Cell.source originalSlot 0)).ordinal := by decide +kernel

theorem second_replay_closes_the_original_native_review (evidence : Evidence) (bound : Origin evidence)
    (checked : lifecycleCheck evidence = .verified) :
    ∃ archive, (OutstandingSource.NativeService.reviewEdge Cell.source originalSlot 0).target.slots[0]? =
      some (.terminal archive) :=
  OutstandingSource.NativeService.paid_has_terminal_receipt Cell.source originalSlot 0
    (lifecycle_verifies_original_delivery evidence bound checked)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.BoundedDisclosure
