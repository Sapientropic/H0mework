import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Evidence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Service

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped
open Institutions.Capitalism.Universal.Source.Program

def originalIndex (slot : Slot) : source.Slot := ⟨slot.val,slot.isLt⟩
def originalPayment (slot : Slot) := actualPayment 2 (by decide) (originalIndex slot)

private theorem slot_ext (left right : ServiceSlot Party Good)
    (actor : left.bearer = right.bearer) (goods : left.goods = right.goods) (kind : left.purpose = right.purpose) :
    left = right := by cases left; cases right; simp_all

theorem original_claim (slot : Slot) : source.seed.slot (originalIndex slot) = claim slot := by
  rcases slot with ⟨slot,bound⟩
  interval_cases slot <;> apply slot_ext <;> decide +kernel +revert

private theorem operation_of_match (operation : Operation Party Good Technology Unit)
    (actor : Party) (goods : Bundle Good) (kind : Use)
    (matched : Institutions.Capitalism.Universal.Exit.Necessity.UseMatches operation actor goods kind) :
    operation = .use actor goods kind := by
  cases operation <;> simp_all [Institutions.Capitalism.Universal.Exit.Necessity.UseMatches]

theorem original_request (slot : Slot) : (originalPayment slot).item.request = serviceRequest slot := by
  have identity : (originalPayment slot).item.request.signer = bearer slot ∧
      (originalPayment slot).item.request.consents = [] ∧
      (originalPayment slot).item.request.purpose = .common ∧ (originalPayment slot).item.request.gates = [] := by
    rcases slot with ⟨slot,bound⟩
    interval_cases slot <;> decide +kernel +revert
  have aligned := (originalPayment slot).use
  rw [original_claim] at aligned
  have operation := operation_of_match _ _ _ _ aligned
  generalize (originalPayment slot).item.request = request at identity operation ⊢
  rcases request with ⟨signer,consents,purpose,gates,kind⟩
  simp only at identity operation
  rcases identity with ⟨rfl,rfl,rfl,rfl⟩
  subst kind
  rfl

def originalEvidence (slot : Slot) : Evidence :=
  let payment := originalPayment slot
  ⟨some ⟨slot.val,0⟩,some ⟨slot.val,payment.visit.ordinal,payment.item.index,
    min 1 (payment.item.before.stock (bearer slot) (good slot)),payment.visit.before.clock,payment.visit.after.clock⟩⟩

def Origin (slot : Slot) (evidence : Evidence) : Prop :=
  ∃ item ∈ (visitData 1).items, item.request = serviceRequest slot ∧
    (∀ payment, evidence.payment = some payment →
      payment.available ≤ item.before.stock (bearer slot) (good slot) ∧
      payment.start = (visitData 1).before.clock ∧ payment.finish = (visitData 1).after.clock)

theorem original_evidence_has_origin (slot : Slot) : Origin slot (originalEvidence slot) := by
  have same := (actual_payment_is_the_original_occurrence 2 (by decide) (originalIndex slot)).1
  change (originalPayment slot).visit = visitData 1 at same
  refine ⟨(originalPayment slot).item,?_,original_request slot,?_⟩
  · have inside := (originalPayment slot).original_item
    rw [same] at inside
    exact inside
  · intro payment equal
    have aligned := Option.some.inj equal
    subst payment
    exact ⟨min_le_right _ _,congrArg (fun visit : VisitData => visit.before.clock) same,
      congrArg (fun visit : VisitData => visit.after.clock) same⟩

theorem restrict_has_origin (slot : Slot) (allowed : List Field) (evidence : Evidence) (bound : Origin slot evidence) :
    Origin slot (restrict allowed evidence) := by
  obtain ⟨item,inside,request,projection⟩ := bound
  refine ⟨item,inside,request,?_⟩
  intro payment same
  by_cases permitted : BoundedDisclosure.Field.payment ∈ allowed
  · exact projection payment (by simpa [restrict,permitted] using same)
  · simp [restrict,permitted] at same

theorem trace_verifies_original (slot : Slot) (evidence : Evidence) (bound : Origin slot evidence)
    (accepted : traceCheck slot evidence = .verified) : source.ActualSlotPaid 1 (originalIndex slot) := by
  obtain ⟨payment,present,_slot,_visit,_row,stock,early,late⟩ := trace_sound slot evidence accepted
  obtain ⟨item,inside,request,projection⟩ := bound
  obtain ⟨balance,start,finish⟩ := projection payment present
  apply (source.prefix_payment_is_actual 1 (originalIndex slot)).mp
  refine ⟨?_,?_,Or.inr ⟨item,inside,?_,?_⟩⟩
  · change 1 ≤ (visitData 1).before.clock; exact start ▸ early
  · change (visitData 1).after.clock ≤ 12; exact finish ▸ late
  · rw [request]; exact (service_valid_iff _ _).mpr (stock.trans balance)
  · rw [request,original_claim]; exact ⟨rfl,rfl,rfl⟩

theorem lifecycle_verifies_original (slot : Slot) (evidence : Evidence) (bound : Origin slot evidence)
    (accepted : lifecycleCheck slot evidence = .verified) : source.ActualSlotPaid 1 (originalIndex slot) := by
  obtain ⟨_admission,payment,present,_slot,_visit,_row,stock,early,late⟩ := lifecycle_sound slot evidence accepted
  obtain ⟨item,inside,request,projection⟩ := bound
  obtain ⟨balance,start,finish⟩ := projection payment present
  apply (source.prefix_payment_is_actual 1 (originalIndex slot)).mp
  refine ⟨?_,?_,Or.inr ⟨item,inside,?_,?_⟩⟩
  · change 1 ≤ (visitData 1).before.clock; exact start ▸ early
  · change (visitData 1).after.clock ≤ 12; exact finish ▸ late
  · rw [request]; exact (service_valid_iff _ _).mpr (stock.trans balance)
  · rw [request,original_claim]; exact ⟨rfl,rfl,rfl⟩

theorem every_original_slot_passes (slot : Slot) :
    traceCheck slot (originalEvidence slot) = .verified ∧ lifecycleCheck slot (originalEvidence slot) = .verified := by
  rcases slot with ⟨slot,bound⟩
  interval_cases slot <;> decide +kernel +revert

def nativeReplay (slot : Slot) : (OutstandingSource.NativeService.process source).Run
    (ResponsibilityLifecycle.ResponsibilityState.empty (OutstandingSource.NativeService.V source))
    (OutstandingSource.NativeService.reviewEdge source (originalIndex slot) 0).target :=
  .step (.step .nil (OutstandingSource.NativeService.admissionEdge source (originalIndex slot)))
    (OutstandingSource.NativeService.reviewEdge source (originalIndex slot) 0)

theorem second_replay_is_the_original_native_review (slot : Slot) (evidence : Evidence) (bound : Origin slot evidence)
    (accepted : lifecycleCheck slot evidence = .verified) :
    ∃ archive, (OutstandingSource.NativeService.reviewEdge source (originalIndex slot) 0).target.slots[0]? =
      some (.terminal archive) :=
  OutstandingSource.NativeService.paid_has_terminal_receipt source (originalIndex slot) 0
    (lifecycle_verifies_original slot evidence bound accepted)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped
