import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Effects

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Exit
open OutstandingSource.NativeService
open ResponsibilityLifecycle

structure VisitData where
  ordinal : Nat
  before : Current
  after : Current
  items : List (ExecutionItem Party Good Port Technology Unit)

def visitData (ordinal : Nat) : VisitData :=
  let before := (source.frameAt ordinal).raw
  let word := source.frameWord ordinal (source.frameAt ordinal)
  ⟨ordinal, before, law.next before word, law.rawItems before word⟩

def visits (count : Nat) : List VisitData := (List.range count).map visitData

structure TracePayment (data : List VisitData) (index : source.Slot) where
  visit : VisitData
  original_visit : visit ∈ data
  item : ExecutionItem Party Good Port Technology Unit
  original_item : item ∈ visit.items
  valid : law.Valid item.before item.request
  use : Necessity.UseMatches item.request.operation (source.seed.slot index).bearer
    (source.seed.slot index).goods (source.seed.slot index).purpose
  earliest : source.seed.task.earliest ≤ visit.before.clock
  deadline : visit.after.clock ≤ source.seed.task.deadline

def tracePayments (data : List VisitData) (index : source.Slot) : List (TracePayment data index) :=
  data.attach.flatMap fun visit =>
    if window : source.seed.task.earliest ≤ visit.val.before.clock ∧
        visit.val.after.clock ≤ source.seed.task.deadline then
      visit.val.items.attach.filterMap fun item =>
        if paid : law.Valid item.val.before item.val.request ∧
            Necessity.UseMatches item.val.request.operation (source.seed.slot index).bearer
              (source.seed.slot index).goods (source.seed.slot index).purpose then
          some ⟨visit.val, visit.property, item.val, item.property, paid.1, paid.2, window.1, window.2⟩
        else none
    else []

theorem trace_search_is_complete (data : List VisitData) (index : source.Slot)
    (payment : TracePayment data index) : (tracePayments data index).isEmpty = false := by
  have member : payment ∈ tracePayments data index := by
    unfold tracePayments
    apply List.mem_flatMap.mpr
    refine ⟨⟨payment.visit, payment.original_visit⟩, List.mem_attach _ _, ?_⟩
    rw [dif_pos ⟨payment.earliest, payment.deadline⟩]
    apply List.mem_filterMap.mpr
    refine ⟨⟨payment.item, payment.original_item⟩, List.mem_attach _ _, ?_⟩
    rw [dif_pos ⟨payment.valid, payment.use⟩]
  exact List.isEmpty_eq_false_iff.mpr (fun empty => by rw [empty] at member; cases member)

def traceCheck (data : List VisitData) : Bool :=
  (List.finRange source.seed.task.slots.length).all fun index => !(tracePayments data index).isEmpty

def terminalFlag (state : ResponsibilityLifecycle.ResponsibilityState (V source)) : Bool :=
  match (state.slots[0]? : Option (ObligationSlot (V source))) with
  | some (ObligationSlot.terminal _) => true
  | _ => false

theorem terminal_flag_iff (state : ResponsibilityLifecycle.ResponsibilityState (V source)) :
    terminalFlag state = true ↔ state.TerminalAt 0 := by
  unfold terminalFlag ResponsibilityLifecycle.ResponsibilityState.TerminalAt
  cases selected : state.slots[0]? with
  | none => simp
  | some slot => cases slot <;> simp

def nativeCheck (count : Nat) : Bool :=
  (List.finRange source.seed.task.slots.length).all fun index =>
    terminalFlag (historyAt source index (count - 1)).state

def firstVisitPayments (index : source.Slot) := tracePayments [visitData 1] index

theorem first_visit_has_every_whole_slot (index : source.Slot) :
    (firstVisitPayments index).isEmpty = false := by
  rcases index with ⟨value, bound⟩
  change value < 6 at bound
  interval_cases value <;> decide +kernel +revert

def firstPayment (index : source.Slot) : TracePayment [visitData 1] index :=
  (firstVisitPayments index).head (List.isEmpty_eq_false_iff.mp (first_visit_has_every_whole_slot index))

def actualPayment (count : Nat) (started : 2 ≤ count) (index : source.Slot) :
    TracePayment (visits count) index := by
  let paid := firstPayment index
  refine { paid with original_visit := ?_ }
  have same : paid.visit = visitData 1 := by simpa using paid.original_visit
  rw [same]
  exact List.mem_map.mpr ⟨1, List.mem_range.mpr (by omega), rfl⟩

theorem actual_payment_is_the_original_occurrence (count : Nat) (started : 2 ≤ count) (index : source.Slot) :
    (actualPayment count started index).visit = visitData 1 ∧
    (actualPayment count started index).item ∈ (source.actualExecution 0).interpreted.items ∧
    source.ActualSlotPaid 1 index := by
  let paid := firstPayment index
  have same : paid.visit = visitData 1 := by simpa using paid.original_visit
  refine ⟨same, ?_, ?_⟩
  · have original := paid.original_item
    rw [same] at original
    exact original
  · apply (source.prefix_payment_is_actual 1 index).mp
    unfold OutstandingSource.SlotPaid
    rw [show source.seed.law = law from rfl]
    exact ⟨by simpa only [same, visitData] using paid.earliest,
      by simpa only [same, visitData] using paid.deadline,
      Or.inr ⟨paid.item, by simpa only [same, visitData] using paid.original_item, paid.valid, paid.use⟩⟩

theorem both_service_replays_accept (count : Nat) (started : 2 ≤ count) :
    traceCheck (visits count) = true ∧ nativeCheck count = true := by
  have complete := source.completion_persists 2 (count - 2) original_service_paid
  have frame : 2 + (count - 2) = count := by omega
  rw [frame] at complete
  constructor
  · apply List.all_eq_true.mpr
    intro index _member
    rw [trace_search_is_complete _ index (actualPayment count started index)]
    rfl
  · apply List.all_eq_true.mpr
    intro index _member
    apply (terminal_flag_iff _).mpr
    have same : count - 1 + 1 = count := by omega
    exact (task_complete_iff_all_native_terminal source (count - 1)).mp (same ▸ complete) index

theorem independent_native_archive_keeps_the_first_receipt (count : Nat) (started : 2 ≤ count)
    (index : source.Slot) :
    (historyAt source index (count - 1)).state = (historyAt source index 1).state ∧
    (historyAt source index (count - 1)).state.TerminalAt 0 ∧
    (historyAt source index (count - 1)).state.history =
      (historyAt source index (count - 1)).run.events := by
  refine ⟨?_, (terminal_flag_iff _).mp ?_, native_run_history_is_exact source index (count - 1)⟩
  · rw [show count - 1 = 1 + (count - 2) by omega]
    exact original_service_archives_survive index (count - 2)
  · exact List.all_eq_true.mp (both_service_replays_accept count started).2 index (List.mem_finRange index)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit
