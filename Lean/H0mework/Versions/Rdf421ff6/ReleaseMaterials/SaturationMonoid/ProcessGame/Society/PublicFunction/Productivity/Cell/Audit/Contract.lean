import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Service
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Cuts
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Seed
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Finance

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open OutstandingSource.NativeService

structure Certificate (count : Nat) where
  registered : 2 ≤ count
  trace_replay : traceCheck (visits count) = true
  native_replay : nativeCheck count = true
  payment : ∀ index : source.Slot, TracePayment (visits count) index
  payment_generated : payment = actualPayment count registered
  native : ∀ index : source.Slot, Prefix source index (count - 1)
  native_generated : native = fun index => historyAt source index (count - 1)
  native_terminal : ∀ index, (native index).state.TerminalAt 0
  native_first_archive : ∀ index, (native index).state = (historyAt source index 1).state
  native_history : ∀ index, (native index).state.history = (native index).run.events
  cuts_checked : floorCheck count = true
  every_cut_floor : ∀ item ∈ Feedback.receipts count, ∀ actor,
    livingFloor item.before actor ∧ livingFloor (law.step item.before item.request) actor
  every_cut_inventory : ∀ item ∈ Feedback.receipts count, ∀ actor ∉ actors count, ∀ good,
    item.before.stock actor good = 0 ∧ (law.step item.before item.request).stock actor good = 0
  seeded_addresses_survive : count ≤ 19 → ∀ item ∈ Feedback.receipts count, ∀ actor,
    0 < item.before.stock actor .seed → 0 < (law.step item.before item.request).stock actor .seed
  seeded_bearers_survive_frames : count ≤ 19 → ∀ start later, start + later ≤ count → ∀ actor,
    0 < (source.currentAt start).stock actor .seed → 0 < (source.currentAt (start + later)).stock actor .seed
  self_signed_debits : ∀ item ∈ Feedback.receipts count, law.Valid item.before item.request →
    ∀ entry ∈ law.debit item.before item.request, entry.1.1 = item.request.signer
  inventory : ∀ actor good, Feedback.stockFromReceipts count actor good = (source.currentAt count).stock actor good
  finance : Financial.BalanceConservation.ledgerClaims source.input (Finance.account count).current =
    (source.currentAt count).claims
  financial_run : (Financial.process source.input).Run (Finance.account 0).current (Finance.account count).current
  original_issues : (Finance.account 2).current.slots.map (Financial.slotClaim source.input) <+:
    (Finance.account count).current.slots.map (Financial.slotClaim source.input)
  financial_history : (Finance.account 2).current.history <+: (Finance.account count).current.history
  original_task_rows : ∀ depth, depth + 2 ≤ count →
    ProgrammeLedger.transferReceiptOf source.input (source.taskWrite depth).2 = some (source.writtenReceipt depth)
  next_dispatch : (source.actualExecution (count - 1)).submitted = (Feedback.respond (source.currentAt count)).word

def certifyCheckedPrefix (count : Nat) (started : 2 ≤ count) (safe : floorCheck count = true) :
    Certificate count where
  registered := started
  trace_replay := (both_service_replays_accept count started).1
  native_replay := (both_service_replays_accept count started).2
  payment := actualPayment count started
  payment_generated := rfl
  native := fun index => historyAt source index (count - 1)
  native_generated := rfl
  native_terminal := fun index => (independent_native_archive_keeps_the_first_receipt count started index).2.1
  native_first_archive := fun index => (independent_native_archive_keeps_the_first_receipt count started index).1
  native_history := fun index => (independent_native_archive_keeps_the_first_receipt count started index).2.2
  cuts_checked := safe
  every_cut_floor := floor_check_covers_every_participant count safe
  every_cut_inventory := every_actual_cut_has_complete_inventory count
  seeded_addresses_survive := every_earlier_prefix_keeps_seeded_addresses count
  seeded_bearers_survive_frames := fun within start later bound =>
    actual_seeded_bearer_survives_later_frames start later (by omega)
  self_signed_debits := fun item _inside valid => valid_debits_only_the_signer _ _ valid
  inventory := Feedback.receipt_consumer_matches_every_actor count
  finance := Finance.all_native_positions_are_the_actual_claims count
  financial_run := by simpa only [Nat.zero_add] using Finance.continuation 0 count
  original_issues := by
    have same : 2 + (count - 2) = count := by omega
    have kept := (Finance.original_issues_and_native_history_survive 2 (count - 2)).1
    rw [same] at kept
    exact kept
  financial_history := by
    have same : 2 + (count - 2) = count := by omega
    have kept := (Finance.original_issues_and_native_history_survive 2 (count - 2)).2
    rw [same] at kept
    exact kept
  original_task_rows := fun depth _ => source.receipt_is_in_original_task_write depth
  next_dispatch := continuation_is_actual count started

inductive Result (count : Nat)
  | beforeRegistration (early : count < 2)
  | violated (cut : CutViolation (Feedback.receipts count) (actors count))
  | certified (certificate : Certificate count)

def generate (count : Nat) : Result count :=
  if started : 2 ≤ count then
    if safe : floorCheck count = true then .certified (certifyCheckedPrefix count started safe)
    else
      let failed : floorCheck count = false := Bool.eq_false_iff.mpr safe
      .violated ((violations (Feedback.receipts count) (actors count)).head
        (List.isEmpty_eq_false_iff.mp (failed_floor_check_has_concrete_cut _ _ failed)))
  else .beforeRegistration (by omega)

theorem checked_prefix_is_certified (count : Nat) (started : 2 ≤ count) (safe : floorCheck count = true) :
    generate count = .certified (certifyCheckedPrefix count started safe) := by
  simp only [generate, dif_pos started, dif_pos safe]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit
