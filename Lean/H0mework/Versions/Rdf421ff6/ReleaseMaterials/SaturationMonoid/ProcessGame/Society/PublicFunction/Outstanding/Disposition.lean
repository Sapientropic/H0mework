import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.Incoming
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.NativeServiceRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)

/-- Disposition of an original native slot by this actual execution. An old
archive is preserved; a new terminal requires this visit's actual payment. -/
inductive SlotDisposition (depth : Nat) (index : source.Slot) where
  | private archived (paid : Nat)
      (prior : (source.frameAt (depth + 1)).payments index = some paid)
      (next : (source.frameAt (depth + 2)).payments index = some paid)
      (unchanged : (NativeService.historyAt source index (depth + 1)).state =
        (NativeService.historyAt source index depth).state)
  | private fulfilled (prior : (source.frameAt (depth + 1)).payments index = none)
      (payment : source.ActualSlotPaid (depth + 1) index)
      (recorded : (source.frameAt (depth + 2)).payments index = some (depth + 1))
      (terminal : (NativeService.historyAt source index (depth + 1)).state.TerminalAt 0)
  | private retained (prior : (source.frameAt (depth + 1)).payments index = none)
      (unpaid : ¬ source.ActualSlotPaid (depth + 1) index)
      (recorded : (source.frameAt (depth + 2)).payments index = none)
      (live : (NativeService.historyAt source index (depth + 1)).state.LiveAt 0)

def slotDisposition (depth : Nat) (index : source.Slot) : source.SlotDisposition depth index := by
  cases prior : (source.frameAt (depth + 1)).payments index with
  | some paid =>
      exact .archived paid prior (source.recorded_payment_preserved (depth + 1) 1 index paid prior)
        (NativeService.terminal_next_state_is_preserved source index depth
          ((NativeService.native_terminal_iff_recorded source index depth).mpr ⟨paid, prior⟩))
  | none =>
      by_cases payment : source.ActualSlotPaid (depth + 1) index
      · have next := NativeService.next_paid source index (depth + 1) prior payment
        exact .fulfilled prior payment next
          ((NativeService.native_terminal_iff_recorded source index (depth + 1)).mpr ⟨_, next⟩)
      · have next := NativeService.next_unpaid source index (depth + 1) prior payment
        exact .retained prior payment next
          ((NativeService.native_live_iff_unpaid source index (depth + 1)).mpr next)

theorem actual_plan_settles_all_original_slots (depth : Nat)
    (nonempty : source.pendingSlots (source.frameAt (depth + 1)).payments ≠ [])
    (plan : PaidServicePlan source.seed.law (source.currentAt (depth + 1))
      (source.pendingTask (source.frameAt (depth + 1)).payments nonempty)
      (source.seed.actionsAt (source.currentAt (depth + 1))) source.seed.budget)
    (emitted : (source.actualExecution depth).submitted = plan.word) :
    ∀ index, (NativeService.historyAt source index (depth + 1)).state.TerminalAt 0 := by
  intro index
  apply (NativeService.native_terminal_iff_recorded source index (depth + 1)).mpr
  cases prior : (source.frameAt (depth + 1)).payments index with
  | some paid => exact ⟨paid, source.recorded_payment_preserved (depth + 1) 1 index paid prior⟩
  | none =>
      have paid : source.ActualSlotPaid (depth + 1) index := by
        change source.SlotPaid (source.currentAt (depth + 1)) (source.actualExecution depth).submitted index
        rw [emitted]
        exact ⟨plan.sound.1.1, plan.sound.1.2.1,
          plan.pointwise_service (source.seed.slot index) (source.pending_slot_has_original_identity _ index prior)⟩
      exact ⟨depth + 1, NativeService.next_paid source index (depth + 1) prior paid⟩

theorem empty_actual_word_retains_native_slots (depth : Nat)
    (empty : (source.actualExecution depth).submitted = []) (index : source.Slot)
    (unpaid : (source.frameAt (depth + 1)).payments index = none) :
    (NativeService.historyAt source index (depth + 1)).state.LiveAt 0 :=
  (NativeService.native_live_iff_unpaid source index (depth + 1)).mpr
    (source.empty_execution_carries_unpaid depth index unpaid empty)

theorem actual_continuation_word (depth : Nat) :
    (source.actualExecution (depth + 1)).submitted =
      (source.decideAt (source.currentAt (depth + 2)) (source.frameAt (depth + 2)).payments).word := by
  rw [source.actual_execution_word]
  unfold frameWord
  rw [if_neg (by omega), if_neg (by omega), ← (source.canonical_frame (depth + 2)).1]

theorem actual_continuation_report (depth : Nat) :
    (source.writtenReceipt (depth + 1)).val =
      (source.decideAt (source.currentAt (depth + 2)) (source.frameAt (depth + 2)).payments).report := by
  rw [source.written_report_exact]
  unfold reportAt
  rw [source.ordinal_exact, if_neg (by omega)]

/-- Every branch consumes the source's actual decision and settles or carries
its original native slots. Completion refers only to these service slots. -/
inductive PublicContinuationDisposition (depth : Nat) where
  | private complete
      (complete : source.pendingSlots (source.frameAt (depth + 2)).payments = [])
      (word : (source.actualExecution (depth + 1)).submitted =
        (source.completionReport (source.currentAt (depth + 2))).word)
      (report : (source.writtenReceipt (depth + 1)).val =
        source.completionReport (source.currentAt (depth + 2)))
      (settled : ∀ index, (NativeService.historyAt source index (depth + 2)).state.TerminalAt 0)
  | private received (event : source.ReceivedEvent (depth + 1))
  | private paid (nonempty : source.pendingSlots (source.frameAt (depth + 2)).payments ≠ [])
      (plan : PaidServicePlan source.seed.law (source.currentAt (depth + 2))
        (source.pendingTask (source.frameAt (depth + 2)).payments nonempty)
        (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget)
      (word : (source.actualExecution (depth + 1)).submitted = plan.word)
      (report : (source.writtenReceipt (depth + 1)).val =
        .planning source.seed.law (source.currentAt (depth + 2))
          (source.pendingTask (source.frameAt (depth + 2)).payments nonempty)
          (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget (.paid plan))
      (settled : ∀ index, (NativeService.historyAt source index (depth + 2)).state.TerminalAt 0)
  | private physical (nonempty : source.pendingSlots (source.frameAt (depth + 2)).payments ≠ [])
      (obstruction : BoundedPhysicalObstruction source.seed.law (source.currentAt (depth + 2))
        (source.pendingTask (source.frameAt (depth + 2)).payments nonempty)
        (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget)
      (word : (source.actualExecution (depth + 1)).submitted = [])
      (report : (source.writtenReceipt (depth + 1)).val =
        .planning source.seed.law (source.currentAt (depth + 2))
          (source.pendingTask (source.frameAt (depth + 2)).payments nonempty)
          (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget (.physical obstruction))
      (retained : ∀ index, (source.frameAt (depth + 2)).payments index = none →
        (NativeService.historyAt source index (depth + 2)).state.LiveAt 0)
  | private capture (nonempty : source.pendingSlots (source.frameAt (depth + 2)).payments ≠ [])
      (obstruction : CaptureBlockage source.seed.law (source.currentAt (depth + 2))
        (source.pendingTask (source.frameAt (depth + 2)).payments nonempty)
        (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget)
      (word : (source.actualExecution (depth + 1)).submitted = [])
      (report : (source.writtenReceipt (depth + 1)).val =
        .planning source.seed.law (source.currentAt (depth + 2))
          (source.pendingTask (source.frameAt (depth + 2)).payments nonempty)
          (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget (.capture obstruction))
      (retained : ∀ index, (source.frameAt (depth + 2)).payments index = none →
        (NativeService.historyAt source index (depth + 2)).state.LiveAt 0)

def publicDisposition (depth : Nat) : source.PublicContinuationDisposition depth := by
  have emitted := source.actual_continuation_word depth
  have written := source.actual_continuation_report depth
  generalize selected : source.decideAt (source.currentAt (depth + 2))
    (source.frameAt (depth + 2)).payments = decision at emitted written
  cases decision with
  | complete complete =>
      exact .complete complete emitted written (fun index =>
        (NativeService.native_terminal_iff_recorded source index (depth + 2)).mpr
          (source.complete_all_recorded (depth + 3)
            (source.completion_persists (depth + 2) 1 complete) index))
  | received incoming =>
      have generated : source.incoming? (source.currentAt (depth + 2)) = some incoming := by
        unfold decideAt at selected
        split at selected
        · cases selected
          assumption
        · split at selected <;> cases selected
      have present : (source.receivedAt (depth + 1)).isSome = true := by
        obtain ⟨event, found⟩ := source.admitted_input_is_received
          (depth + 1) (by omega) incoming generated
        rw [found]
        rfl
      exact .received ((source.receivedAt (depth + 1)).get present)
  | planning pending outcome =>
      cases outcome with
      | paid plan =>
        exact .paid pending plan emitted written
          (source.actual_plan_settles_all_original_slots (depth + 1) pending plan emitted)
      | physical obstruction =>
        exact .physical pending obstruction emitted written
          (source.empty_actual_word_retains_native_slots (depth + 1) emitted)
      | capture obstruction =>
        exact .capture pending obstruction emitted written
          (source.empty_actual_word_retains_native_slots (depth + 1) emitted)

inductive ContinuationKind where
  | complete | received | paid | physical | capture
  deriving DecidableEq, Repr

variable {source}

inductive SlotDispositionKind where
  | archived | fulfilled | retained
  deriving DecidableEq, Repr

def SlotDisposition.kind {depth : Nat} {index : source.Slot} :
    source.SlotDisposition depth index → SlotDispositionKind
  | .archived .. => .archived
  | .fulfilled .. => .fulfilled
  | .retained .. => .retained

def PublicContinuationDisposition.kind {depth : Nat} : source.PublicContinuationDisposition depth → ContinuationKind
  | .complete .. => .complete
  | .received .. => .received
  | .paid .. => .paid
  | .physical .. => .physical
  | .capture .. => .capture

theorem PublicContinuationDisposition.paid_settles_original_native_task {depth : Nat}
    (disposition : source.PublicContinuationDisposition depth) (paid : disposition.kind = .paid) :
    ∀ index, (NativeService.historyAt source index (depth + 2)).state.TerminalAt 0 := by
  cases disposition <;> simp_all [kind]

theorem PublicContinuationDisposition.blockage_retains_original_native_task {depth : Nat}
    (disposition : source.PublicContinuationDisposition depth)
    (blocked : disposition.kind = .physical ∨ disposition.kind = .capture) :
    ∀ index, (source.frameAt (depth + 2)).payments index = none →
      (NativeService.historyAt source index (depth + 2)).state.LiveAt 0 := by
  cases disposition <;> simp_all [kind]

theorem SlotDisposition.new_terminal_requires_this_actual_payment {depth : Nat} {index : source.Slot}
    (disposition : source.SlotDisposition depth index)
    (unpaid : (source.frameAt (depth + 1)).payments index = none)
    (terminal : (NativeService.historyAt source index (depth + 1)).state.TerminalAt 0) :
    source.ActualSlotPaid (depth + 1) index ∧
      (source.frameAt (depth + 2)).payments index = some (depth + 1) ∧
      ProgrammeLedger.transferReceiptOf source.input (source.taskWrite depth).2 =
        some (source.writtenReceipt depth) := by
  rcases disposition with ⟨paid, prior, next, unchanged⟩ | ⟨prior, payment, recorded, settled⟩ |
    ⟨prior, absent, recorded, live⟩
  · rw [unpaid] at prior
    cases prior
  · exact ⟨payment, recorded, source.receipt_is_in_original_task_write depth⟩
  · obtain ⟨paid, paidAt⟩ := (NativeService.native_terminal_iff_recorded source index (depth + 1)).mp terminal
    rw [recorded] at paidAt
    cases paidAt

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource
