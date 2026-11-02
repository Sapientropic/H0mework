import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeCuts

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService

open ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.Program

section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (originInputs : List (RawEvent Party Good Port Technology Instrument))

private inductive Boundary (obligation : AdmittedObligation (V source originInputs))
  | inherited (event : Review source originInputs obligation)
  | appended (index : source.Slot) (past : List (RawEvent Party Good Port Technology Instrument))
      (word : RawEvent Party Good Port Technology Instrument)
      (content : obligation.content = index) (scope : obligation.scope = index)
      (admission : obligation.admission.sourceEvent.index = index)
  | actual (index : source.Slot)
      (input : Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput source)
      (content : obligation.content = index) (scope : obligation.scope = index)
      (admission : obligation.admission.sourceEvent.index = index)

private def Boundary.event {obligation : AdmittedObligation (V source originInputs)} :
    Boundary source originInputs obligation → Event source originInputs
  | .inherited event => reviewSource source originInputs event
  | .appended index past word _ _ _ => ⟨index, past.length + 2, some (past ++ [word])⟩
  | .actual index input _ _ _ => actualEvent source originInputs index input

private def Boundary.disposition {obligation : AdmittedObligation (V source originInputs)}
    (event : Boundary source originInputs obligation) :
    BoundaryDisposition (V source originInputs) obligation (Boundary.event source originInputs event) := by
  cases event with
  | inherited event => exact SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService.disposition source originInputs event
  | appended index past word content scope admission =>
    if paid : ActualSlotPaid source (past ++ [word]) (past.length + 2) index then
      exact .terminal (.final (.fulfilled ⟨content, scope,
        visitReceiptAt source originInputs index (past.length + 1) (some (past ++ [word])), paid⟩))
    else exact .carry (.maintained ⟨content, scope,
      visitReceiptAt source originInputs index (past.length + 1) (some (past ++ [word])), paid⟩)
  | actual index input content scope admission =>
    if paid : input.Paid index then
      exact .terminal (.final (.fulfilled ⟨content, scope, actualReceipt source originInputs index input, paid⟩))
    else exact .carry (.maintained ⟨content, scope, actualReceipt source originInputs index input, paid⟩)

def threadProcess : NativeResponsibilityProcess (V source originInputs) where
  AdmissionEvent := source.Slot
  admissionPayload := admissionPayload source originInputs
  BoundaryEvent := Boundary source originInputs
  boundarySource := Boundary.event source originInputs
  boundary_anchor_eq := by
    intro obligation event
    cases event with
    | inherited event => exact (process source originInputs).boundary_anchor_eq event
    | appended index past word content scope admission =>
      change MinimalRegistrableSourceAnchor.canonical index index =
        MinimalRegistrableSourceAnchor.canonical obligation.admission.sourceEvent.index obligation.admission.sourceEvent.index
      rw [admission]
    | actual index input content scope admission =>
      change MinimalRegistrableSourceAnchor.canonical index index =
        MinimalRegistrableSourceAnchor.canonical obligation.admission.sourceEvent.index obligation.admission.sourceEvent.index
      rw [admission]
  boundary_incidence_eq := by
    intro obligation event
    cases event with
    | inherited event => exact (process source originInputs).boundary_incidence_eq event
    | appended index past word content scope admission => exact admission.symm
    | actual index input content scope admission => exact admission.symm
  boundaryDisposition := Boundary.disposition source originInputs
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

/-- This is the existing process's boundary operation on the original live
obligation. The Physical source decides carry or fulfilment itself. -/
def actualEdge (state : (threadProcess source originInputs).GeneratedState)
    (index : source.Slot) (address : Fin state.current.slots.length)
    (present : state.current.slots.get address = .live (obligation source originInputs index))
    (input : Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput source) :
    (threadProcess source originInputs).Edge state.current :=
  .cross address (obligation source originInputs index) present (.actual index input rfl rfl rfl)

def advanceActual (state : (threadProcess source originInputs).GeneratedState)
    (index : source.Slot) (address : Fin state.current.slots.length)
    (present : state.current.slots.get address = .live (obligation source originInputs index))
    (input : Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput source) :=
  state.step (threadProcess source originInputs) (actualEdge source originInputs state index address present input)

def actualRun (state : (threadProcess source originInputs).GeneratedState)
    (index : source.Slot) (address : Fin state.current.slots.length)
    (present : state.current.slots.get address = .live (obligation source originInputs index))
    (input : Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput source) :
    (threadProcess source originInputs).Run state.current
      (advanceActual source originInputs state index address present input).current :=
  .step .nil (actualEdge source originInputs state index address present input)

def actualArchive (index : source.Slot)
    (input : Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput source)
    (paid : input.Paid index) : TerminalArchive (V source originInputs) :=
  ⟨obligation source originInputs index, actualEvent source originInputs index input,
    .fulfilled ⟨rfl, rfl, actualReceipt source originInputs index input, paid⟩⟩

theorem actual_paid_generates_original_terminal
    (state : (threadProcess source originInputs).GeneratedState)
    (index : source.Slot) (address : Fin state.current.slots.length)
    (present : state.current.slots.get address = .live (obligation source originInputs index))
    (input : Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput source)
    (paid : input.Paid index) :
    (advanceActual source originInputs state index address present input).current.slots[address.val]? =
      some (.terminal (actualArchive source originInputs index input paid)) := by
  have target := NativeResponsibilityProcess.cross_target_slot (P := threadProcess source originInputs)
    address (obligation source originInputs index) present (Boundary.actual index input rfl rfl rfl)
  simpa only [advanceActual, actualEdge, NativeResponsibilityProcess.GeneratedState.step,
    threadProcess, Boundary.disposition, Boundary.event, actualArchive, dif_pos paid,
    BoundaryDisposition.targetSlot] using target

theorem actual_unpaid_keeps_original_live
    (state : (threadProcess source originInputs).GeneratedState)
    (index : source.Slot) (address : Fin state.current.slots.length)
    (present : state.current.slots.get address = .live (obligation source originInputs index))
    (input : Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.SourceInput source)
    (unpaid : ¬ input.Paid index) :
    (advanceActual source originInputs state index address present input).current.slots[address.val]? =
      some (.live (obligation source originInputs index)) := by
  have target := NativeResponsibilityProcess.cross_target_slot (P := threadProcess source originInputs)
    address (obligation source originInputs index) present (Boundary.actual index input rfl rfl rfl)
  simpa only [advanceActual, actualEdge, NativeResponsibilityProcess.GeneratedState.step,
    threadProcess, Boundary.disposition, Boundary.event, dif_neg unpaid,
    BoundaryDisposition.targetSlot, ActiveCarryDisposition.target] using target

private def inheritRun {first last : ResponsibilityState (V source originInputs)} :
    (process source originInputs).Run first last → (threadProcess source originInputs).Run first last
  | .nil => .nil
  | .step prior (.admit event) => .step (inheritRun prior) (.admit event)
  | .step prior (.cross slot obligation present event) =>
      .step (inheritRun prior) (.cross slot obligation present (.inherited event))
  | .step _ (.reopen _ _ _ impossible) => nomatch impossible

private theorem inheritRun_events {first last : ResponsibilityState (V source originInputs)}
    (run : (process source originInputs).Run first last) : (inheritRun source originInputs run).events = run.events := by
  induction run with
  | nil => rfl
  | step prior edge ih =>
    cases edge with
    | admit event => simp only [inheritRun, NativeResponsibilityProcess.Run.events]; rw [ih]; rfl
    | cross slot obligation present event => simp only [inheritRun, NativeResponsibilityProcess.Run.events]; rw [ih]; rfl
    | reopen slot archive present impossible => exact nomatch impossible

inductive ThreadShape (index : source.Slot) (inputs : List (RawEvent Party Good Port Technology Instrument))
    (state : ResponsibilityState (V source originInputs)) : Type
  | live (unpaid : (frameAt source inputs (inputs.length + 2)).payments index = none)
      (slots : state.slots = [.live (obligation source originInputs index)])
  | terminal (archive : TerminalArchive (V source originInputs)) (paid : Nat)
      (recorded : (frameAt source inputs (inputs.length + 2)).payments index = some paid)
      (original : archive.obligation = obligation source originInputs index)
      (slots : state.slots = [.terminal archive])

structure Thread (index : source.Slot) (inputs : List (RawEvent Party Good Port Technology Instrument)) where
  private mk ::
  state : (threadProcess source originInputs).GeneratedState
  shape : ThreadShape source originInputs index inputs state.current

variable {originInputs}

def Thread.initial (index : source.Slot) : Thread source originInputs index originInputs := by
  let actual := historyAt source originInputs index (originInputs.length + 1)
  refine ⟨⟨actual.state, inheritRun source originInputs actual.run⟩, ?_⟩
  cases actual.shape with
  | live unpaid slots => exact .live unpaid slots
  | terminal depth paid recorded slots => exact .terminal (paidArchive source originInputs index depth paid) (depth + 1) recorded rfl slots

/-- Only the shared bootstrap and original request have happened here.
The vocabulary may retain its original inputs while later payments come
from the actual appended words. -/
def Thread.beginAtBootstrap (index : source.Slot) : Thread source originInputs index [] := by
  let actual := historyAt source originInputs index 1
  have common : frameAt source originInputs 2 = frameAt source [] 2 := by
    simpa only [frameAt,List.nil_append] using
      congrArg ExecutionPrefix.frame
        (OutstandingSource.History.extending_inputs_preserves_its_executed_prefix source [] originInputs 2 (by simp))
  refine ⟨⟨actual.state,inheritRun source originInputs actual.run⟩,?_⟩
  cases actual.shape with
  | live unpaid slots => exact .live (by simpa only [List.length_nil,zero_add,← common] using unpaid) slots
  | terminal depth paid recorded slots =>
      exact .terminal (paidArchive source originInputs index depth paid) (depth+1)
        (by simpa only [List.length_nil,zero_add,← common] using recorded) rfl slots

theorem Thread.initial_preserves_the_entire_original_state (index : source.Slot) :
    (Thread.initial source (originInputs := originInputs) index).state.current =
      (historyAt source originInputs index (originInputs.length + 1)).state := rfl

theorem Thread.initial_preserves_every_original_run_event (index : source.Slot) :
    (Thread.initial source (originInputs := originInputs) index).state.generated.events =
      (historyAt source originInputs index (originInputs.length + 1)).run.events :=
  inheritRun_events source originInputs _

variable {inputs : List (RawEvent Party Good Port Technology Instrument)}

def appended (word : RawEvent Party Good Port Technology Instrument) := inputs ++ [word]

theorem common_payments (word : RawEvent Party Good Port Technology Instrument) :
    (frameAt source (appended (inputs := inputs) word) (inputs.length + 2)).payments =
      (frameAt source inputs (inputs.length + 2)).payments :=
  congrArg (fun past : ExecutionPrefix source => past.frame.payments)
    (OutstandingSource.History.extending_inputs_preserves_its_executed_prefix source inputs [word] _ (Nat.le_refl _))

def remoteArchive (index : source.Slot) (word : RawEvent Party Good Port Technology Instrument)
    (paid : ActualSlotPaid source (appended (inputs := inputs) word) (inputs.length + 2) index) :
    TerminalArchive (V source originInputs) :=
  ⟨obligation source originInputs index, ⟨index, inputs.length + 2, some (appended (inputs := inputs) word)⟩,
    .fulfilled ⟨rfl, rfl, visitReceiptAt source originInputs index (inputs.length + 1) (some (appended (inputs := inputs) word)), paid⟩⟩

def Thread.advance {index : source.Slot} (thread : Thread source originInputs index inputs)
    (word : RawEvent Party Good Port Technology Instrument) : Thread source originInputs index (appended (inputs := inputs) word) := by
  rcases thread with ⟨state, shape⟩
  cases shape with
  | live unpaid slots =>
    let address : Fin state.current.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ _⟩
    have present : state.current.slots.get address = .live (obligation source originInputs index) := by simp [slots, address]
    let event : (threadProcess source originInputs).Edge state.current :=
      .cross address (obligation source originInputs index) present (.appended index inputs word rfl rfl rfl)
    have prior : (frameAt source (appended (inputs := inputs) word) (inputs.length + 2)).payments index = none := by
      rw [common_payments source word]; exact unpaid
    by_cases paid : ActualSlotPaid source (inputs ++ [word]) (inputs.length + 2) index
    · refine ⟨state.step (threadProcess source originInputs) event, .terminal (remoteArchive source (inputs := inputs) index word paid) (inputs.length + 2) ?_ rfl ?_⟩
      · simpa only [appended, List.length_append, List.length_singleton, Nat.add_assoc] using
          next_paid source (appended (inputs := inputs) word) index (inputs.length + 2) prior paid
      · simp [event, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
          threadProcess, Boundary.disposition, Boundary.event, paid, slots, address, remoteArchive, appended, BoundaryDisposition.targetSlot]
    · refine ⟨state.step (threadProcess source originInputs) event, .live ?_ ?_⟩
      · simpa only [appended, List.length_append, List.length_singleton, Nat.add_assoc] using
          next_unpaid source (appended (inputs := inputs) word) index (inputs.length + 2) prior paid
      · simp [event, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
          threadProcess, Boundary.disposition, Boundary.event, paid, slots, address, BoundaryDisposition.targetSlot,
          ActiveCarryDisposition.target]
  | terminal archive paid recorded original slots =>
    refine ⟨state, .terminal archive paid ?_ original slots⟩
    have prior : (frameAt source (appended (inputs := inputs) word) (inputs.length + 2)).payments index = some paid := by
      rw [common_payments source word]; exact recorded
    simpa only [appended, List.length_append, List.length_singleton, Nat.add_assoc] using
      OutstandingSource.History.archive_preserved source (appended (inputs := inputs) word) (inputs.length + 2) 1 index paid prior

def Thread.actualRun {index : source.Slot} (thread : Thread source originInputs index inputs)
    (word : RawEvent Party Good Port Technology Instrument) :
    (threadProcess source originInputs).Run thread.state.current (thread.advance source word).state.current := by
  rcases thread with ⟨state, shape⟩
  cases shape with
  | live unpaid slots =>
    dsimp only [Thread.advance]
    split <;> exact .step .nil (.cross _ _ _ _)
  | terminal archive paid recorded original slots => exact .nil

def Thread.extend {index : source.Slot} {inputs : List (RawEvent Party Good Port Technology Instrument)}
    (thread : Thread source originInputs index inputs) :
    (later : List (RawEvent Party Good Port Technology Instrument)) → Thread source originInputs index (inputs ++ later)
  | [] => by simpa only [List.append_nil] using thread
  | word :: later => by
      simpa only [appended,List.append_assoc,List.singleton_append] using
        (thread.advance source word).extend later

def Thread.fromInputs (index : source.Slot) (actualInputs : List (RawEvent Party Good Port Technology Instrument)) :
    Thread source originInputs index actualInputs :=
  (Thread.beginAtBootstrap source index).extend source actualInputs

theorem Thread.native_live_iff_unpaid {index : source.Slot} (thread : Thread source originInputs index inputs) :
    thread.state.current.LiveAt 0 ↔ (frameAt source inputs (inputs.length + 2)).payments index = none := by
  cases thread.shape with
  | live unpaid slots => exact ⟨fun _ => unpaid, fun _ => ⟨obligation source originInputs index, by simp [slots]⟩⟩
  | terminal archive paid recorded original slots =>
    constructor
    · rintro ⟨obligation, present⟩; simp only [slots, List.getElem?_cons_zero] at present; cases present
    · intro unpaid; rw [unpaid] at recorded; cases recorded

theorem Thread.native_terminal_iff_recorded {index : source.Slot} (thread : Thread source originInputs index inputs) :
    thread.state.current.TerminalAt 0 ↔ ∃ paid, (frameAt source inputs (inputs.length + 2)).payments index = some paid := by
  cases thread.shape with
  | live unpaid slots =>
    constructor
    · rintro ⟨archive, present⟩; simp only [slots, List.getElem?_cons_zero] at present; cases present
    · rintro ⟨paid, recorded⟩; rw [unpaid] at recorded; cases recorded
  | terminal archive paid recorded original slots =>
    exact ⟨fun _ => ⟨paid, recorded⟩, fun _ => ⟨archive, by simp [slots]⟩⟩

theorem Thread.terminal_state_is_preserved {index : source.Slot} (thread : Thread source originInputs index inputs)
    (terminal : thread.state.current.TerminalAt 0) (word : RawEvent Party Good Port Technology Instrument) :
    (thread.advance source word).state = thread.state := by
  rcases thread with ⟨state, shape⟩
  cases shape with
  | live unpaid slots =>
    obtain ⟨archive, present⟩ := terminal
    simp only [slots, List.getElem?_cons_zero] at present
    cases present
  | terminal archive paid recorded original slots => rfl

theorem Thread.original_obligation_is_retained {index : source.Slot} (thread : Thread source originInputs index inputs) :
    thread.state.current.slots = [.live (obligation source originInputs index)] ∨
      ∃ archive : TerminalArchive (V source originInputs), thread.state.current.slots = [.terminal archive] ∧
        archive.obligation = obligation source originInputs index := by
  cases thread.shape with
  | live unpaid slots => exact .inl slots
  | terminal archive paid recorded original slots => exact .inr ⟨archive, slots, original⟩

theorem Thread.actual_history {index : source.Slot} (thread : Thread source originInputs index inputs) :
    thread.state.current.history = thread.state.generated.events := thread.state.history_eq

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService
