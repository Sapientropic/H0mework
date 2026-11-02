import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageDuty

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageDuty

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (cursor : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (emission : Emission cursor vocabulary encoding)

inductive Shape (suffix : List (EventHistory.Stage (code := code)))
    (state : ResponsibilityState (V cursor vocabulary encoding law)) : Type
  | live (unconfirmed : ¬ Acknowledged cursor vocabulary encoding law emission suffix)
      (slots : state.slots = [.live (obligation cursor vocabulary encoding law emission)])
  | terminal (record : TerminalArchive (V cursor vocabulary encoding law))
      (ack : Acknowledged cursor vocabulary encoding law emission suffix)
      (original : record.obligation = obligation cursor vocabulary encoding law emission)
      (slots : state.slots = [.terminal record])

structure Prefix (suffix : List (EventHistory.Stage (code := code))) where
  state : ResponsibilityState (V cursor vocabulary encoding law)
  run : (process cursor vocabulary encoding law).Run (ResponsibilityState.empty _) state
  shape : Shape cursor vocabulary encoding law emission suffix state

def inspect (suffix : List (EventHistory.Stage (code := code)))
    (state : ResponsibilityState (V cursor vocabulary encoding law))
    (run : (process cursor vocabulary encoding law).Run (ResponsibilityState.empty _) state)
    (slots : state.slots = [.live (obligation cursor vocabulary encoding law emission)]) :
    Prefix cursor vocabulary encoding law emission suffix := by
  let address : Fin state.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ 0⟩
  have present : state.slots.get address = .live (obligation cursor vocabulary encoding law emission) := by simp [slots, address]
  let edge : (process cursor vocabulary encoding law).Edge state :=
    .cross address _ present (review cursor vocabulary encoding law emission suffix)
  by_cases ack : Acknowledged cursor vocabulary encoding law emission suffix
  · exact ⟨edge.target, .step run edge, .terminal (archive cursor vocabulary encoding law emission suffix ack) ack rfl (by
      simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition, reviewSource,
        review, dif_pos ack, slots, address, BoundaryDisposition.targetSlot, archive])⟩
  · exact ⟨edge.target, .step run edge, .live ack (by
      simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition, reviewSource,
        review, dif_neg ack, slots, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target])⟩

def initial : Prefix cursor vocabulary encoding law emission [] :=
  let edge : (process cursor vocabulary encoding law).Edge (ResponsibilityState.empty _) := .admit emission
  inspect cursor vocabulary encoding law emission [] edge.target (.step .nil edge) rfl

def advance (oldSuffix newSuffix : List (EventHistory.Stage (code := code))) (continued : oldSuffix <+: newSuffix)
    (prior : Prefix cursor vocabulary encoding law emission oldSuffix) :
    Prefix cursor vocabulary encoding law emission newSuffix := by
  rcases prior with ⟨state, run, shape⟩
  cases shape with
  | live _ slots => exact inspect cursor vocabulary encoding law emission newSuffix state run slots
  | terminal record ack original slots =>
    have nextAck : Acknowledged cursor vocabulary encoding law emission newSuffix := by
      obtain ⟨more, same⟩ := continued
      exact same ▸ acknowledged_is_preserved cursor vocabulary encoding law emission oldSuffix more ack
    exact ⟨state, run, .terminal record nextAck original slots⟩

abbrev History := Sigma (Prefix cursor vocabulary encoding law emission)

def step (prior : History cursor vocabulary encoding law emission) (stage : EventHistory.Stage (code := code)) :
    History cursor vocabulary encoding law emission :=
  ⟨prior.1 ++ [stage], advance cursor vocabulary encoding law emission _ _ (List.prefix_append _ _) prior.2⟩

def runFrom (prior : History cursor vocabulary encoding law emission) :
    List (EventHistory.Stage (code := code)) → History cursor vocabulary encoding law emission
  | [] => prior
  | stage :: tail => runFrom (step cursor vocabulary encoding law emission prior stage) tail

def through (suffix : List (EventHistory.Stage (code := code))) : History cursor vocabulary encoding law emission :=
  runFrom cursor vocabulary encoding law emission ⟨[], initial cursor vocabulary encoding law emission⟩ suffix

theorem actual_suffix_is_preserved (prior : History cursor vocabulary encoding law emission)
    (suffix : List (EventHistory.Stage (code := code))) :
    (runFrom cursor vocabulary encoding law emission prior suffix).1 = prior.1 ++ suffix := by
  induction suffix generalizing prior with
  | nil => simp [runFrom]
  | cons stage tail ih => simp only [runFrom, ih, step, List.append_assoc, List.singleton_append]

theorem through_observes_the_actual_suffix (suffix : List (EventHistory.Stage (code := code))) :
    (through cursor vocabulary encoding law emission suffix).1 = suffix :=
  actual_suffix_is_preserved cursor vocabulary encoding law emission _ suffix

theorem terminal_iff_actual_content_receipt (suffix : List (EventHistory.Stage (code := code))) :
    (through cursor vocabulary encoding law emission suffix).2.state.TerminalAt 0 ↔
      Acknowledged cursor vocabulary encoding law emission suffix := by
  have same := through_observes_the_actual_suffix cursor vocabulary encoding law emission suffix
  cases (through cursor vocabulary encoding law emission suffix).2.shape with
  | live unconfirmed slots =>
    constructor
    · rintro ⟨record, impossible⟩; simp [slots] at impossible
    · intro ack; exact False.elim (unconfirmed (same.symm ▸ ack))
  | terminal record ack _ slots =>
    exact ⟨fun _ => same ▸ ack, fun _ => ⟨record, by simp [slots]⟩⟩

theorem original_admission_and_complete_native_history (suffix : List (EventHistory.Stage (code := code))) :
    (through cursor vocabulary encoding law emission suffix).2.state.history =
      (through cursor vocabulary encoding law emission suffix).2.run.events ∧
    (through cursor vocabulary encoding law emission suffix).2.state.slots.length = 1 ∧
    (∀ record, (through cursor vocabulary encoding law emission suffix).2.state.slots[0]? = some (.terminal record) →
      record.obligation = obligation cursor vocabulary encoding law emission) := by
  refine ⟨by simpa [ResponsibilityState.empty] using (through cursor vocabulary encoding law emission suffix).2.run.history_eq, ?_⟩
  cases (through cursor vocabulary encoding law emission suffix).2.shape with
  | live _ slots =>
    refine ⟨by simp [slots], ?_⟩
    intro record impossible; simp [slots] at impossible
  | terminal record _ original slots =>
    refine ⟨by simp [slots], ?_⟩
    intro other present
    have same : record = other := by simpa [slots] using present
    exact same ▸ original

theorem live_iff_no_content_receipt (suffix : List (EventHistory.Stage (code := code))) :
    (through cursor vocabulary encoding law emission suffix).2.state.LiveAt 0 ↔
      ¬ Acknowledged cursor vocabulary encoding law emission suffix := by
  have same := through_observes_the_actual_suffix cursor vocabulary encoding law emission suffix
  cases (through cursor vocabulary encoding law emission suffix).2.shape with
  | live unconfirmed slots =>
    exact ⟨fun _ ack => unconfirmed (same.symm ▸ ack), fun _ =>
      ⟨obligation cursor vocabulary encoding law emission, by simp [slots]⟩⟩
  | terminal _ ack _ slots =>
    constructor
    · rintro ⟨duty, impossible⟩; simp [slots] at impossible
    · intro missing; exact False.elim (missing (same ▸ ack))

theorem terminal_step_retains_the_first_archive (prior : History cursor vocabulary encoding law emission)
    (stage : EventHistory.Stage (code := code)) (terminal : prior.2.state.TerminalAt 0) :
    (step cursor vocabulary encoding law emission prior stage).2.state = prior.2.state := by
  rcases prior with ⟨suffix, state, run, shape⟩
  cases shape with
  | live _ slots => obtain ⟨record, impossible⟩ := terminal; simp [slots] at impossible
  | terminal record ack original slots => rfl

theorem runFrom_append (prior : History cursor vocabulary encoding law emission)
    (first more : List (EventHistory.Stage (code := code))) :
    runFrom cursor vocabulary encoding law emission prior (first ++ more) =
      runFrom cursor vocabulary encoding law emission (runFrom cursor vocabulary encoding law emission prior first) more := by
  induction first generalizing prior with
  | nil => rfl
  | cons stage tail ih => exact ih (step cursor vocabulary encoding law emission prior stage)

theorem terminal_run_retains_the_first_archive (prior : History cursor vocabulary encoding law emission)
    (suffix : List (EventHistory.Stage (code := code))) (terminal : prior.2.state.TerminalAt 0) :
    (runFrom cursor vocabulary encoding law emission prior suffix).2.state = prior.2.state := by
  induction suffix generalizing prior with
  | nil => rfl
  | cons stage tail ih =>
    have same := terminal_step_retains_the_first_archive cursor vocabulary encoding law emission prior stage terminal
    exact (ih _ (same.symm ▸ terminal)).trans same

theorem first_archive_is_retained (suffix more : List (EventHistory.Stage (code := code)))
    (terminal : (through cursor vocabulary encoding law emission suffix).2.state.TerminalAt 0) :
    (through cursor vocabulary encoding law emission (suffix ++ more)).2.state =
      (through cursor vocabulary encoding law emission suffix).2.state := by
  unfold through
  rw [runFrom_append]
  exact terminal_run_retains_the_first_archive cursor vocabulary encoding law emission _ more terminal

def histories (stages : List (EventHistory.Stage (code := code))) :=
  (origins cursor vocabulary encoding stages).map fun emission =>
    (⟨emission, through cursor vocabulary encoding law emission (stages.drop emission.birthStages.length)⟩ :
      Sigma (History cursor vocabulary encoding law))

theorem generated_row_observes_the_original_whole_history
    (stages : List (EventHistory.Stage (code := code)))
    (row : Sigma (History cursor vocabulary encoding law))
    (inside : row ∈ histories cursor vocabulary encoding law stages) :
    row.1.birthStages ++ row.2.1 = stages := by
  obtain ⟨emission, member, same⟩ := List.mem_map.mp inside
  cases same
  obtain ⟨index, _, born⟩ := List.mem_filterMap.mp member
  obtain ⟨birth, send⟩ := birth_is_the_original_prefix cursor vocabulary encoding stages index emission born
  rw [through_observes_the_actual_suffix, emission.at_birth, send, birth]
  exact List.take_append_drop _ _

theorem generated_row_terminal_iff_the_actual_receiver_confirms
    (stages : List (EventHistory.Stage (code := code)))
    (row : Sigma (History cursor vocabulary encoding law))
    (inside : row ∈ histories cursor vocabulary encoding law stages) :
    row.2.2.state.TerminalAt 0 ↔
      ∃ receipt ∈ (StageReception.run vocabulary encoding law cursor stages row.1.wire.recipient stages.length).receipts,
        receipt.wire.ballot = row.1.wire.ballot := by
  have whole := generated_row_observes_the_original_whole_history cursor vocabulary encoding law stages row inside
  obtain ⟨emission, _, same⟩ := List.mem_map.mp inside
  cases same
  rw [through_observes_the_actual_suffix] at whole
  rw [terminal_iff_actual_content_receipt]
  unfold Acknowledged received
  rw [whole]

theorem generated_ready_delivery_settles_the_original_native_duty
    (stages : List (EventHistory.Stage (code := code)))
    (row : Sigma (History cursor vocabulary encoding law))
    (inside : row ∈ histories cursor vocabulary encoding law stages)
    (index : Nat) (wire : StageTransport.Wire (code := code)) (before : index < stages.length)
    (ready : StageQueueProgress.readyAt vocabulary encoding law cursor stages row.1.wire.recipient index = some wire)
    (body : wire.ballot = row.1.wire.ballot) :
    row.2.2.state.TerminalAt 0 := by
  obtain ⟨receipt, actual, same⟩ := StageQueueProgress.source_ready_delivery_generates_or_preserves_its_actual_content_receipt
    vocabulary encoding law cursor stages row.1.wire.recipient index wire ready
  apply (generated_row_terminal_iff_the_actual_receiver_confirms cursor vocabulary encoding law stages row inside).mpr
  exact ⟨receipt, (StageQueueProgress.receipts_are_preserved vocabulary encoding law cursor stages row.1.wire.recipient
    (index + 1) stages.length (by omega)).subset actual, same.trans body⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageDuty
