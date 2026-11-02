import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.TimedDuty
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SilentWindow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.TimedRetry

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code) (past : List (EventHistory.Stage (code := code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

abbrev current := EventHistory.execute start past

def localSend (sender recipient : Fin code.sites) (supported : Event.send sender recipient ∈ code.eventAlphabet) :
    LocalMove code sender :=
  ⟨some ⟨.send sender recipient, supported⟩, by
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨⟨.send sender recipient, supported⟩, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨List.mem_attach _ _, by simp⟩⟩

def sending (sender recipient : Fin code.sites) (supported : Event.send sender recipient ∈ code.eventAlphabet) : Rule code where
  work := (SilentWindow.quiet (code := code)).work
  events := fun key _ => if same : key.1 = sender then same.symm ▸ localSend sender recipient supported
    else ⟨none, List.mem_cons_self⟩

def delivery (serial : Nat) (supported : Event.deliver serial ∈ code.eventAlphabet) : Opponent code :=
  fun _ _ _ => some ⟨.deliver serial, supported⟩

abbrev waiting (entry : TimedDuty.Overdue start past vocabulary encoding law) :=
  SilentWindow.delay (current start past) entry.emission.wire.ballot.key
abbrev aligned (entry : TimedDuty.Overdue start past vocabulary encoding law) :=
  past ++ SilentWindow.stages (waiting start past vocabulary encoding law entry)
abbrev sent (entry : TimedDuty.Overdue start past vocabulary encoding law)
    (supported : Event.send entry.emission.wire.ballot.key entry.emission.wire.recipient ∈ code.eventAlphabet) :=
  aligned start past vocabulary encoding law entry ++
    [(sending entry.emission.wire.ballot.key entry.emission.wire.recipient supported, SilentWindow.environment)]
abbrev completed (entry : TimedDuty.Overdue start past vocabulary encoding law)
    (supported : Event.send entry.emission.wire.ballot.key entry.emission.wire.recipient ∈ code.eventAlphabet)
    (wire : StageTransport.Wire (code := code)) (deliverable : Event.deliver wire.serial ∈ code.eventAlphabet) :=
  sent start past vocabulary encoding law entry supported ++ [(SilentWindow.quiet, delivery wire.serial deliverable)]

structure Ready where
  private mk ::
  overdue : TimedDuty.Overdue start past vocabulary encoding law
  supported : Event.send overdue.emission.wire.ballot.key overdue.emission.wire.recipient ∈ code.eventAlphabet
  fuel : waiting start past vocabulary encoding law overdue + 2 ≤ (EventStep.seed (current start past)).remaining
  wire : StageTransport.Wire (code := code)
  issued : StageTransport.issuedAt vocabulary encoding start
    (sent start past vocabulary encoding law overdue supported)
    (aligned start past vocabulary encoding law overdue).length = some wire
  same_content : StageDuty.content wire = StageDuty.content overdue.emission.wire
  deliverable : Event.deliver wire.serial ∈ code.eventAlphabet
  received : StageQueueProgress.readyAt vocabulary encoding law start
    (completed start past vocabulary encoding law overdue supported wire deliverable)
    overdue.emission.wire.recipient ((aligned start past vocabulary encoding law overdue).length + 1) = some wire

abbrev Ready.stages (answer : Ready start past vocabulary encoding law) :=
  completed start past vocabulary encoding law answer.overdue answer.supported answer.wire answer.deliverable

inductive Obstruction where
  | unsupportedSend | exhausted | noAuthenticatedSend | changedContent | unsupportedDelivery | reception
  deriving DecidableEq
inductive Plan where
  | idle
  | blocked (reason : Obstruction)
  | ready (answer : Ready start past vocabulary encoding law)

def produce : Plan start past vocabulary encoding law :=
  match (TimedDuty.observed start past vocabulary encoding law).head? with
  | none => .idle
  | some entry =>
    if supported : Event.send entry.emission.wire.ballot.key entry.emission.wire.recipient ∈ code.eventAlphabet then
    if fuel : waiting start past vocabulary encoding law entry + 2 ≤ (EventStep.seed (current start past)).remaining then
      match issued : StageTransport.issuedAt vocabulary encoding start
          (sent start past vocabulary encoding law entry supported) (aligned start past vocabulary encoding law entry).length with
      | none => .blocked .noAuthenticatedSend
      | some wire =>
        if same : StageDuty.content wire = StageDuty.content entry.emission.wire then
        if deliverable : Event.deliver wire.serial ∈ code.eventAlphabet then
        if received : StageQueueProgress.readyAt vocabulary encoding law start
            (completed start past vocabulary encoding law entry supported wire deliverable)
            entry.emission.wire.recipient ((aligned start past vocabulary encoding law entry).length + 1) = some wire then
          .ready ⟨entry, supported, fuel, wire, issued, same, deliverable, received⟩
        else .blocked .reception
        else .blocked .unsupportedDelivery
        else .blocked .changedContent
    else .blocked .exhausted
    else .blocked .unsupportedSend

def stages : List (EventHistory.Stage (code := code)) :=
  match produce start past vocabulary encoding law with
  | .ready answer => answer.stages
  | _ => past

theorem ready_appends_the_generated_schedule (answer : Ready start past vocabulary encoding law)
    (selected : produce start past vocabulary encoding law = .ready answer) :
    stages start past vocabulary encoding law = answer.stages := by
  simp only [stages, selected]

theorem blocked_keeps_the_actual_history (reason : Obstruction)
    (blocked : produce start past vocabulary encoding law = .blocked reason) :
    stages start past vocabulary encoding law = past := by
  simp only [stages, blocked]

theorem the_original_history_is_preserved (answer : Ready start past vocabulary encoding law) : past <+: answer.stages :=
  (List.prefix_append _ _).trans ((List.prefix_append _ _).trans (List.prefix_append _ _))

theorem retry_uses_the_original_senders_roster_turn (answer : Ready start past vocabulary encoding law) :
    Distributed.Recall.Information.Agency.ownerAt code
      (EventHistory.execute start (aligned start past vocabulary encoding law answer.overdue)).ownerStart
      (EventStep.seed (EventHistory.execute start (aligned start past vocabulary encoding law answer.overdue))).history.length =
        some answer.overdue.emission.wire.ballot.key := by
  rw [StageQueue.execute_append, SilentWindow.execution_is_the_actual_cursor]
  exact SilentWindow.the_actual_receiver_owns_the_generated_arrival _ _

theorem retry_has_a_bounded_source_schedule (answer : Ready start past vocabulary encoding law) :
    answer.stages.length = past.length + waiting start past vocabulary encoding law answer.overdue + 2 ∧
      waiting start past vocabulary encoding law answer.overdue <
        (current start past).ownerStart - (EventStep.seed (current start past)).history.length + 4 * code.sites := by
  refine ⟨?_, SilentWindow.the_generated_delay_has_a_source_roster_bound _ _⟩
  simp only [Ready.stages, completed, sent, aligned, List.length_append, List.length_singleton, SilentWindow.stage_count]

theorem ready_requires_a_real_communication_window (answer : Ready start past vocabulary encoding law) :
    0 < law.maxDelay := by
  have ready := answer.received
  unfold StageQueueProgress.readyAt at ready
  split at ready <;> try contradiction
  rename_i row wire actual incoming
  split at ready <;> try contradiction
  rename_i accepted
  have facts := StageReception.check_sound vocabulary encoding law start answer.stages
    answer.overdue.emission.wire.recipient row [] wire wire accepted
  have earlier := facts.2.2.1
  have timely := facts.2.2.2.2.2.2.2.1
  omega

theorem the_new_wire_has_actual_source_authentication (answer : Ready start past vocabulary encoding law) :
    StageTransport.verify vocabulary encoding start answer.stages answer.wire = true := by
  apply decide_eq_true
  apply List.mem_filterMap.mpr
  refine ⟨(aligned start past vocabulary encoding law answer.overdue).length, ?_, ?_⟩
  · simp only [Ready.stages, completed, sent, List.mem_range, List.length_append, List.length_singleton]
    omega
  · exact (StagePrefix.issued_at start
      (sent start past vocabulary encoding law answer.overdue answer.supported)
      [(SilentWindow.quiet, delivery answer.wire.serial answer.deliverable)] vocabulary encoding _
      (by simp only [sent, List.length_append, List.length_singleton]; omega)).trans answer.issued

theorem new_actual_delivery_terminates_the_original_duty (answer : Ready start past vocabulary encoding law) :
    ∃ row ∈ StageDuty.histories start vocabulary encoding law answer.stages,
      row.1 = answer.overdue.emission ∧ row.2.2.state.TerminalAt 0 := by
  have original := TimedDuty.original_emission_survives_extension start past vocabulary encoding law answer.overdue
    (SilentWindow.stages (waiting start past vocabulary encoding law answer.overdue) ++
      [(sending answer.overdue.emission.wire.ballot.key answer.overdue.emission.wire.recipient answer.supported, SilentWindow.environment)] ++
      [(SilentWindow.quiet, delivery answer.wire.serial answer.deliverable)])
  have inside : answer.overdue.emission ∈ StageDuty.origins start vocabulary encoding answer.stages := by
    simpa only [Ready.stages, completed, sent, aligned, List.append_assoc] using original
  let row : Sigma (StageDuty.History start vocabulary encoding law) :=
    ⟨answer.overdue.emission, StageDuty.through start vocabulary encoding law answer.overdue.emission
      (answer.stages.drop answer.overdue.emission.birthStages.length)⟩
  have member : row ∈ StageDuty.histories start vocabulary encoding law answer.stages :=
    List.mem_map.mpr ⟨answer.overdue.emission, inside, rfl⟩
  refine ⟨row, member, rfl, StageDuty.generated_ready_delivery_settles_the_original_native_duty
    start vocabulary encoding law answer.stages row member
    ((aligned start past vocabulary encoding law answer.overdue).length + 1) answer.wire ?_ answer.received ?_⟩
  · simp only [Ready.stages, completed, sent, List.length_append, List.length_singleton]
    omega
  · exact congrArg Prod.fst answer.same_content

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.TimedRetry
