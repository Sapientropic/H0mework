import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceptionEvidence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionResponse

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (pastStages : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev current := EventHistory.execute start pastStages
abbrev observed (receiver : Fin model.source.code.sites) := ReceptionEvidence.observed start pastStages vocabulary encoding law receiver
abbrev signature := IncidentResponse.signature model
abbrev Active := IncidentResponse.Active model start pastStages
abbrev Identity := Fin model.source.code.sites × Nat
abbrev Obstruction := IncidentResponse.Obstruction

structure Ready where
  private mk ::
  receiver : Fin model.source.code.sites
  evidence : ReceptionEvidence.Entry start pastStages vocabulary encoding law receiver
  supported : signature model receiver ∈ model.source.code.actions
  capacity : 1 ≤ model.source.code.actionLimit
  activation : .activate receiver ∈ model.source.code.eventAlphabet
  fuel : 0 < (EventStep.seed (current model start pastStages)).remaining
  owner : Distributed.Recall.Information.Agency.ownerAt model.source.code (current model start pastStages).ownerStart
    (EventStep.seed (current model start pastStages)).history.length = some receiver
  memory : model.source.code.memoryReady ((EventStep.seed (current model start pastStages)).frame.inbox receiver) = true
  standing : Mandate.Challenge.Submission (scope := model.scope) (signature model receiver)
  valid : model.source.code.law.Valid (EventStep.seed (current model start pastStages)).current (signature model receiver)
  active : Active model start pastStages

inductive Plan where
  | idle
  | environmentTurn
  | blocked (reason : Obstruction)
  | ready (response : Ready model start pastStages vocabulary encoding law)

private theorem head_member {α : Type} (items : List α) (value : α) (first : items.head? = some value) : value ∈ items := by
  cases items with
  | nil => cases first
  | cons head tail =>
    have same : head = value := Option.some.inj first
    subst value
    exact List.mem_cons_self

private def planAt (handled : List (Identity model)) : Plan model start pastStages vocabulary encoding law :=
  match owner : Distributed.Recall.Information.Agency.ownerAt model.source.code (current model start pastStages).ownerStart
      (EventStep.seed (current model start pastStages)).history.length with
  | none => .environmentTurn
  | some receiver =>
    match _first : ((observed model start pastStages vocabulary encoding law receiver).filter
        (fun evidence => decide ((receiver, evidence.index) ∉ handled))).head? with
    | none => .idle
    | some evidence =>
      if supported : signature model receiver ∈ model.source.code.actions then
      if capacity : 1 ≤ model.source.code.actionLimit then
      if activation : .activate receiver ∈ model.source.code.eventAlphabet then
      if fuel : 0 < (EventStep.seed (current model start pastStages)).remaining then
      if memory : model.source.code.memoryReady ((EventStep.seed (current model start pastStages)).frame.inbox receiver) = true then
      if standing : Mandate.Challenge.Submission (scope := model.scope) (signature model receiver) then
      if valid : model.source.code.law.Valid (EventStep.seed (current model start pastStages)).current (signature model receiver) then
      if active : Active model start pastStages then
        .ready ⟨receiver, evidence, supported, capacity, activation, fuel, owner, memory, standing, valid, active⟩
      else .blocked .inactive
      else .blocked .invalid
      else .blocked .noStanding
      else .blocked .sealed
      else .blocked .exhausted
      else .blocked .unsupportedActivation
      else .blocked .noActionCapacity
      else .blocked .unsupportedAction

variable (response : Ready model start pastStages vocabulary encoding law)

def work : model.source.code.Policy := fun key _ =>
  if key.1 = response.receiver then [signature model response.receiver] else []

theorem work_generated : work model start pastStages vocabulary encoding law response ∈ model.source.code.policies := by
  apply model.source.code.every_local_policy_is_enumerated
  intro key _
  apply (mem_words_iff _ _ _).mpr
  unfold work
  split
  · exact ⟨response.capacity, by intro action member; simpa only [List.mem_singleton.mp member] using response.supported⟩
  · simp

def localActivation : LocalMove model.source.code response.receiver :=
  ⟨some ⟨.activate response.receiver, response.activation⟩, by
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨⟨.activate response.receiver, response.activation⟩, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨List.mem_attach _ _, by simp⟩⟩

def protocol : Rule model.source.code where
  work := ⟨work model start pastStages vocabulary encoding law response, work_generated model start pastStages vocabulary encoding law response⟩
  events := fun key _ => if same : key.1 = response.receiver then
    same.symm ▸ localActivation model start pastStages vocabulary encoding law response
  else ⟨none, List.mem_cons_self⟩

abbrev row (rival : Opponent model.source.code) :=
  StageTrace.material (current model start pastStages) (protocol model start pastStages vocabulary encoding law response) rival

theorem response_uses_the_actual_receivers_owned_activation (rival : Opponent model.source.code) :
    StageTrace.activation (row model start pastStages vocabulary encoding law response rival) = some response.receiver := by
  have live : (EventStep.seed (current model start pastStages)).remaining ≠ 0 := Nat.ne_of_gt response.fuel
  simp [row, StageTrace.activation, StageTrace.material, StageTrace.capture, live, response.owner,
    localEvent, protocol, localActivation]

theorem response_submits_its_original_signature (rival : Opponent model.source.code) :
    (row model start pastStages vocabulary encoding law response rival).submitted = [signature model response.receiver] := by
  have actual := StageTrace.an_owned_activation_submits_its_selected_work (current model start pastStages)
    (protocol model start pastStages vocabulary encoding law response) rival response.receiver
    (response_uses_the_actual_receivers_owned_activation model start pastStages vocabulary encoding law response rival)
  exact actual.2.trans (by simp [protocol, Code.action, response.memory, work])

abbrev sameRule := IncidentResponse.sameRule model
abbrev sameRule_iff := IncidentResponse.sameRule_iff model

structure Answer where
  private mk ::
  pastStages : List (EventHistory.Stage (code := model.source.code))
  response : Ready model start pastStages vocabulary encoding law
  actualRule : Rule model.source.code
  rival : Opponent model.source.code
  aligned : sameRule model actualRule (protocol model start pastStages vocabulary encoding law response) = true

abbrev Answer.birthStages (answer : Answer model start vocabulary encoding law) :=
  answer.pastStages ++ [(answer.actualRule, answer.rival)]
abbrev Answer.id (answer : Answer model start vocabulary encoding law) :=
  (answer.response.receiver, answer.response.evidence.index)

private def register (priorStages : List (EventHistory.Stage (code := model.source.code)))
    (answers : List (Answer model start vocabulary encoding law)) (stage : EventHistory.Stage (code := model.source.code)) : List (Answer model start vocabulary encoding law) :=
  match planAt model start priorStages vocabulary encoding law (answers.map (Answer.id model start vocabulary encoding law)) with
  | .ready selected =>
    if aligned : sameRule model stage.1 (protocol model start priorStages vocabulary encoding law selected) = true then
      answers ++ [⟨priorStages, selected, stage.1, stage.2, aligned⟩]
    else answers
  | _ => answers

private def scan (priorStages : List (EventHistory.Stage (code := model.source.code)))
    (answers : List (Answer model start vocabulary encoding law)) :
    List (EventHistory.Stage (code := model.source.code)) → List (Answer model start vocabulary encoding law)
  | [] => answers
  | stage :: tail => scan (priorStages ++ [stage]) (register model start vocabulary encoding law priorStages answers stage) tail

def journal := scan model start vocabulary encoding law [] [] pastStages

def produce : Plan model start pastStages vocabulary encoding law :=
  planAt model start pastStages vocabulary encoding law ((journal model start pastStages vocabulary encoding law).map (Answer.id model start vocabulary encoding law))

private theorem scan_append (priorStages first more : List (EventHistory.Stage (code := model.source.code)))
    (answers : List (Answer model start vocabulary encoding law)) :
    scan model start vocabulary encoding law priorStages answers (first ++ more) =
      scan model start vocabulary encoding law (priorStages ++ first) (scan model start vocabulary encoding law priorStages answers first) more := by
  induction first generalizing priorStages answers with
  | nil => simp [scan]
  | cons stage tail ih => simp only [List.cons_append, scan, ih, List.append_assoc, List.nil_append]

private theorem scan_prefix (priorStages tail : List (EventHistory.Stage (code := model.source.code)))
    (answers : List (Answer model start vocabulary encoding law))
    (old : ∀ answer ∈ answers, answer.birthStages <+: priorStages) :
    ∀ answer ∈ scan model start vocabulary encoding law priorStages answers tail, answer.birthStages <+: priorStages ++ tail := by
  induction tail generalizing priorStages answers with
  | nil => simpa only [scan, List.append_nil] using old
  | cons stage tail ih =>
    have next : ∀ answer ∈ register model start vocabulary encoding law priorStages answers stage,
        answer.birthStages <+: priorStages ++ [stage] := by
      intro answer member
      unfold register at member
      split at member
      · split at member
        · rcases List.mem_append.mp member with previous | generated
          · exact (old answer previous).trans (List.prefix_append _ _)
          · obtain rfl := List.mem_singleton.mp generated
            exact List.prefix_refl _
        · exact (old answer member).trans (List.prefix_append _ _)
      · exact (old answer member).trans (List.prefix_append _ _)
    simpa only [scan, List.append_assoc, List.singleton_append, List.nil_append] using ih (priorStages ++ [stage]) _ next

theorem every_answer_retains_its_actual_source_prefix
    (answer : Answer model start vocabulary encoding law)
    (inside : answer ∈ journal model start pastStages vocabulary encoding law) : answer.birthStages <+: pastStages := by
  simpa only [List.nil_append] using scan_prefix model start vocabulary encoding law [] pastStages [] (by simp) answer inside

theorem every_answer_has_the_actual_owned_signature
    (answer : Answer model start vocabulary encoding law) :
    StageTrace.activation (StageTrace.material (current model start answer.pastStages) answer.actualRule answer.rival) = some answer.response.receiver ∧
      (StageTrace.material (current model start answer.pastStages) answer.actualRule answer.rival).submitted =
        [signature model answer.response.receiver] := by
  have same := (sameRule_iff model _ _).mp answer.aligned
  rw [same]
  exact ⟨response_uses_the_actual_receivers_owned_activation _ _ _ _ _ _ _ _,
    response_submits_its_original_signature _ _ _ _ _ _ _ _⟩

private theorem planAt_never_selects_a_handled_rejection (handled : List (Identity model))
    (selected : planAt model start pastStages vocabulary encoding law handled = .ready response) :
    (response.receiver, response.evidence.index) ∉ handled := by
  unfold planAt at selected
  split at selected
  · contradiction
  · split at selected
    · contradiction
    · rename_i receiver owner evidence first
      have fresh := (List.mem_filter.mp (head_member _ _ first)).2
      repeat' first | split at selected | contradiction
      cases Plan.ready.inj selected
      exact of_decide_eq_true fresh

theorem a_ready_response_has_not_been_registered
    (selected : produce model start pastStages vocabulary encoding law = .ready response) :
    (response.receiver, response.evidence.index) ∉
      (journal model start pastStages vocabulary encoding law).map (Answer.id model start vocabulary encoding law) :=
  planAt_never_selects_a_handled_rejection model start pastStages vocabulary encoding law response _ selected

theorem every_registered_response_is_an_actual_history_row
    (answer : Answer model start vocabulary encoding law)
    (inside : answer ∈ journal model start pastStages vocabulary encoding law) :
    StageTrace.material (current model start answer.pastStages) answer.actualRule answer.rival ∈ StageTrace.records start pastStages := by
  obtain ⟨tail, same⟩ := every_answer_retains_its_actual_source_prefix model start pastStages vocabulary encoding law answer inside
  rw [← same, StageQueue.records_append]
  apply List.mem_append_left
  rw [Answer.birthStages, StageQueue.records_append]
  exact List.mem_append_right _ (List.mem_cons_self)

theorem a_generated_response_is_registered_once (rival : Opponent model.source.code)
    (selected : produce model start pastStages vocabulary encoding law = .ready response) :
    (journal model start (pastStages ++ [(protocol model start pastStages vocabulary encoding law response, rival)]) vocabulary encoding law).map (Answer.id model start vocabulary encoding law) =
      (journal model start pastStages vocabulary encoding law).map (Answer.id model start vocabulary encoding law) ++ [(response.receiver, response.evidence.index)] := by
  unfold journal
  rw [scan_append]
  simp only [List.nil_append, scan]
  change (register model start vocabulary encoding law pastStages (journal model start pastStages vocabulary encoding law)
    (protocol model start pastStages vocabulary encoding law response, rival)).map (Answer.id model start vocabulary encoding law) = _
  unfold produce at selected
  simp only [register, selected, (sameRule_iff model _ _).mpr rfl, dif_pos, List.map_append, List.map_cons, List.map_nil]
  rfl

def stages (rival : Opponent model.source.code) :=
  match produce model start pastStages vocabulary encoding law with
  | .ready selected => pastStages ++ [(protocol model start pastStages vocabulary encoding law selected, rival)]
  | _ => pastStages

theorem ready_appends_the_actual_response_stage (rival : Opponent model.source.code)
    (selected : produce model start pastStages vocabulary encoding law = .ready response) :
    stages model start pastStages vocabulary encoding law rival = pastStages ++ [(protocol model start pastStages vocabulary encoding law response, rival)] := by
  simp only [stages, selected]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionResponse
