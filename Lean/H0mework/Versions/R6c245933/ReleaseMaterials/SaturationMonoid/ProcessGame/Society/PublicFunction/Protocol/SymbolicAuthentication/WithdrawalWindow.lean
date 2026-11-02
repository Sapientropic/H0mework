import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SilentWindow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalWindow

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev current := EventHistory.execute start past
abbrev head := (IncidentResponse.journal model start past vocabulary encoding law).head?
def delay : Nat := match head model start past vocabulary encoding law with
  | none => 0
  | some answer => SilentWindow.delay (current model start past) answer.response.incident.receiver
def waiting := if delay model start past vocabulary encoding law < (EventStep.seed (current model start past)).remaining then
  past ++ SilentWindow.stages (delay model start past vocabulary encoding law) else past
abbrev arrival := EventHistory.execute start (waiting model start past vocabulary encoding law)

def produce : IncidentWithdrawal.Plan model start (waiting model start past vocabulary encoding law) vocabulary encoding law :=
  if delay model start past vocabulary encoding law < (EventStep.seed (current model start past)).remaining then
    IncidentWithdrawal.produce model start (waiting model start past vocabulary encoding law) vocabulary encoding law
  else .blocked .exhausted

def stages (rival : Opponent model.source.code) :=
  if delay model start past vocabulary encoding law < (EventStep.seed (current model start past)).remaining then
    IncidentWithdrawal.stages model start (waiting model start past vocabulary encoding law) vocabulary encoding law rival
  else past

variable (enough : delay model start past vocabulary encoding law < (EventStep.seed (current model start past)).remaining)

include enough in
theorem arrival_is_the_generated_silent_cursor : arrival model start past vocabulary encoding law =
    SilentWindow.cursorAt (current model start past) (delay model start past vocabulary encoding law) := by
  simp only [arrival, waiting, if_pos enough, StageQueue.execute_append, SilentWindow.execution_is_the_actual_cursor]

include enough in
theorem waiting_preserves_the_actual_source :
    SilentWindow.Preserves (current model start past) (arrival model start past vocabulary encoding law)
      (delay model start past vocabulary encoding law) := by
  rw [arrival_is_the_generated_silent_cursor model start past vocabulary encoding law enough]
  exact SilentWindow.preserves_the_actual_state _ _

include enough in
theorem the_actual_head_survives (answer : IncidentResponse.Answer model start vocabulary encoding law)
    (original : head model start past vocabulary encoding law = some answer) :
    (IncidentResponse.journal model start (waiting model start past vocabulary encoding law) vocabulary encoding law).head? = some answer := by
  rw [waiting, if_pos enough]
  exact IncidentResponse.Prefix.the_original_head_survives model start vocabulary encoding law past _ answer original

include enough in
theorem the_original_receiver_owns_the_arrival (answer : IncidentResponse.Answer model start vocabulary encoding law)
    (original : head model start past vocabulary encoding law = some answer) :
    Distributed.Recall.Information.Agency.ownerAt model.source.code
      (arrival model start past vocabulary encoding law).ownerStart
      (EventStep.seed (arrival model start past vocabulary encoding law)).history.length = some answer.response.incident.receiver := by
  rw [arrival_is_the_generated_silent_cursor model start past vocabulary encoding law enough]
  have count : delay model start past vocabulary encoding law =
      SilentWindow.delay (current model start past) answer.response.incident.receiver := by
    unfold delay
    rw [original]
  rw [count]
  exact SilentWindow.the_actual_receiver_owns_the_generated_arrival (code := model.source.code)
    (current model start past) answer.response.incident.receiver

include enough in
theorem a_rotation_obstruction_generates_an_actual_attempt
    (answer : IncidentResponse.Answer model start vocabulary encoding law)
    (original : head model start past vocabulary encoding law = some answer)
    (blocked : IncidentWithdrawal.produce model start past vocabulary encoding law = .blocked .notOwner)
    (memory : model.source.code.memoryReady ((EventStep.seed (current model start past)).frame.inbox answer.response.incident.receiver) = true) :
    ∃ ready : IncidentWithdrawal.Ready model start (waiting model start past vocabulary encoding law) vocabulary encoding law,
      ready.answer = answer ∧ ((∃ accepted, produce model start past vocabulary encoding law = .paid ready accepted) ∨
      (∃ denied, produce model start past vocabulary encoding law = .refused ready denied)) := by
  have state := waiting_preserves_the_actual_source model start past vocabulary encoding law enough
  have kept := the_actual_head_survives model start past vocabulary encoding law enough answer original
  have owned := the_original_receiver_owns_the_arrival model start past vocabulary encoding law enough answer original
  have live : 0 < (EventStep.seed (arrival model start past vocabulary encoding law)).remaining := by
    rw [state.fuel]
    omega
  have memoryAfter : model.source.code.memoryReady
      ((EventStep.seed (arrival model start past vocabulary encoding law)).frame.inbox answer.response.incident.receiver) = true := by
    rw [state.frame]
    exact memory
  have actionSame : IncidentWithdrawal.action model start (waiting model start past vocabulary encoding law) vocabulary encoding law answer =
      IncidentWithdrawal.action model start past vocabulary encoding law answer := by
    unfold IncidentWithdrawal.action Mandate.request Mandate.advance
    rw [state.technology]
  unfold IncidentWithdrawal.produce at blocked
  change (IncidentWithdrawal.observed model start past vocabulary encoding law).head? = some answer at original
  split at blocked
  · rename_i absent
    rw [original] at absent
    contradiction
  rename_i selectedAnswer selected
  have identity : selectedAnswer = answer := Option.some.inj (selected.symm.trans original)
  subst selectedAnswer
  split at blocked <;> try (exact False.elim (by cases blocked))
  rename_i snapshot
  split at blocked <;> try (exact False.elim (by cases blocked))
  rename_i member
  split at blocked <;> try (exact False.elim (by cases blocked))
  rename_i supported
  split at blocked <;> try (exact False.elim (by cases blocked))
  rename_i capacity
  split at blocked <;> try (exact False.elim (by cases blocked))
  rename_i activation
  split at blocked <;> try (exact False.elim (by cases blocked))
  have snapshotAfter : (EventStep.seed (arrival model start past vocabulary encoding law)).current.technology =
      IncidentWithdrawal.snapshot model start vocabulary encoding law answer := state.technology.trans snapshot
  have supportedAfter : IncidentWithdrawal.action model start (waiting model start past vocabulary encoding law) vocabulary encoding law answer ∈ model.source.code.actions := by
    rw [actionSame]
    exact supported
  simp only [produce, if_pos enough]
  generalize result : IncidentWithdrawal.produce model start (waiting model start past vocabulary encoding law) vocabulary encoding law = plan
  unfold IncidentWithdrawal.produce at result
  split at result
  · rename_i absentAfter
    change (IncidentResponse.journal model start (waiting model start past vocabulary encoding law) vocabulary encoding law).head? = none at absentAfter
    rw [kept] at absentAfter
    contradiction
  rename_i selectedAfter foundAfter
  have identityAfter : selectedAfter = answer := Option.some.inj (foundAfter.symm.trans kept)
  subst selectedAfter
  simp only [dif_pos snapshotAfter, dif_pos member, dif_pos supportedAfter, dif_pos capacity,
    dif_pos activation, dif_pos live, dif_pos owned, dif_pos memoryAfter] at result
  split at result
  · rename_i valid
    exact ⟨_, rfl, Or.inl ⟨valid, result.symm⟩⟩
  · rename_i denied
    exact ⟨_, rfl, Or.inr ⟨denied, result.symm⟩⟩

omit [DecidableEq Instrument] in
theorem revoke_validity_depends_on_stock_and_technology
    (base : RawLaw Party Good Port Technology Instrument)
    (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port))
    (first last : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (stock : last.stock = first.stock) (technology : last.technology = first.technology) (actor : Party) :
    (Mandate.law base scope).Valid first (Mandate.request scope first actor .revoke) ↔
      (Mandate.law base scope).Valid last (Mandate.request scope last actor .revoke) := by
  simp only [RawLaw.Valid, RawLaw.SignerMatches, Mandate.request, RawLaw.operationAllowed,
    Mandate.law, RawPolicy.eval, Mandate.advance, Mandate.CanRun, RawLaw.requiredPorts,
    RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard, stock, technology]

include enough in
theorem a_funded_rotation_obstruction_generates_a_paid_attempt
    (answer : IncidentResponse.Answer model start vocabulary encoding law)
    (original : head model start past vocabulary encoding law = some answer)
    (blocked : IncidentWithdrawal.produce model start past vocabulary encoding law = .blocked .notOwner)
    (memory : model.source.code.memoryReady ((EventStep.seed (current model start past)).frame.inbox answer.response.incident.receiver) = true)
    (funded : model.source.code.law.Valid (EventStep.seed (current model start past)).current
      (IncidentWithdrawal.action model start past vocabulary encoding law answer)) :
    ∃ ready : IncidentWithdrawal.Ready model start (waiting model start past vocabulary encoding law) vocabulary encoding law,
      ready.answer = answer ∧ ∃ accepted, produce model start past vocabulary encoding law = .paid ready accepted := by
  obtain ⟨ready, same, paid | refused⟩ := a_rotation_obstruction_generates_an_actual_attempt
    model start past vocabulary encoding law enough answer original blocked memory
  · exact ⟨ready, same, paid⟩
  · obtain ⟨denied, _⟩ := refused
    have facts := waiting_preserves_the_actual_source model start past vocabulary encoding law enough
    have valid : model.source.code.law.Valid (EventStep.seed (arrival model start past vocabulary encoding law)).current
        (IncidentWithdrawal.action model start (waiting model start past vocabulary encoding law) vocabulary encoding law answer) := by
      rw [model.law_exact] at funded ⊢
      exact (revoke_validity_depends_on_stock_and_technology model.base model.scope _ _ facts.stock facts.technology _).mp funded
    rw [← same] at valid
    exact False.elim (denied valid)

include enough in
theorem paid_is_the_actual_resumed_producer
    (ready : IncidentWithdrawal.Ready model start (waiting model start past vocabulary encoding law) vocabulary encoding law)
    (accepted : model.source.code.law.Valid (EventStep.seed (arrival model start past vocabulary encoding law)).current
      (IncidentWithdrawal.action model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready.answer))
    (rival : Opponent model.source.code)
    (selected : produce model start past vocabulary encoding law = .paid ready accepted) :
    IncidentWithdrawal.produce model start (waiting model start past vocabulary encoding law) vocabulary encoding law = .paid ready accepted ∧
      stages model start past vocabulary encoding law rival =
        (waiting model start past vocabulary encoding law) ++
          [(IncidentWithdrawal.protocol model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready, rival)] := by
  simp only [produce, if_pos enough] at selected
  exact ⟨selected, by simp only [stages, if_pos enough]; exact IncidentWithdrawal.paid_appends_the_actual_attempt _ _ _ _ _ _ ready _ accepted selected⟩

include enough in
theorem the_silent_window_generates_its_own_archived_claim
    (answer : IncidentResponse.Answer model start vocabulary encoding law)
    (original : head model start past vocabulary encoding law = some answer)
    (blocked : IncidentWithdrawal.produce model start past vocabulary encoding law = .blocked .notOwner)
    (memory : model.source.code.memoryReady ((EventStep.seed (current model start past)).frame.inbox answer.response.incident.receiver) = true)
    (funded : model.source.code.law.Valid (EventStep.seed (current model start past)).current
      (IncidentWithdrawal.action model start past vocabulary encoding law answer))
    (rival : Opponent model.source.code) (more : List (EventHistory.Stage (code := model.source.code))) :
    ∃ (ready : IncidentWithdrawal.Ready model start (waiting model start past vocabulary encoding law) vocabulary encoding law), ∃ accepted,
      ready.answer = answer ∧ produce model start past vocabulary encoding law = .paid ready accepted ∧
      stages model start past vocabulary encoding law rival = waiting model start past vocabulary encoding law ++
        [(IncidentWithdrawal.protocol model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready, rival)] ∧
      let native := IncidentWithdrawalNative.native model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready rival more
      let family := Native.Authority.programme native
      let sourceIndex := Native.Authority.sourceIndex native
      let depth := IncidentWithdrawalNative.depth model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready rival more
      ∃ claim : Native.Authority.Challenge native,
        claim.position = IncidentWithdrawalNative.birthPosition model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready rival more ∧
        (⟨claim, Mandate.Challenge.through family sourceIndex claim (depth + 2)⟩ :
          Sigma fun original => Native.Authority.ChallengeHistory native original) ∈ (Native.Authority.fullGenerate native depth).challenges ∧
        (Mandate.Challenge.through family sourceIndex claim (depth + 2)).isPending _ _ = false := by
  obtain ⟨ready, same, accepted, selected⟩ := a_funded_rotation_obstruction_generates_a_paid_attempt
    model start past vocabulary encoding law enough answer original blocked memory funded
  have actual := paid_is_the_actual_resumed_producer model start past vocabulary encoding law enough ready accepted rival selected
  obtain ⟨claim, position, _, installed, terminal⟩ :=
    IncidentCompletion.every_actual_paid_attempt_archives_the_original_complete_history model start
      (waiting model start past vocabulary encoding law) vocabulary encoding law ready rival more accepted
  exact ⟨ready, accepted, same, selected, actual.2, claim, position, installed, terminal⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalWindow
