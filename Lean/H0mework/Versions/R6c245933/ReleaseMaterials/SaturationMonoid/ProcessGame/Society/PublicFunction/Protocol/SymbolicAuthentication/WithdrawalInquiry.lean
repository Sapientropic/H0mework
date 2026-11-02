import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalState

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalInquiry

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (installed : List (Rule model.source.code))
  (worker : Fin model.source.code.sites)

def reaffirm : Request Party Good Port (Mandate.State Party Technology) Instrument :=
  ⟨model.source.code.siteParty worker, [], model.scope.challenge, [model.scope.challenge], .present⟩

def reads : List (LocalMove model.source.code worker) :=
  (ownMoves model.source.code worker).attach.filter fun move => match move.val with
  | some event => match event.val with
    | .send sender recipient => decide (sender = worker ∧ recipient = worker)
    | _ => false
  | none => false

def waiting : LocalMove model.source.code worker := ⟨none, List.mem_cons_self⟩

def work (signal : Fin model.source.code.signals) :=
  match WithdrawalState.produce model start installed worker signal with
  | .ready value => if reaffirm model worker ∈ model.source.code.actions ∧ 2 ≤ model.source.code.actionLimit
    then [reaffirm model worker, value] else []
  | _ => []

theorem work_supported (signal : Fin model.source.code.signals) :
    work model start installed worker signal ∈ words model.source.code.actions model.source.code.actionLimit := by
  unfold work
  split
  · rename_i value prepared
    have admitted := WithdrawalState.ready_admission model start installed worker signal value prepared
    split
    · rename_i supported
      exact (mem_words_iff _ _ _).mpr ⟨supported.2, by
        intro item inside
        rcases List.mem_cons.mp inside with same | later
        · exact same ▸ supported.1
        · exact List.mem_singleton.mp later ▸ admitted.2.1⟩
    · exact (mem_words_iff _ _ _).mpr (by simp)
  all_goals exact (mem_words_iff _ _ _).mpr (by simp)

def policy : model.source.code.Policy :=
  let table := Vector.ofFn (work model start installed worker)
  fun key _ => if key.1 = worker then table.get key.2 else []

theorem policy_at (signal : Fin model.source.code.signals) :
    policy model start installed worker (worker, signal) (model.source.code.key_mem _) =
      work model start installed worker signal := by
  simp only [policy, Vector.get, Vector.ofFn, if_pos rfl, Array.getElem_ofFn]
  apply congrArg (work model start installed worker)
  exact Fin.ext rfl

theorem policy_generated : policy model start installed worker ∈ model.source.code.policies := by
  apply model.source.code.every_local_policy_is_enumerated
  intro key inside
  rcases key with ⟨site, signal⟩
  by_cases same : site = worker
  · subst site
    rw [policy_at]
    exact work_supported model start installed worker signal
  · simp only [policy, if_neg same]
    exact (mem_words_iff _ _ _).mpr (by simp)

-- A conflict generates a registered paid self-read. It does not manufacture
-- a fresh signal or presume that the environment will deliver the packet.
def event (signal : Fin model.source.code.signals) : LocalMove model.source.code worker :=
  match WithdrawalState.produce model start installed worker signal with
  | .ambiguous .. => (reads model worker).headD (waiting model worker)
  | .ready _ => if work model start installed worker signal = [] then waiting model worker
    else if supported : Event.activate worker ∈ model.source.code.eventAlphabet then
      LocalWithdrawal.activation model worker supported else waiting model worker
  | _ => waiting model worker

def protocol : Rule model.source.code where
  work := ⟨policy model start installed worker, policy_generated model start installed worker⟩
  events := fun key _ => if same : key.1 = worker then same.symm ▸ event model start installed worker key.2
    else ⟨none, List.mem_cons_self⟩

theorem equal_records_generate_the_same_work_and_event
    (first second : Fin model.source.code.signals) (same : first = second) :
    work model start installed worker first = work model start installed worker second ∧
      event model start installed worker first = event model start installed worker second := by
  rw [same]
  exact ⟨rfl, rfl⟩

theorem a_ready_local_word_reaffirms_and_recovers_the_actual_revoke
    (past : List (EventHistory.Stage (code := model.source.code)))
    (value : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (prepared : WithdrawalState.produce model start (past.map Prod.fst) worker
      (LocalWithdrawal.reading model (EventHistory.execute start past) worker) = .ready value)
    (supported : reaffirm model worker ∈ model.source.code.actions) (capacity : 2 ≤ model.source.code.actionLimit) :
    work model start (past.map Prod.fst) worker (LocalWithdrawal.reading model (EventHistory.execute start past) worker) =
      [reaffirm model worker, NativeReview.action model start past worker] := by
  have actual := WithdrawalState.a_ready_query_recovers_the_actual_original_revoke model start worker past value prepared
  simp only [work, prepared, if_pos (And.intro supported capacity), actual]

theorem the_ready_local_word_is_actually_submitted
    (past : List (EventHistory.Stage (code := model.source.code)))
    (value : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (prepared : WithdrawalState.produce model start (past.map Prod.fst) worker
      (LocalWithdrawal.reading model (EventHistory.execute start past) worker) = .ready value)
    (supported : reaffirm model worker ∈ model.source.code.actions) (capacity : 2 ≤ model.source.code.actionLimit)
    (live : 0 < (EventStep.seed (EventHistory.execute start past)).remaining)
    (owned : Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
      (EventStep.seed (EventHistory.execute start past)).history.length = some worker)
    (rival : Opponent model.source.code) :
    (StageTrace.material (EventHistory.execute start past) (protocol model start (past.map Prod.fst) worker) rival).submitted =
      [reaffirm model worker, NativeReview.action model start past worker] := by
  let cursor := EventHistory.execute start past
  let rule := protocol model start (past.map Prod.fst) worker
  let row := StageTrace.material cursor rule rival
  change WithdrawalState.produce model start (past.map Prod.fst) worker (LocalWithdrawal.reading model cursor worker) = .ready value at prepared
  change 0 < (EventStep.seed cursor).remaining at live
  change Distributed.Recall.Information.Agency.ownerAt model.source.code cursor.ownerStart
    (EventStep.seed cursor).history.length = some worker at owned
  have admitted := WithdrawalState.ready_admission model start _ _ _ value prepared
  have word : work model start (past.map Prod.fst) worker (LocalWithdrawal.reading model cursor worker) =
      [reaffirm model worker, value] := by
    simp only [work, prepared, if_pos (And.intro supported capacity)]
  have activation : StageTrace.activation row = some worker := by
    simp [row, rule, StageTrace.activation, StageTrace.material, StageTrace.capture, Nat.ne_of_gt live, owned,
      localEvent, protocol, event, prepared, word, admitted.2.2.1, LocalWithdrawal.activation]
  have actual := StageTrace.an_owned_activation_submits_its_selected_work cursor rule rival worker activation
  have requested := WithdrawalState.a_ready_query_recovers_the_actual_original_revoke model start worker past value prepared
  exact actual.2.trans (by
    change model.source.code.action (policy model start (past.map Prod.fst) worker) worker (LocalWithdrawal.reading model cursor worker) = _
    simp only [Code.action, admitted.2.2.2.1, if_pos, policy_at, word, requested])

theorem absent_read_admission_preserves_a_typed_wait
    (signal : Fin model.source.code.signals) (first second : State model.source.code)
    (ambiguous : WithdrawalState.produce model start installed worker signal = .ambiguous first second)
    (missing : reads model worker = []) :
    (event model start installed worker signal).val = none := by
  simp only [event, ambiguous, missing, List.headD_nil, waiting]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalInquiry
