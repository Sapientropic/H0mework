import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CausalLocalDomain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompactClaimGate

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (installed : List (Rule model.source.code))
  (worker : Fin model.source.code.sites) (signal : Fin model.source.code.signals)

abbrev Revoke := Request Party Good Port (Mandate.State Party Technology) Instrument

def view (cursor : Cursor model.source.code) : Option (Revoke (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument)) :=
  if LocalClaimGate.pending model cursor worker then some (LocalWithdrawal.request model cursor worker) else none

def fibre := (CausalLocalDomain.history [start] installed).filter fun cursor =>
  LocalWithdrawal.reading model cursor worker == signal

inductive Query where
  | unseen (empty : fibre model start installed worker signal = [])
  | known (value : Option (Revoke (Party := Party) (Good := Good)
      (Port := Port) (Technology := Technology) (Instrument := Instrument)))
      (first : Cursor model.source.code) (actual : first ∈ fibre model start installed worker signal)
      (uniform : ∀ other ∈ fibre model start installed worker signal, view model worker other = value)
  | ambiguous (first second : Cursor model.source.code)
      (left : first ∈ fibre model start installed worker signal)
      (right : second ∈ fibre model start installed worker signal)
      (different : view model worker second ≠ view model worker first)

def query : Query model start installed worker signal :=
  match selected : fibre model start installed worker signal with
  | [] => .unseen selected
  | first :: rest =>
    match inspect (fun other => view model worker other = view model worker first) rest with
    | .accepted uniform => .known (view model worker first) first
        (by rw [selected]; exact List.mem_cons_self) (by
          intro other inside
          rw [selected] at inside
          rcases List.mem_cons.mp inside with same | later
          · exact same ▸ rfl
          · exact uniform other later)
    | .rejected other inside different => .ambiguous first other
        (by rw [selected]; exact List.mem_cons_self)
        (by rw [selected]; exact List.mem_cons_of_mem _ inside) different

theorem every_actual_prefix_retains_a_complete_compatible_representative
    (past : List (EventHistory.Stage (code := model.source.code))) :
    ∃ representative ∈ fibre model start (past.map Prod.fst) worker
        (LocalWithdrawal.reading model (EventHistory.execute start past) worker),
      EventStep.Matches representative (EventHistory.execute start past) := by
  obtain ⟨representative, inside, same⟩ := CausalLocalDomain.every_finite_actual_trace_has_a_compact_representative
    [start] start start List.mem_cons_self (EventStep.matches_self _) past
  refine ⟨representative, List.mem_filter.mpr ⟨inside, ?_⟩, same⟩
  exact decide_eq_true (congrArg (fun state : State model.source.code => state.frame.inbox worker) same.state)

theorem matched_sources_have_the_same_complete_view (left right : Cursor model.source.code)
    (same : EventStep.Matches left right) : view model worker left = view model worker right := by
  unfold view LocalWithdrawal.request
  rw [LocalClaimGate.matched_completed_sources_have_the_same_pending model left right same worker, same.state]

abbrev reaffirm := WithdrawalInquiry.reaffirm model worker

def allowed (value : Revoke (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Prop :=
  reaffirm model worker ∈ model.source.code.actions ∧ value ∈ model.source.code.actions ∧
    2 ≤ model.source.code.actionLimit ∧ Event.activate worker ∈ model.source.code.eventAlphabet ∧
      model.source.code.memoryReady signal = true ∧ model.source.code.siteParty worker ∈ Delegation.members model.scope.task
instance (value : Revoke (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Decidable (allowed model worker signal value) := by
  unfold allowed; infer_instance

def workFrom (observed : Query model start installed worker signal) := match observed with
  | .known (some value) .. => if allowed model worker signal value then [reaffirm model worker, value] else []
  | _ => []

theorem supportedFrom (observed : Query model start installed worker signal) : workFrom model start installed worker signal observed ∈ words model.source.code.actions model.source.code.actionLimit := by
  unfold workFrom
  split
  · split
    · rename_i admitted
      exact (mem_words_iff _ _ _).mpr ⟨admitted.2.2.1, by
        intro item inside
        rcases List.mem_cons.mp inside with same | later
        · exact same ▸ admitted.1
        · exact List.mem_singleton.mp later ▸ admitted.2.1⟩
    · exact (mem_words_iff _ _ _).mpr (by simp)
  · exact (mem_words_iff _ _ _).mpr (by simp)

def work := workFrom model start installed worker signal (query model start installed worker signal)

theorem supported : work model start installed worker signal ∈ words model.source.code.actions model.source.code.actionLimit :=
  supportedFrom model start installed worker signal _

def eventFrom (observed : Query model start installed worker signal) : LocalMove model.source.code worker :=
  match observed with
  | .ambiguous .. => (WithdrawalInquiry.reads model worker).headD (WithdrawalInquiry.waiting model worker)
  | .known (some _) .. => if workFrom model start installed worker signal observed = [] then WithdrawalInquiry.waiting model worker
      else if supported : Event.activate worker ∈ model.source.code.eventAlphabet then
        LocalWithdrawal.activation model worker supported else WithdrawalInquiry.waiting model worker
  | _ => WithdrawalInquiry.waiting model worker

def event := eventFrom model start installed worker signal (query model start installed worker signal)

structure Cell where
  word : List (Revoke (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  move : Move model.source.code

def cell : Cell model :=
  let observed := query model start installed worker signal
  ⟨workFrom model start installed worker signal observed,
    (eventFrom model start installed worker signal observed).val⟩

def table := Vector.ofFn fun site => Vector.ofFn (cell model start installed site)

def entry
    (cached : Vector (Vector (Cell model) model.source.code.signals) model.source.code.sites)
    (key : model.source.code.Key) : Cell model := (cached.get key.1).get key.2

theorem table_at (key : model.source.code.Key) :
    entry model (table model start installed) key = cell model start installed key.1 key.2 := by
  simp only [entry, table, Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

def protocol : Rule model.source.code :=
  let cached := table model start installed
  { work := ⟨fun key _ => (entry model cached key).word, by
      apply model.source.code.every_local_policy_is_enumerated
      intro key inside
      change (entry model (table model start installed) key).word ∈ _
      rw [table_at]
      exact supported model start installed key.1 key.2⟩
    events := fun key _ => ⟨(entry model cached key).move, by
      change (entry model (table model start installed) key).move ∈ _
      rw [table_at]
      exact (eventFrom model start installed key.1 key.2 (query model start installed key.1 key.2)).property⟩ }

theorem compiled_work_and_event_are_the_generated_local_cell (key : model.source.code.Key) :
    (protocol model start installed).work.val key (model.source.code.key_mem key) = work model start installed key.1 key.2 ∧
      ((protocol model start installed).events key (model.source.code.key_mem key)).val =
        (event model start installed key.1 key.2).val := by
  change (entry model (table model start installed) key).word = _ ∧ (entry model (table model start installed) key).move = _
  rw [table_at]
  exact ⟨rfl, rfl⟩

theorem every_nonempty_local_word_recovers_its_own_actual_pending_claim_and_revoke
    (past : List (EventHistory.Stage (code := model.source.code)))
    (nonempty : work model start (past.map Prod.fst) worker
      (LocalWithdrawal.reading model (EventHistory.execute start past) worker) ≠ []) :
    LocalClaimGate.pending model (EventHistory.execute start past) worker = true ∧
      work model start (past.map Prod.fst) worker (LocalWithdrawal.reading model (EventHistory.execute start past) worker) =
        [reaffirm model worker, LocalWithdrawal.request model (EventHistory.execute start past) worker] := by
  obtain ⟨representative, inside, same⟩ := every_actual_prefix_retains_a_complete_compatible_representative model start worker past
  cases selected : query model start (past.map Prod.fst) worker
      (LocalWithdrawal.reading model (EventHistory.execute start past) worker) with
  | unseen empty => simp [work, workFrom, selected] at nonempty
  | ambiguous first second left right different => simp [work, workFrom, selected] at nonempty
  | known value first actual uniform =>
    cases value with
    | none => simp [work, workFrom, selected] at nonempty
    | some value =>
      have admitted : allowed model worker (LocalWithdrawal.reading model (EventHistory.execute start past) worker) value := by
        by_contra absent
        simp [work, workFrom, selected, absent] at nonempty
      have precise := (matched_sources_have_the_same_complete_view model worker representative _ same).symm.trans
        (uniform _ inside)
      unfold view at precise
      split at precise
      · refine ⟨by assumption, ?_⟩
        simp only [work, workFrom, selected, if_pos admitted, Option.some.inj precise]
      · contradiction

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompactClaimGate
