import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Extension
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CatalogueHandoffSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)

structure Catalogue where
  actions : List (Request Party Good Port (Mandate.State Party Technology) Instrument)
  actionLimit : Nat
  histories : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  historyLimit : Nat
  events : Events old

variable (extra : Catalogue old)
-- Initial replay is already paid history. Enlarging its batch limit would
-- execute a different past; new catalogue events enter through future feedback.
abbrev supply : Extension.Supply old :=
  ⟨extra.actions,extra.actionLimit,extra.histories,extra.historyLimit,extra.events,0⟩
abbrev code := Extension.code old (supply old extra)

/-- Extend the action interface without reconstructing any installed source history or control. -/
def cursor (current : Cursor old) : Cursor (code old extra) :=
  ⟨current.reference,Extension.all_original_policies_remain_generated old (supply old extra) _ current.reference_generated,
    current.history,Extension.all_original_histories_remain_generated old (supply old extra) _ current.original,
    Extension.opponent old (supply old extra) current.opponent,current.side,
    Extension.input old (supply old extra) current.entry,current.overrides,current.cut,current.ownerStart⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem traceFrom (policy : old.Policy) (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (history : History) (rival : Opponent old) (n : Nat) (past : Events old) (f : old.Frame) :
    Reaction.traceFrom (code old extra) policy current history (Extension.opponent old (supply old extra) rival) n past
        (Extension.frame old (supply old extra) f) = Reaction.traceFrom old policy current history rival n past f := by
  induction n generalizing past f with
  | zero => rfl
  | succ n ih =>
    simp only [Reaction.traceFrom,Extension.opponent,Extension.forget_frame]
    cases chosen : rival history past f with
    | none => rfl
    | some event =>
      simp only [Extension.step_preserves_the_actual_frame]
      exact congrArg (List.cons event.val) (ih _ _)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem replay (policy : old.Policy)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (events : Events old) :
    (code old extra).replay policy current events =
      Extension.frame old (supply old extra) (old.replay policy current events) := by
  change events.foldl _ _ = _
  have fold (f : old.Frame) :
      events.foldl ((code old extra).step policy current) (Extension.frame old (supply old extra) f) =
        Extension.frame old (supply old extra) (events.foldl (old.step policy current) f) := by
    induction events generalizing f with
    | nil => rfl
    | cons head tail ih =>
      simp only [List.foldl_cons,Extension.step_preserves_the_actual_frame,ih]
  exact fold old.start

private theorem suffixBody (here : Cursor (code old extra))
    (stages : List (EventHistory.Stage (code := code old extra)))
    (location : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (early : location.round - old.initial.round - 1 < here.history.length + 1 + here.cut) :
    (EventHistory.execute here stages).source.body location = here.source.body location := by
  induction stages generalizing here with
  | nil => rfl
  | cons stage tail ih =>
    rcases stage with ⟨protocol,rival⟩
    have nextEarly : location.round - old.initial.round - 1 <
        (here.after protocol rival).history.length + 1 + (here.after protocol rival).cut := by
      change location.round - old.initial.round - 1 < here.history.length + 1 + (here.cut + 1)
      omega
    exact (ih (here.after protocol rival) nextEarly).trans
      (Future.earlier_body here.source here.entry here.cut (Cursor.controller here protocol rival)
        (term here.source here.entry here.cut protocol).val rfl location early)

variable (current : Cursor old) (original : current.side = .original)
include original

theorem policy : (cursor old extra current).source.policy? = current.source.policy? := by
  simp only [Machine.policy?,Machine.policyForSide,Cursor.source,cursor,original]

theorem frameFor (location : RawCurrent Party Good (Mandate.State Party Technology) Instrument) :
    Machine.frameFor (code old extra) (cursor old extra current).source.policy? current.history
      (cursor old extra current).opponent location =
      Extension.frame old (supply old extra) (Machine.frameFor old current.source.policy? current.history current.opponent location) := by
  have side : current.source.policy? = some current.reference := by
    simp only [Machine.policy?,Machine.policyForSide,Cursor.source,original]
  rw [policy old extra current original,side]
  simp only [Machine.frameFor,Machine.eventsFor,cursor]
  rw [show (code old extra).start = Extension.frame old (supply old extra) old.start from rfl]
  simp only [code,supply,Extension.code,Nat.max_zero]
  rw [traceFrom]
  exact replay old extra _ _ _

theorem initial : (cursor old extra current).source.feedbackInitial (cursor old extra current).entry =
    Extension.state old (supply old extra) (current.source.feedbackInitial current.entry) := by
  have mapped := frameFor old extra current original (old.historyCurrent current.history)
  have side : current.source.policy? = some current.reference := by
    simp only [Machine.policy?,Machine.policyForSide,Cursor.source,original]
  have past : (cursor old extra current).source.emissionEvents (old.historyCurrent current.history) =
      current.source.emissionEvents (old.historyCurrent current.history) := by
    simp only [Machine.emissionEvents,Machine.eventsFor,policy old extra current original,side]
    rw [show (code old extra).start = Extension.frame old (supply old extra) old.start from rfl]
    simpa only [code,supply,Extension.code,Nat.max_zero,cursor] using (traceFrom old extra current.reference _ current.history current.opponent old.eventLimit [] old.start)
  change Feedback.State.mk _ _ _ _ _ = _
  simp only [Machine.feedbackInitial,Machine.responseFrame]
  change Feedback.State.mk
    ((code old extra).law.next (old.historyCurrent current.history)
      (Machine.frameFor (code old extra) (cursor old extra current).source.policy? current.history
        (cursor old extra current).opponent (old.historyCurrent current.history)).word)
    (current.history ++ [(Machine.frameFor (code old extra) (cursor old extra current).source.policy? current.history
        (cursor old extra current).opponent (old.historyCurrent current.history)).word])
    ((cursor old extra current).source.emissionEvents (old.historyCurrent current.history))
    (Machine.frameFor (code old extra) (cursor old extra current).source.policy? current.history
        (cursor old extra current).opponent (old.historyCurrent current.history)) current.entry.budget = _
  rw [past,mapped]
  rfl

theorem feedbackPolicy (n : Nat) : (cursor old extra current).source.feedbackPolicy n = current.source.feedbackPolicy n := by
  unfold Machine.feedbackPolicy
  rw [policy old extra current original]
  rfl

theorem feedbackState (n : Nat) :
    (cursor old extra current).source.feedbackState (cursor old extra current).entry n =
      Extension.state old (supply old extra) (current.source.feedbackState current.entry n) := by
  induction n with
  | zero => exact initial old extra current original
  | succ n ih =>
    simp only [Machine.feedbackState,feedbackPolicy old extra current original,ih]
    exact Extension.advance_preserves_the_whole_actual_state old (supply old extra) _ _ _

theorem response (location : RawCurrent Party Good (Mandate.State Party Technology) Instrument) :
    (cursor old extra current).source.response location = current.source.response location :=
  congrArg Code.Frame.word (frameFor old extra current original location)

theorem laterResponse (location : RawCurrent Party Good (Mandate.State Party Technology) Instrument) (n : Nat) :
    (cursor old extra current).source.laterResponse location n = current.source.laterResponse location n := by
  change Feedback.word (code old extra) _ _ _ = Feedback.word old _ _ _
  rw [feedbackState old extra current original,feedbackPolicy old extra current original]
  exact Extension.word_preserves_the_actual_request old (supply old extra) _ _ _

theorem body (location : RawCurrent Party Good (Mandate.State Party Technology) Instrument) :
    (cursor old extra current).source.body location = current.source.body location := by
  simp only [Machine.body,List.getElem?_nil,
    laterResponse old extra current original,response old extra current original]
  rfl

theorem rawEvent (ordinal : Nat) :
    ProgrammeSource.rawEvent (cursor old extra current).source.input
        (ProgrammeHistory.visitAt current.source.input ordinal).current =
      ProgrammeSource.rawEvent current.source.input
        (ProgrammeHistory.visitAt current.source.input ordinal).current := by
  cases (ProgrammeHistory.visitAt current.source.input ordinal).current with
  | bootstrap => rfl
  | running location past => exact body old extra current original location

theorem financialAccounts (ordinal : Nat) :
    Native.Coupling.Match old current.source.input (cursor old extra current).source.input
      (Financial.accountAt current.source.input ordinal)
      (Financial.accountAt (cursor old extra current).source.input ordinal) :=
  Native.Coupling.History.complete_accounts old current.source.input (cursor old extra current).source.input rfl rfl
    ordinal (fun n _ => rawEvent old extra current original n)
    current.source.body (cursor old extra current).source.body rfl rfl ordinal (Nat.le_refl _)

theorem seed : EventStep.seed (cursor old extra current) =
    Extension.state old (supply old extra) (EventStep.seed current) :=
  feedbackState old extra current original current.cut

theorem completeFinancialPrefix (stages : List (EventHistory.Stage (code := code old extra)))
    (ordinal : Nat) (bounded : ordinal ≤ EventStep.boundary current) :
    Native.Coupling.Match old current.source.input (EventHistory.execute (cursor old extra current) stages).source.input
      (Financial.accountAt current.source.input ordinal)
      (Financial.accountAt (EventHistory.execute (cursor old extra current) stages).source.input ordinal) := by
  have events : ∀ n, n < EventStep.boundary current →
      ProgrammeSource.rawEvent (EventHistory.execute (cursor old extra current) stages).source.input
          (ProgrammeHistory.visitAt current.source.input n).current =
        ProgrammeSource.rawEvent current.source.input (ProgrammeHistory.visitAt current.source.input n).current := by
    intro n before
    cases view : (ProgrammeHistory.visitAt current.source.input n).current with
    | bootstrap => rfl
    | running location past =>
      change (EventHistory.execute (cursor old extra current) stages).source.body location = current.source.body location
      have rounds := ProgrammeHistory.visit_round current.source.input n
      rw [view] at rounds
      change location.round = old.initial.round + n at rounds
      have early : location.round - old.initial.round - 1 < current.history.length + 1 + current.cut := by
        change n < current.history.length + 2 + current.cut at before
        omega
      exact (suffixBody old extra (cursor old extra current) stages location early).trans
        (body old extra current original location)
  exact Native.Coupling.History.complete_accounts old current.source.input
    (EventHistory.execute (cursor old extra current) stages).source.input rfl rfl
    (EventStep.boundary current) events current.source.body
    (EventHistory.execute (cursor old extra current) stages).source.body rfl rfl ordinal bounded

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CatalogueHandoffSource
