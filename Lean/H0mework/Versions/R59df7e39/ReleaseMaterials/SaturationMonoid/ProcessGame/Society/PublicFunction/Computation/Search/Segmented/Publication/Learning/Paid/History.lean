import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Step

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {domain : List (Cursor model.source.code)} {original : Prefix.Rule model.source.code}
  {baseline : Program model.source.code (horizon domain)} {actualHorizon : Nat}
  (state : State model domain original baseline actualHorizon)
  (reader : Fin model.source.code.sites)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code)

abbrev Requests := List (Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

structure Entry where
  before : State model domain original baseline actualHorizon
  quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  event : Turn before reader quote point rival
  generated : event = turn before reader quote point rival

def audit (state : State model domain original baseline actualHorizon)
    (reader : Fin model.source.code.sites)
    (point : View (code := model.source.code)) (rival : Opponent model.source.code) :
    Requests (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument) →
      List (Entry (model := model) (domain := domain) (original := original)
        (baseline := baseline) (actualHorizon := actualHorizon) reader point rival)
  | [] => []
  | quote :: rest => ⟨state,quote,turn state reader quote point rival,rfl⟩ ::
      audit (turn state reader quote point rival).next reader point rival rest

def run (state : State model domain original baseline actualHorizon)
    (reader : Fin model.source.code.sites)
    (point : View (code := model.source.code)) (rival : Opponent model.source.code) : Requests (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) → State model domain original baseline actualHorizon
  | [] => state
  | quote :: rest => run (turn state reader quote point rival).next reader point rival rest

def paidCount (state : State model domain original baseline actualHorizon)
    (reader : Fin model.source.code.sites)
    (point : View (code := model.source.code)) (rival : Opponent model.source.code) : Requests (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) → Nat
  | [] => 0
  | quote :: rest => (if (turn state reader quote point rival).learned then 1 else 0) +
      paidCount (turn state reader quote point rival).next reader point rival rest

def executed (state : State model domain original baseline actualHorizon)
    (reader : Fin model.source.code.sites)
    (point : View (code := model.source.code)) (rival : Opponent model.source.code) : Requests (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) → List (Prefix.Rule model.source.code)
  | [] => []
  | quote :: rest => (turn state reader quote point rival).rules ++
      executed (turn state reader quote point rival).next reader point rival rest

variable (requests : Requests (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem no_old_or_new_paid_stage_is_replayed_or_erased :
    (run state reader point rival requests).past = state.past ++ executed state reader point rival requests := by
  induction requests generalizing state with
  | nil => exact (List.append_nil _).symm
  | cons quote rest ih =>
      change (run (turn state reader quote point rival).next reader point rival rest).past = _
      rw [ih,Turn.every_reserved_stage_keeps_its_actual_attempt_on_refusal,List.append_assoc]
      rfl

theorem every_finite_feedback_chain_keeps_actual_local_knowledge
    (covered : Knowledge.Contains state.beliefs (state.current point rival)) :
    Knowledge.Contains (run state reader point rival requests).beliefs
      ((run state reader point rival requests).current point rival) := by
  induction requests generalizing state with
  | nil => exact covered
  | cons quote rest ih =>
      exact ih _ (Turn.actual_knowledge_survives_every_paid_or_refused_turn _ covered)

theorem the_paid_chain_is_the_actual_execution_of_its_generated_rules :
    (run state reader point rival requests).current point rival =
      Window.Observed.Transcript.actualView (executed state reader point rival requests) (state.current point rival) rival := by
  change Window.Observed.Transcript.actualView _ point rival = _
  rw [no_old_or_new_paid_stage_is_replayed_or_erased]
  unfold Window.Observed.Transcript.actualView
  rw [List.foldl_append]
  rfl

theorem an_unpaid_next_service_preserves_the_cached_programme
    (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (unpaid : ¬ funded state reader quote point rival) :
    (run state reader point rival [quote]).programme = state.programme :=
  Turn.no_unpaid_turn_runs_the_new_solver _ unpaid

theorem every_round_reuses_the_actual_last_cache_and_current
    (before after : Requests (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :
    run state reader point rival (before ++ after) =
      run (run state reader point rival before) reader point rival after := by
  induction before generalizing state with
  | nil => rfl
  | cons quote rest ih => exact ih _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid
