import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Reception
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving.History

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Round
open Publication.Learning Publication.Learning.Paid
open PublicFunction.Protocol.SymbolicAuthentication
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
  (state : Paid.State model domain original baseline actualHorizon)
  (reader : Fin model.source.code.sites)
  (unit : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (point : View (code := model.source.code)) (rival : Opponent model.source.code)

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev prepared := Driving.Round.prepared state
abbrev quoted := Driving.Round.quoted state unit
abbrev service := Driving.Round.service state reader unit point rival

def afterService := Reception.refresh point rival reader vocabulary encoding law state.past.length
  (Driving.Round.afterService state reader unit point rival)

def next :=
  let serviced := afterService state reader unit point rival vocabulary encoding law
  Reception.refresh point rival reader vocabulary encoding law serviced.past.length (Driving.Progress.next serviced)

def stages := (service state reader unit point rival).rules ++
  Driving.Progress.rules (afterService state reader unit point rival vocabulary encoding law)

theorem the_same_actual_stage_word_is_retained :
    stages state reader unit point rival vocabulary encoding law = Driving.Round.stages state reader unit point rival := rfl

theorem every_attempt_and_executed_learning_stage_is_locked_into_past :
    (next state reader unit point rival vocabulary encoding law).past =
      state.past ++ stages state reader unit point rival vocabulary encoding law := by
  change (Driving.Progress.next (afterService state reader unit point rival vocabulary encoding law)).past = _
  rw [Driving.Progress.the_next_cached_stage_is_paid_into_the_actual_past]
  have charged := Paid.Turn.every_reserved_stage_keeps_its_actual_attempt_on_refusal (service state reader unit point rival)
  change (afterService state reader unit point rival vocabulary encoding law).past = state.past ++ (service state reader unit point rival).rules at charged
  rw [charged,List.append_assoc]
  rfl

theorem each_live_round_has_actual_progress (live : Driving.Progress.Live state) :
    state.past.length < (next state reader unit point rival vocabulary encoding law).past.length := by
  rw [every_attempt_and_executed_learning_stage_is_locked_into_past,the_same_actual_stage_word_is_retained]
  rw [←Driving.Round.every_attempt_and_executed_learning_stage_is_locked_into_past]
  exact Driving.Round.each_live_round_has_actual_progress state reader unit point rival live

theorem actual_origin_knowledge_survives_both_phases
    (covered : Knowledge.Contains state.beliefs (state.current point rival)) :
    Knowledge.Contains (next state reader unit point rival vocabulary encoding law).beliefs
      ((next state reader unit point rival vocabulary encoding law).current point rival) := by
  have charged := Paid.Turn.actual_knowledge_survives_every_paid_or_refused_turn (service state reader unit point rival) covered
  have received := Reception.every_actual_new_receipt_preserves_actual_knowledge point rival reader vocabulary encoding law
    (Driving.Round.afterService state reader unit point rival).past state.past.length
    (Driving.Round.afterService state reader unit point rival).beliefs charged
  have executed := Driving.Progress.actual_local_knowledge_survives_the_cached_stage
    (afterService state reader unit point rival vocabulary encoding law) point rival received
  exact Reception.every_actual_new_receipt_preserves_actual_knowledge point rival reader vocabulary encoding law
    (Driving.Progress.next (afterService state reader unit point rival vocabulary encoding law)).past
    (afterService state reader unit point rival vocabulary encoding law).past.length
    (Driving.Progress.next (afterService state reader unit point rival vocabulary encoding law)).beliefs executed

abbrev serviceReception := Reception.generate point rival reader vocabulary encoding law
  (Driving.Round.afterService state reader unit point rival).past state.past.length
abbrev stageReception := Reception.generate point rival reader vocabulary encoding law
  (Driving.Progress.next (afterService state reader unit point rival vocabulary encoding law)).past
  (afterService state reader unit point rival vocabulary encoding law).past.length

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Round
