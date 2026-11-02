import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving.Progress

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving.Round
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

abbrev prepared := Progress.padded state
abbrev quoted := Paid.Schedule.request (prepared state) unit
abbrev service := Paid.turn (prepared state) reader (quoted state unit) point rival
abbrev afterService := (service state reader unit point rival).next

/-- A paid update is physically executed before another request. An unavailable
service instead follows the already accepted cache, so time and messages advance. -/
def next := Progress.next (afterService state reader unit point rival)
def stages := (service state reader unit point rival).rules ++
  Progress.rules (afterService state reader unit point rival)

theorem every_attempt_and_executed_learning_stage_is_locked_into_past :
    (next state reader unit point rival).past = state.past ++ stages state reader unit point rival := by
  rw [next,Progress.the_next_cached_stage_is_paid_into_the_actual_past,
    Paid.Turn.every_reserved_stage_keeps_its_actual_attempt_on_refusal]
  change (state.past ++ _) ++ _ = _
  rw [List.append_assoc]
  rfl

theorem each_live_round_has_actual_progress (live : Progress.Live state) :
    state.past.length < (next state reader unit point rival).past.length := by
  have noRollback := Progress.no_actual_slot_is_rolled_back (afterService state reader unit point rival)
  have chain := Paid.Turn.every_reserved_stage_keeps_its_actual_attempt_on_refusal
    (service state reader unit point rival)
  have sizes := congrArg List.length chain
  simp only [List.length_append] at sizes
  change (afterService state reader unit point rival).past.length = state.past.length +
    (service state reader unit point rival).rules.length at sizes
  by_cases empty : (service state reader unit point rival).rules = []
  · have same : (afterService state reader unit point rival).past.length = state.past.length := by
      simpa only [empty,List.length_nil,Nat.add_zero] using sizes
    have room : Progress.Live (afterService state reader unit point rival) := by
      unfold Progress.Live
      rw [same]
      exact live
    rw [next,Progress.an_existing_live_slot_is_really_consumed _ room,same]
    exact Nat.lt_succ_self _
  · have positive : 0 < (service state reader unit point rival).rules.length := by
      cases same : (service state reader unit point rival).rules with
      | nil => exact False.elim (empty same)
      | cons => exact Nat.zero_lt_succ _
    change state.past.length < (Progress.next (afterService state reader unit point rival)).past.length
    omega

theorem actual_origin_knowledge_survives_both_phases
    (covered : Knowledge.Contains state.beliefs (state.current point rival)) :
    Knowledge.Contains (next state reader unit point rival).beliefs
      ((next state reader unit point rival).current point rival) :=
  Progress.actual_local_knowledge_survives_the_cached_stage _ point rival
    (Paid.Turn.actual_knowledge_survives_every_paid_or_refused_turn _ covered)

theorem paid_service_is_followed_by_an_actual_selected_stage
    (paid : (service state reader unit point rival).learned = true) :
    stages state reader unit point rival = (service state reader unit point rival).rules ++
      [(afterService state reader unit point rival).programme.at original
        (afterService state reader unit point rival).past.length] := by
  have live : Progress.Live (afterService state reader unit point rival) := by
    cases event : service state reader unit point rival with
    | unsupported | unreserved | unpaid => simp only [event,Paid.Turn.learned] at paid;cases paid
    | paid supported booked receipt decision =>
        have past := Paid.Turn.every_reserved_stage_keeps_its_actual_attempt_on_refusal
          (Paid.Turn.paid supported booked receipt decision)
        have length := congrArg List.length past
        simp only [Paid.Turn.rules,List.length_append,List.length_singleton] at length
        unfold afterService
        rw [event]
        constructor
        · rw [length];exact booked.1
        · rw [length];exact booked.2.1
  unfold stages Progress.rules
  rw [if_pos live]

theorem an_admitted_decision_really_executes_the_paying_readers_branch
    (supported : Paid.request (quoted state unit) ∈ words model.source.code.actions model.source.code.actionLimit)
    (booked : (prepared state).Booked (Paid.requestedRule reader (quoted state unit) supported))
    (receipt : Paid.funded (prepared state) reader (quoted state unit) point rival)
    (accepted : Selection.acceptable model domain original
      ((prepared state).carry (Paid.requestedRule reader (quoted state unit) supported) booked).programme
      (((prepared state).carry (Paid.requestedRule reader (quoted state unit) supported) booked).proposal reader))
    (made : service state reader unit point rival = .paid supported booked receipt (.admitted accepted)) :
    stages state reader unit point rival =
      [Paid.requestedRule reader (quoted state unit) supported,
        ((prepared state).carry (Paid.requestedRule reader (quoted state unit) supported) booked).learned reader] := by
  have paid : (service state reader unit point rival).learned = true := by rw [made];rfl
  rw [paid_service_is_followed_by_an_actual_selected_stage state reader unit point rival paid]
  unfold afterService
  rw [made]
  let carried := (prepared state).carry (Paid.requestedRule reader (quoted state unit) supported) booked
  change [Paid.requestedRule reader (quoted state unit) supported,
    (carried.proposal reader).at original carried.past.length] = _
  have chosen : (carried.proposal reader).at original carried.past.length = carried.learned reader := by
    change ((carried.past ++ (carried.learned reader :: carried.programme.controls.drop (carried.past.length+1))).take (horizon domain))[carried.past.length]?.getD _ = _
    have live : carried.past.length < horizon domain := by
      simpa only [carried,Paid.State.carry,List.length_append,List.length_singleton] using booked.2.1
    rw [List.getElem?_take_of_lt live,List.getElem?_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
  rw [chosen]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving.Round
