import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.History

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Renewal.Tail
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

theorem a_local_proposal_preserves_each_later_registered_stage
    (index : Nat) (later : state.past.length+1 ≤ index)
    (present : index < state.programme.controls.length) :
    (state.proposal reader).at original index = state.programme.at original index := by
  have within := present.trans_le state.programme.bounded
  change (((state.past ++ (state.learned reader :: state.programme.controls.drop (state.past.length+1))).take (horizon domain))[index]?).getD _ = _
  rw [List.getElem?_take_of_lt within]
  have grouped : state.past ++ (state.learned reader :: state.programme.controls.drop (state.past.length+1)) =
      (state.past ++ [state.learned reader]) ++ state.programme.controls.drop (state.past.length+1) := by
    simp only [List.append_assoc,List.singleton_append]
  rw [grouped,List.getElem?_append_right (by simpa only [List.length_append,List.length_singleton] using later),List.getElem?_drop]
  simp only [List.length_append,List.length_singleton]
  rw [Nat.add_sub_of_le later,List.getElem?_eq_getElem present,Option.getD_some]
  change _ = (state.programme.controls[index]?).getD _
  rw [List.getElem?_eq_getElem present,Option.getD_some]

theorem executing_a_cached_stage_keeps_its_complete_future (index : Nat) :
    (Driving.Progress.next state).programme.at original index = state.programme.at original index := by
  unfold Driving.Progress.next
  split
  · exact Commitment.stage original state.programme index
  · rfl

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

theorem an_actual_round_cannot_erase_any_still_future_registered_stage
    (index : Nat)
    (later : (Asynchronous.Round.next state reader unit point rival vocabulary encoding law).past.length ≤ index)
    (inside : index < horizon domain) :
    (Asynchronous.Round.next state reader unit point rival vocabulary encoding law).programme.at original index =
      state.programme.at original index := by
  change (Driving.Progress.next (Asynchronous.Round.afterService state reader unit point rival vocabulary encoding law)).programme.at original index = _
  rw [executing_a_cached_stage_keeps_its_complete_future]
  change (Driving.Round.service state reader unit point rival).next.programme.at original index = _
  cases made : Driving.Round.service state reader unit point rival with
  | unsupported => exact Commitment.stage original state.programme index
  | unreserved => exact Commitment.stage original state.programme index
  | unpaid => exact Commitment.stage original state.programme index
  | paid supported booked receipt decision =>
      cases decision with
      | refused => exact Commitment.stage original state.programme index
      | admitted accepted =>
          have paid : (Driving.Round.service state reader unit point rival).learned = true := by rw [made];rfl
          have two := Driving.Round.paid_service_is_followed_by_an_actual_selected_stage state reader unit point rival paid
          have history := congrArg List.length (Asynchronous.Round.every_attempt_and_executed_learning_stage_is_locked_into_past state reader unit point rival vocabulary encoding law)
          rw [Asynchronous.Round.the_same_actual_stage_word_is_retained,two] at history
          rw [made] at history
          simp only [List.length_append,List.length_singleton,Paid.Turn.rules] at history
          let carried := (Driving.Round.prepared state).carry (Paid.requestedRule reader (Driving.Round.quoted state unit) supported) booked
          have retained : carried.past.length+1 ≤ index := by
            simp only [carried,Paid.State.carry,Driving.Round.prepared,Driving.Progress.padded,List.length_append,List.length_singleton]
            omega
          have present : index < carried.programme.controls.length := by
            change index < (Commitment.padded original state.programme).controls.length
            rw [Commitment.padded_length]
            exact inside
          change (carried.proposal reader).at original index = _
          rw [a_local_proposal_preserves_each_later_registered_stage carried reader index retained present]
          exact Commitment.stage original state.programme index

variable (template : Program model.source.code (horizon domain))
def Keeps : Prop := ∀ index, state.past.length ≤ index → index < horizon domain →
  state.programme.at original index = template.at original index

theorem the_next_actual_round_keeps_the_original_future
    (retained : Keeps state template) :
    Keeps (Asynchronous.Round.next state reader unit point rival vocabulary encoding law) template := by
  intro index later inside
  have history := congrArg List.length (Asynchronous.Round.every_attempt_and_executed_learning_stage_is_locked_into_past state reader unit point rival vocabulary encoding law)
  simp only [List.length_append] at history
  exact (an_actual_round_cannot_erase_any_still_future_registered_stage state reader unit point rival vocabulary encoding law index later inside).trans
    (retained index (by omega) inside)

theorem every_actual_round_keeps_the_original_registered_future
    (retained : Keeps state template) (fuel : Nat) :
    Keeps (Asynchronous.run reader unit point rival vocabulary encoding law state fuel) template := by
  induction fuel generalizing state with
  | zero => exact retained
  | succ fuel ih => exact ih _ (the_next_actual_round_keeps_the_original_future state reader unit point rival vocabulary encoding law template retained)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Renewal.Tail
