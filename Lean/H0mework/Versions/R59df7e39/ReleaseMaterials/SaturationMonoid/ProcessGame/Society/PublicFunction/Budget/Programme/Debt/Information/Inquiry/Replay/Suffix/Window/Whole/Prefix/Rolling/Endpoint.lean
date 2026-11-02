import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Runtime

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Endpoint
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {views : List (View (code := model.source.code))} {original : Prefix.Rule model.source.code}
  {reference : Program model.source.code (horizon (Runtime.domain model views))}
  (work : Work model (Runtime.domain model views) original reference)
  (empty : work.past = []) (actual : View (code := model.source.code))
  (covered : Knowledge.Contains views actual) (rival : Opponent model.source.code)

abbrev count := Cut.horizon actual.point.source actual.point.entry actual.point.cut

include empty covered in
theorem the_actual_window_generates_exactly_its_original_number_of_stages :
    (run work (count actual)).past.length = count actual := by
  have finite := Knowledge.cursor_covered views actual covered
  obtain ⟨representative,inside,matched⟩ := finite
  have bounded := Continuation.Whole.Complete.each_remaining_horizon_is_generated
    (Runtime.domain model views) representative inside
  rw [matched.horizon] at bounded
  rw [every_generated_prefix_length,empty,List.length_nil,Nat.zero_add,Nat.min_eq_left bounded]

include empty covered in
theorem the_entire_actual_chain_keeps_the_original_full_responsibility_comparison :
    Synthesis.accepts model.source.code (economicAxes actual.point.source actual.point.cut)
      (actualEvaluation model actual.point original (Splice.word (run work (count actual)).past) rival)
      (actualEvaluation model actual.point original reference rival) := by
  have length := the_actual_window_generates_exactly_its_original_number_of_stages work empty actual covered
  have same : actualEvaluation model actual.point original (Splice.word (run work (count actual)).past) rival =
      actualEvaluation model actual.point original (run work (count actual)).programme rival := by
    apply stages_generate_the_same_complete_evaluation
    intro offset inside
    exact Commitment.retained_stages original _ _ (run work (count actual)).retained offset (by rw [length];exact inside)
  rw [same]
  exact Runtime.the_current_future_completion_protects_the_same_original_actual_reference
    model views original reference work (count actual) actual rival covered

include empty covered in
theorem the_actual_chain_consumes_exactly_its_original_unspent_budget :
    (seed (Runtime.execute model views original reference work (count actual) actual rival)).remaining = 0 := by
  have length := the_actual_window_generates_exactly_its_original_number_of_stages work empty actual covered
  by_cases positive : 0 < count actual
  · have nonempty : (run work (count actual)).past ≠ [] := by
      intro none
      rw [none,List.length_nil] at length
      omega
    have states := Splice.states_assembly actual.point rival original (run work (count actual)).past nonempty
    have cut : (Runtime.execute model views original reference work (count actual) actual rival).cut =
        actual.point.cut+(run work (count actual)).past.length :=
      Installation.Chain.fold_cut (model := model) actual.point rival _
    have same : seed (Runtime.execute model views original reference work (count actual) actual rival) =
        seed (Whole.Runtime.execute actual.point original (Splice.word (run work (count actual)).past) rival) := by
      change (Runtime.execute model views original reference work (count actual) actual rival).source.feedbackState
        (Runtime.execute model views original reference work (count actual) actual rival).entry
        (Runtime.execute model views original reference work (count actual) actual rival).cut = _
      have index := cut.trans (congrArg (actual.point.cut+·) length)
      rw [index]
      exact congrFun states _
    rw [same]
    exact Whole.Runtime.the_whole_word_consumes_exactly_its_original_remaining_budget _ _ _ _
  · have zero : count actual = 0 := by omega
    change (seed (Splice.install actual.point rival (run work (count actual)).past)).remaining = 0
    have none : (run work (count actual)).past = [] := List.eq_nil_of_length_eq_zero (length.trans zero)
    rw [none]
    change (seed actual.point).remaining = 0
    exact zero

include empty covered in
theorem the_completed_chain_is_its_verified_original_whole_word_input
    (positive : 0 < count actual) :
    (Runtime.execute model views original reference work (count actual) actual rival).source.input =
      (source actual.point original (Splice.word (run work (count actual)).past) rival).input := by
  have length := the_actual_window_generates_exactly_its_original_number_of_stages work empty actual covered
  apply Splice.input_assembly actual.point rival original _
  intro none
  rw [none,List.length_nil] at length
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Endpoint
