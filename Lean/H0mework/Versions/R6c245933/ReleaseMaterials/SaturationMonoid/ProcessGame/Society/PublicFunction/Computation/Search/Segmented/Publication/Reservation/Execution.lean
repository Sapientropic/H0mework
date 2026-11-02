import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Plan

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Execution
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat) (slots : Nat)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code) (ordinal : Nat)

abbrev full := Reservation.full model domain original reference worker receiver quote quotas slots point rival ordinal
abbrev future := Reservation.future model domain original reference worker receiver quote quotas slots point rival ordinal
abbrev cutPoint := Reservation.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal

theorem future_fits : (future model domain original reference worker receiver quote quotas slots point rival ordinal).length ≤ Deployment.actualHorizon model point := by
  unfold future Reservation.future
  split
  · exact Nat.zero_le _
  · change (List.drop quotas.length (Prefix.Padding.controls original _)).length ≤ _
    rw [List.length_drop,Prefix.Padding.length]
    exact Nat.sub_le _ _

theorem each_actual_prefix_extends_to_the_same_source (count : Nat) :
    full model domain original reference worker receiver quote quotas slots point rival ordinal =
      Splice.install (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count) rival
        ((future model domain original reference worker receiver quote quotas slots point rival ordinal).drop count) := by
  change Splice.install _ rival ((future model domain original reference worker receiver quote quotas slots point rival ordinal).take _) = _
  rw [List.take_of_length_le (future_fits model domain original reference worker receiver quote quotas slots point rival ordinal)]
  change List.foldl _ _ _ = List.foldl _ (List.foldl _ _ _) _
  rw [←List.foldl_append,List.take_append_drop]

variable (selected : Reservation.Selection model domain original reference worker receiver quote quotas slots point rival ordinal)
  (made : Reservation.select model domain original reference worker receiver quote quotas slots point rival ordinal = some selected)

abbrev controls := Deployment.completeControls model domain original point selected.plan.choice.policy.protocol

include selected in
private theorem original_paid_prefix :
    Deployment.paidFinal model domain original reference worker quote quotas point rival =
      Splice.install point.point rival (reserved model original worker quote quotas) ∧ quotas.length ≤ horizon domain := by
  have arrived := Deployment.released_result_is_the_same_source_generated_cache model domain original reference worker quote quotas point rival ordinal
    selected.plan.execution selected.plan.finished selected.plan.arrived
  obtain ⟨_,actual,within⟩ := Segmented.a_released_result_has_executed_the_entire_fixed_fee_plan
    model domain original reference worker quote quotas point rival selected.plan.finished arrived
  exact ⟨actual,within⟩

theorem the_complete_installed_controls_retain_every_paid_and_announcement_slot :
    (controls model domain original reference worker receiver quote quotas slots point rival ordinal selected).take
      (quotas.length+selected.plan.announcements.length) = reserved model original worker quote quotas ++ selected.plan.announcements := by
  exact Publication.Installation.the_complete_installed_controls_retain_every_paid_and_announcement_slot
    model domain original reference worker receiver quote quotas slots point rival ordinal selected.plan

theorem the_actual_controls_retain_the_new_receiver_fee :
    (controls model domain original reference worker receiver quote quotas slots point rival ordinal selected).take
      (quotas.length+selected.plan.announcements.length+1) =
      Reservation.reservedBlock model original worker receiver quote quotas selected.plan.announcements := by
  have retained := (Reservation.eligible_iff model domain original reference worker receiver quote quotas selected.plan.announcements selected.plan.choice.policy).mp selected.reservedNext
  have size : (Reservation.reservedBlock model original worker receiver quote quotas selected.plan.announcements).length =
      quotas.length+selected.plan.announcements.length+1 := by simp [Reservation.reservedBlock,Segmented.reserved,Nat.add_assoc]
  have clipped : (clip (Deployment.actualHorizon model point) selected.plan.choice.policy.protocol).controls.take
      (Reservation.reservedBlock model original worker receiver quote quotas selected.plan.announcements).length =
      Reservation.reservedBlock model original worker receiver quote quotas selected.plan.announcements := by
    change (selected.plan.choice.policy.protocol.controls.take _).take _ = _
    rw [size,List.take_take,Nat.min_eq_left (Nat.le_of_lt selected.actualRoom)]
    exact retained
  simpa only [size] using Prefix.Padding.preserves_prefix original _ _ clipped

include made in
theorem the_receiver_fee_is_the_actual_next_post_communication_stage :
    (future model domain original reference worker receiver quote quotas slots point rival ordinal).take
      (selected.plan.announcements.length+1) = selected.plan.announcements ++ [Reservation.fee model original receiver quote] := by
  simp only [future,Reservation.future,made]
  have retained := the_actual_controls_retain_the_new_receiver_fee model domain original reference worker receiver quote quotas slots point rival ordinal selected
  have dropped := congrArg (List.drop quotas.length) retained
  simpa only [Reservation.reservedBlock,List.append_assoc,List.drop_take,List.drop_append,List.length_replicate,Nat.sub_self,List.drop_zero,
    Nat.add_assoc,Nat.zero_sub,Nat.add_sub_cancel_left,List.nil_append,Segmented.reserved,List.drop_replicate,List.replicate_zero] using dropped

include made in
theorem the_actual_remaining_word_begins_with_the_registered_communication_programme :
    (future model domain original reference worker receiver quote quotas slots point rival ordinal).take selected.plan.announcements.length = selected.plan.announcements := by
  simp only [future,Reservation.future,made]
  have retained := the_complete_installed_controls_retain_every_paid_and_announcement_slot model domain original reference worker receiver quote quotas slots point rival ordinal selected
  have dropped := congrArg (List.drop quotas.length) retained
  simpa only [List.drop_take,List.drop_append,List.length_replicate,Nat.sub_self,List.drop_zero,
    Nat.add_assoc,Nat.zero_sub,Nat.add_sub_cancel_left,List.nil_append,Segmented.reserved,List.drop_replicate,List.replicate_zero] using dropped

include made in
theorem the_actual_communication_cut_is_the_paid_source_followed_by_the_registered_programme :
    cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal selected.plan.announcements.length =
      Splice.install (Deployment.paidFinal model domain original reference worker quote quotas point rival) rival selected.plan.announcements := by
  change Splice.install _ rival ((future model domain original reference worker receiver quote quotas slots point rival ordinal).take _) = _
  rw [the_actual_remaining_word_begins_with_the_registered_communication_programme model domain original reference worker receiver quote quotas slots point rival ordinal selected made]

include made in
theorem the_actual_full_window_retains_the_selected_programme_and_all_communication_costs :
    full model domain original reference worker receiver quote quotas slots point rival ordinal =
      Splice.install point.point rival (controls model domain original reference worker receiver quote quotas slots point rival ordinal selected) := by
  have actual := (original_paid_prefix model domain original reference worker receiver quote quotas slots point rival ordinal selected).1
  have retained := the_complete_installed_controls_retain_every_paid_and_announcement_slot model domain original reference worker receiver quote quotas slots point rival ordinal selected
  have feeRetained := congrArg (List.take quotas.length) retained
  rw [List.take_take,Nat.min_eq_left (Nat.le_add_right _ _),List.take_append_of_le_length (by simp)] at feeRetained
  simp only [List.take_replicate,Nat.min_self] at feeRetained
  have whole := List.take_append_drop quotas.length (controls model domain original reference worker receiver quote quotas slots point rival ordinal selected)
  rw [feeRetained] at whole
  simp only [full,Reservation.full,Reservation.cutPoint]
  rw [List.take_of_length_le (future_fits model domain original reference worker receiver quote quotas slots point rival ordinal)]
  simp only [future,Reservation.future,made]
  rw [actual]
  change List.foldl _ (List.foldl _ point.point _) _ = _
  rw [←List.foldl_append,whole]
  rfl

include made in
theorem the_complete_actual_budget_is_consumed :
    (Cut.seed (full model domain original reference worker receiver quote quotas slots point rival ordinal)).remaining = 0 := by
  rw [the_actual_full_window_retains_the_selected_programme_and_all_communication_costs model domain original reference worker receiver quote quotas slots point rival ordinal selected made]
  have remaining := Installation.Chain.fold_remaining (model := model) point.point rival
    (controls model domain original reference worker receiver quote quotas slots point rival ordinal selected)
  change _ = _ - (Prefix.Padding.controls original _).length at remaining
  rw [Prefix.Padding.length] at remaining
  exact remaining.trans (Nat.sub_self _)


private theorem closing_has_a_stage {before : View (code := model.source.code)}
    {cache : Option (Cache model domain original reference worker quote quotas)} {jobs : List Nat}
    (execution : Scan model domain original reference worker quote quotas rival before cache jobs)
    (closing : PaidSlot model worker quote rival) (present : execution.closingReceipt = some closing) :
    0 < execution.rules.length := by
  cases execution with
  | empty | stopped => cases present
  | next => exact Nat.zero_lt_succ _

include made in
theorem the_original_evaluated_input_includes_every_actual_communication_cost :
    (full model domain original reference worker receiver quote quotas slots point rival ordinal).source.input =
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.source point.point original
        (clip (Deployment.actualHorizon model point) selected.plan.choice.policy.protocol) rival).input := by
  rw [the_actual_full_window_retains_the_selected_programme_and_all_communication_costs model domain original reference worker receiver quote quotas slots point rival ordinal selected made]
  have ready := Deployment.released_result_is_the_same_source_generated_cache model domain original reference worker quote quotas point rival ordinal
    selected.plan.execution selected.plan.finished selected.plan.arrived
  obtain ⟨rules,_,_⟩ := Segmented.a_released_result_has_executed_the_entire_fixed_fee_plan
    model domain original reference worker quote quotas point rival selected.plan.finished ready
  obtain ⟨_,closing,present⟩ := Segmented.a_released_finished_cache_is_its_actual_payment_replay_and_has_a_closing_receipt
    model domain original reference worker quote quotas point rival selected.plan.finished ready
  have positive := closing_has_a_stage model domain original reference worker quote quotas rival
    (Segmented.trace model domain original reference worker quote quotas point rival) closing present
  rw [rules,List.length_replicate] at positive
  have nonempty : controls model domain original reference worker receiver quote quotas slots point rival ordinal selected ≠ [] := by
    intro empty
    have size := Prefix.Padding.length original (clip (Deployment.actualHorizon model point) selected.plan.choice.policy.protocol)
    change (controls model domain original reference worker receiver quote quotas slots point rival ordinal selected).length = _ at size
    rw [empty] at size
    have within := selected.plan.within
    simp only [List.length_nil] at size
    omega
  rw [Splice.input_assembly _ _ original _ nonempty,Prefix.Padding.same_entire_source]

theorem the_selected_publication_plan_keeps_the_original_actual_full_responsibility_contract
    (covered : Continuation.Covered domain point.point) :
    Synthesis.accepts model.source.code (economicAxes point.point.source point.point.cut)
      (actualEvaluation model point.point original (clip (Deployment.actualHorizon model point) selected.plan.choice.policy.protocol) rival)
      (actualEvaluation model point.point original reference rival) :=
  Deployment.the_charged_selected_programme_protects_every_covered_actual_source model domain original reference worker quote quotas point rival selected.plan.choice covered

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Execution
