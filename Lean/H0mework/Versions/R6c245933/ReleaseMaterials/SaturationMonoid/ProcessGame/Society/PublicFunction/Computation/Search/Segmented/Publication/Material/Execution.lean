import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Material.Observation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving.History

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Material.Execution
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix
open PublicFunction.Protocol.SymbolicAuthentication
open Publication.Learning.Paid

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat) (slots : Nat)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code) (ordinal : Nat)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code))
  (law : StageReception.Law model.source.code)
  (record : Material.Carrier model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)

  (initial : List (View (code := model.source.code)))

variable (rounds : Nat)

abbrev past := Observation.controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record

def seed : Publication.Learning.Paid.State model domain original record.plan.choice.policy.protocol (Deployment.actualHorizon model point) where
  past := past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record
  programme := record.plan.choice.policy.protocol
  beliefs := Observation.posterior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial
  within := by
    have kept := (Plan.eligible_iff model domain original reference worker quote quotas record.plan.announcements record.plan.choice.policy).mp record.plan.publicationPrefix
    have size := congrArg List.length kept
    simp only [List.length_take,List.length_append,List.length_replicate] at size
    have bounded := record.plan.choice.policy.protocol.bounded
    change (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length ≤ _
    simp only [past,Observation.controls,List.length_append,List.length_replicate]
    omega

  actualWithin := by simpa only [past,Observation.controls,List.length_append,List.length_replicate] using record.plan.within
  retained := by simpa only [past,Observation.controls,List.length_append,List.length_replicate] using
    (Plan.eligible_iff model domain original reference worker quote quotas record.plan.announcements record.plan.choice.policy).mp record.plan.publicationPrefix
  above := Commitment.admissible_plan_is_its_own_valid_reference model domain original reference _ record.plan.choice.policy.accepted

abbrev final := Driving.run receiver quote point rival (seed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) rounds
abbrev programme := (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).programme
abbrev stages := Driving.executed receiver quote point rival (seed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) rounds

theorem every_executed_stage_is_locked_in_the_original_complete_comparison :
    (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past = past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record ++ stages model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds :=
  Driving.no_old_or_new_actual_stage_is_replayed_or_erased _ _ _ _ _ _

theorem the_whole_driven_chain_retains_actual_origin_preserving_knowledge
    (covered : Knowledge.Contains initial point) :
    Knowledge.Contains (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).beliefs ((final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).current point rival) :=
  Driving.every_finite_feedback_chain_keeps_actual_local_knowledge _ _ _ _ _ _
    (Observation.the_received_reading_generates_an_origin_preserving_posterior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial covered)

theorem the_original_reference_and_all_opponents_are_protected :
    Selection.acceptable model domain original reference (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds) :=
  Selection.acceptable_trans model domain original _ _ _ (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).above record.plan.choice.policy.accepted

private theorem nondomination_survives_nonstrict_improvement
    {Policy Coordinate : Type} (axes : List Coordinate) (cost : Policy → Coordinate → ℚ)
    (old next other : Policy) (maximal : ¬ Distributed.Improves axes cost old other)
    (improved : Distributed.NoWorse axes cost next old) :
    ¬ Distributed.Improves axes cost next other := by
  intro strict
  exact maximal ⟨Distributed.noWorse_trans strict.1 improved,
    fun reverse => strict.2 (Distributed.noWorse_trans improved reverse)⟩

theorem no_original_paid_candidate_dominates_the_actual_driven_chain
    (other : Prefix.Candidate model domain original (reserved model original worker quote quotas) reference)
    (inside : other ∈ Prefix.candidates model domain original (reserved model original worker quote quotas) reference) :
    ¬ Distributed.Improves (Selection.axes (fuel := horizon domain) model domain)
      (Selection.benefit model domain original) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds) other.protocol :=
  nondomination_survives_nonstrict_improvement _ _ record.plan.choice.policy.protocol (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds) other.protocol
    (record.plan.choice.maximal other inside)
    (Selection.acceptance_bounds_every_benefit model domain original _ _ (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).above)

theorem the_original_paid_and_communication_prefix_is_retained :
    (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).controls.take (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length = past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record := by
  have retained := (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).retained
  have chain := every_executed_stage_is_locked_in_the_original_complete_comparison model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds
  have bound : (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length ≤ (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past.length := by
    calc
      _ ≤ (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length + (stages model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).length := Nat.le_add_right _ _
      _ = (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past.length := by
        have sizes := congrArg List.length chain
        simp only [List.length_append] at sizes
        simpa only [past,Observation.controls,List.length_append] using sizes.symm
  have shorter := congrArg (fun controls => controls.take (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length) retained
  rw [List.take_take,Nat.min_eq_left bound] at shorter
  rw [shorter,chain,List.take_append_of_le_length (Nat.le_refl _),List.take_length]

abbrev controls := Deployment.completeControls model domain original point (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds)
abbrev before := (Observation.atCommunication model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).point
abbrev future := (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).drop (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length
abbrev cutPoint (count : Nat) := Splice.install (before model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) rival ((future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).take count)
abbrev full := cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds (Deployment.actualHorizon model point)

theorem the_same_paid_and_communication_past_survives_normalization :
    (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).take (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length = past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record := by
  have within : (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length ≤ Deployment.actualHorizon model point := by
    simpa only [past,Observation.controls,List.length_append,List.length_replicate] using record.plan.within
  have clipped : (clip (Deployment.actualHorizon model point) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds)).controls.take (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length = past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record := by
    change ((programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).controls.take _).take _ = _
    rw [List.take_take,Nat.min_eq_left within]
    exact the_original_paid_and_communication_prefix_is_retained model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds
  exact Prefix.Padding.preserves_prefix original _ _ clipped

theorem only_the_new_post_communication_suffix_is_executed :
    full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds = Splice.install point.point rival (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds) := by
  have fits : (future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).length ≤ Deployment.actualHorizon model point := by
    change (List.drop _ (Prefix.Padding.controls original _)).length ≤ _
    rw [List.length_drop,Prefix.Padding.length]
    exact Nat.sub_le _ _
  change Splice.install _ rival ((future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).take _) = _
  rw [List.take_of_length_le fits]
  rw [show before model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record = Splice.install point.point rival (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) from
    Observation.the_after_receipt_point_is_the_actual_locked_prefix model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record]
  have joined := List.take_append_drop (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds)
  rw [the_same_paid_and_communication_past_survives_normalization] at joined
  change List.foldl _ (List.foldl _ point.point _) _ = _
  rw [←List.foldl_append,joined]
  rfl

theorem all_original_remaining_slots_are_actually_executed :
    (Cut.seed (full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds)).remaining = 0 := by
  rw [only_the_new_post_communication_suffix_is_executed]
  have remaining := Distributed.Recall.Information.Agency.Protocol.Continuation.Installation.Chain.fold_remaining
    (model := model) point.point rival (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds)
  change _ = _ - (Prefix.Padding.controls original _).length at remaining
  rw [Prefix.Padding.length] at remaining
  exact remaining.trans (Nat.sub_self _)

private theorem closing_has_a_stage {cursor : View (code := model.source.code)}
    {cache : Option (Cache model domain original reference worker quote quotas)} {jobs : List Nat}
    (execution : Scan model domain original reference worker quote quotas rival cursor cache jobs)
    (closing : PaidSlot model worker quote rival) (present : execution.closingReceipt = some closing) :
    0 < execution.rules.length := by
  cases execution with
  | empty | stopped => cases present
  | next => exact Nat.zero_lt_succ _

theorem actual_new_input_is_the_same_complete_original_evaluated_input :
    (full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).source.input =
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.source point.point original
        (clip (Deployment.actualHorizon model point) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds)) rival).input := by
  rw [only_the_new_post_communication_suffix_is_executed]
  have rules : (Segmented.trace model domain original reference worker quote quotas point rival).rules = reserved model original worker quote quotas := by
    have executed := (Segmented.trace model domain original reference worker quote quotas point rival).the_actual_source_contains_exactly_the_executed_fee_prefix
    simpa only [record.plan.complete,List.length_nil,Nat.sub_zero] using executed.2.1
  have positive := closing_has_a_stage model domain original reference worker quote quotas rival
    (Segmented.trace model domain original reference worker quote quotas point rival) record.payload.closing record.payload.sealed
  rw [rules,List.length_replicate] at positive
  have nonempty : controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds ≠ [] := by
    intro empty
    have size := Prefix.Padding.length original (clip (Deployment.actualHorizon model point) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds))
    change (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).length = _ at size
    rw [empty] at size
    have within := record.plan.within
    simp only [List.length_nil] at size
    omega
  rw [Splice.input_assembly _ _ original _ nonempty,Prefix.Padding.same_entire_source]

theorem the_new_programme_protects_the_original_actual_reference
    (covered : Continuation.Covered domain point.point) :
    Synthesis.accepts model.source.code (economicAxes point.point.source point.point.cut)
      (actualEvaluation model point.point original (clip (Deployment.actualHorizon model point) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds)) rival)
      (actualEvaluation model point.point original reference rival) := by
  have same : actualEvaluation model point.point original (clip (Deployment.actualHorizon model point) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds)) rival =
      actualEvaluation model point.point original (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds) rival := by
    apply stages_generate_the_same_complete_evaluation
    intro offset inside
    exact Continuation.Whole.Complete.clipping_keeps_each_consumed_stage _ _ _ _ inside
  rw [same]
  exact Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Observation.public_domain_acceptance_protects_every_covered_actual_source model point.point original
    (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds) rival domain covered reference
    (the_original_reference_and_all_opponents_are_protected model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds)

theorem every_actual_prefix_extends_to_the_same_new_source (count : Nat) :
    full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds = Splice.install (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds count) rival ((future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).drop count) := by
  have fits : (future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).length ≤ Deployment.actualHorizon model point := by
    change (List.drop _ (Prefix.Padding.controls original _)).length ≤ _
    rw [List.length_drop,Prefix.Padding.length]
    exact Nat.sub_le _ _
  change Splice.install _ rival ((future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).take _) = _
  rw [List.take_of_length_le fits]
  change List.foldl _ _ _ = List.foldl _ (List.foldl _ _ _) _
  rw [←List.foldl_append,List.take_append_drop]

theorem every_actual_driver_stage_is_present_once_in_the_final_source :
    (future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).take (stages model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).length = stages model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds := by
  have clipped : (clip (Deployment.actualHorizon model point) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds)).controls.take
      (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past.length = (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past := by
    change ((programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).controls.take _).take _ = _
    rw [List.take_take,Nat.min_eq_left (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).actualWithin]
    exact (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).retained
  have committed := Prefix.Padding.preserves_prefix original _ _ clipped
  change (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).take (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past.length = (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past at committed
  rw [every_executed_stage_is_locked_in_the_original_complete_comparison model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds] at committed
  have afterPast := congrArg (fun rules => rules.drop (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length) committed
  rw [List.drop_left] at afterPast
  simpa only [future,past,Observation.controls,List.drop_take,List.length_append,Nat.add_sub_cancel_left] using afterPast

theorem the_actual_driver_end_is_a_literal_prefix_of_the_same_final_source :
    cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds (stages model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).length = ((final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).current point rival).point := by
  change Splice.install (before model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) rival ((future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).take (stages model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).length) = _
  rw [every_actual_driver_stage_is_present_once_in_the_final_source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds,
    State.current_is_the_actual_control_prefix,
    every_executed_stage_is_locked_in_the_original_complete_comparison model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds,
    show before model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record = Splice.install point.point rival (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) from
      Observation.the_after_receipt_point_is_the_actual_locked_prefix model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record]
  change List.foldl _ (List.foldl _ point.point _) _ = List.foldl _ point.point _
  simp only [past,Observation.controls,List.foldl_append]

abbrev tail := clip (horizon domain) (Splice.word ((programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).controls.drop (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past.length))

theorem the_final_driven_tail_reconstructs_the_complete_original_programme :
    Prefix.extension (horizon domain) (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past (tail model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds) = programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds := by
  unfold tail
  rw [Prefix.tail_normalization_does_not_change_any_consumed_prefix_extension]
  have joined : (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past ++ (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).controls.drop (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past.length = (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).controls := by
    calc
      _ = (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).controls.take (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past.length ++
          (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).controls.drop (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past.length :=
        congrArg (fun earlier => earlier ++ (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).controls.drop (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past.length) (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).retained.symm
      _ = _ := List.take_append_drop _ _
  apply (Continuation.Whole.Program.mk.injEq ..).mpr
  change ((final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past ++ (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).controls.drop (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past.length).take (horizon domain) = _
  rw [joined,List.take_of_length_le (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).bounded]

theorem the_actual_paid_past_and_every_finite_continuation_are_independently_reviewed :
    Prefix.verify model domain original (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past reference (tail model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds) = true := by
  apply (Prefix.verify_iff _ _ _ _ _ _).mpr
  rw [the_final_driven_tail_reconstructs_the_complete_original_programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds]
  refine ⟨the_original_reference_and_all_opponents_are_protected model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds,?_⟩
  intro future accepted
  let appended := Splice.word ((record.plan.announcements ++ stages model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds) ++ future.2.controls)
  have same : Prefix.extension (horizon domain) (reserved model original worker quote quotas) appended =
      Prefix.extension (horizon domain) (final model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds).past future.2 := by
    rw [every_executed_stage_is_locked_in_the_original_complete_comparison model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds]
    unfold appended Prefix.extension Splice.word past Observation.controls clip Continuation.Whole.Complete.clip
    simp only [List.append_assoc]
  have originalAccepted : Selection.acceptable model domain original reference
      (Prefix.extension (horizon domain) (reserved model original worker quote quotas) appended) := by rw [same];exact accepted
  obtain ⟨candidate,included,identity⟩ := Prefix.every_accepted_completion_is_generated model domain original
    (reserved model original worker quote quotas) reference ⟨_,appended⟩ originalAccepted
  have maximal := no_original_paid_candidate_dominates_the_actual_driven_chain model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial rounds candidate included
  rw [identity,same] at maximal
  exact maximal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Material.Execution
