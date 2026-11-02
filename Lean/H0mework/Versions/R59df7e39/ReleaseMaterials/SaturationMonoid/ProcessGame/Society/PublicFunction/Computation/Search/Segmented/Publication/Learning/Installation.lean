import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Proposal
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.Domain

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Installation
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix
open PublicFunction.Protocol.SymbolicAuthentication

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
  (record : Publication.Receipt.Published model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)

  (initial : List (View (code := model.source.code)))

abbrev past := Proposal.past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record
abbrev programme := Proposal.programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial
abbrev controls := Deployment.completeControls model domain original point (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)
abbrev before := (Observation.atCommunication model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).point
abbrev future := (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).drop (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length
abbrev cutPoint (count : Nat) := Splice.install (before model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) rival ((future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).take count)
abbrev full := cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial (Deployment.actualHorizon model point)

theorem the_same_paid_and_communication_past_survives_normalization :
    (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).take (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length = past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record := by
  have within : (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length ≤ Deployment.actualHorizon model point := by
    simpa only [past,Proposal.past,Observation.controls,List.length_append,List.length_replicate] using record.plan.within
  have clipped : (clip (Deployment.actualHorizon model point) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)).controls.take (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length = past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record := by
    change ((programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).controls.take _).take _ = _
    rw [List.take_take,Nat.min_eq_left within]
    exact Proposal.the_generated_programme_retains_the_entire_actual_paid_and_communication_past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial
  exact Prefix.Padding.preserves_prefix original _ _ clipped

theorem only_the_new_post_communication_suffix_is_executed :
    full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial = Splice.install point.point rival (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) := by
  have fits : (future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).length ≤ Deployment.actualHorizon model point := by
    change (List.drop _ (Prefix.Padding.controls original _)).length ≤ _
    rw [List.length_drop,Prefix.Padding.length]
    exact Nat.sub_le _ _
  change Splice.install _ rival ((future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).take _) = _
  rw [List.take_of_length_le fits]
  rw [show before model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record = Splice.install point.point rival (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) from
    Observation.the_after_receipt_point_is_the_actual_locked_prefix model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record]
  have joined := List.take_append_drop (past model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).length (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)
  rw [the_same_paid_and_communication_past_survives_normalization] at joined
  change List.foldl _ (List.foldl _ point.point _) _ = _
  rw [←List.foldl_append,joined]
  rfl

theorem all_original_remaining_slots_are_actually_executed :
    (Cut.seed (full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)).remaining = 0 := by
  rw [only_the_new_post_communication_suffix_is_executed]
  have remaining := Distributed.Recall.Information.Agency.Protocol.Continuation.Installation.Chain.fold_remaining
    (model := model) point.point rival (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)
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
    (full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).source.input =
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.source point.point original
        (clip (Deployment.actualHorizon model point) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)) rival).input := by
  rw [only_the_new_post_communication_suffix_is_executed]
  have ready := Deployment.released_result_is_the_same_source_generated_cache model domain original reference worker quote quotas point rival ordinal record.plan.execution record.plan.finished record.plan.arrived
  obtain ⟨rules,_,_⟩ := Segmented.a_released_result_has_executed_the_entire_fixed_fee_plan
    model domain original reference worker quote quotas point rival record.plan.finished ready
  have positive := closing_has_a_stage model domain original reference worker quote quotas rival
    (Segmented.trace model domain original reference worker quote quotas point rival) record.closing record.sealed
  rw [rules,List.length_replicate] at positive
  have nonempty : controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial ≠ [] := by
    intro empty
    have size := Prefix.Padding.length original (clip (Deployment.actualHorizon model point) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial))
    change (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).length = _ at size
    rw [empty] at size
    have within := record.plan.within
    simp only [List.length_nil] at size
    omega
  rw [Splice.input_assembly _ _ original _ nonempty,Prefix.Padding.same_entire_source]

theorem the_new_programme_protects_the_original_actual_reference
    (covered : Continuation.Covered domain point.point) :
    Synthesis.accepts model.source.code (economicAxes point.point.source point.point.cut)
      (actualEvaluation model point.point original (clip (Deployment.actualHorizon model point) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)) rival)
      (actualEvaluation model point.point original reference rival) := by
  have same : actualEvaluation model point.point original (clip (Deployment.actualHorizon model point) (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)) rival =
      actualEvaluation model point.point original (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) rival := by
    apply stages_generate_the_same_complete_evaluation
    intro offset inside
    exact Continuation.Whole.Complete.clipping_keeps_each_consumed_stage _ _ _ _ inside
  rw [same]
  exact Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Observation.public_domain_acceptance_protects_every_covered_actual_source model point.point original
    (programme model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) rival domain covered reference
    (Proposal.the_initial_reference_and_every_original_opponent_are_retained model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)

theorem every_actual_prefix_extends_to_the_same_new_source (count : Nat) :
    full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial = Splice.install (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial count) rival ((future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).drop count) := by
  have fits : (future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).length ≤ Deployment.actualHorizon model point := by
    change (List.drop _ (Prefix.Padding.controls original _)).length ≤ _
    rw [List.length_drop,Prefix.Padding.length]
    exact Nat.sub_le _ _
  change Splice.install _ rival ((future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial).take _) = _
  rw [List.take_of_length_le fits]
  change List.foldl _ _ _ = List.foldl _ (List.foldl _ _ _) _
  rw [←List.foldl_append,List.take_append_drop]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Installation
