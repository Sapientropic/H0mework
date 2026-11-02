import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Runtime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Runtime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Observation

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Deployment
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
  (domain : List (Cursor model.source.code))
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code)

private theorem scan_budget {before : View (code := model.source.code)}
    {cache : Option (Cache model domain original reference worker quote quotas)} {jobs : List Nat}
    (execution : Scan model domain original reference worker quote quotas rival before cache jobs) :
    execution.rules.length ≤ (Cut.seed before.point).remaining := by
  induction execution with
  | empty | stopped => exact Nat.zero_le _
  | next before prior quota rest consumed later ih =>
      have positive : (Cut.seed before.point).remaining ≠ 0 := by
        intro empty
        simp only [Charge.trace,dif_pos empty,Cut.Trace.rules] at consumed
        cases consumed
      have actual := (Charge.trace quote worker before rival).final_is_generated_only_by_its_actual_single_cut_rules
      rw [consumed] at actual
      have remaining : (Cut.seed (Charge.trace quote worker before rival).final.point).remaining =
          (Cut.seed before.point).remaining-1 := by
        rw [actual]
        exact Installation.Chain.after_remaining (model := model) before.point _ rival
      change later.rules.length+1 ≤ _
      rw [remaining] at ih
      omega

private theorem closing_has_a_stage {before : View (code := model.source.code)}
    {cache : Option (Cache model domain original reference worker quote quotas)} {jobs : List Nat}
    (execution : Scan model domain original reference worker quote quotas rival before cache jobs)
    (closing : PaidSlot model worker quote rival) (present : execution.closingReceipt = some closing) :
    0 < execution.rules.length := by
  cases execution with
  | empty | stopped => cases present
  | next => exact Nat.zero_lt_succ _

abbrev paidFinal := (Sparse.trace model domain original reference worker quote quotas point rival).final.point
abbrev actualHorizon := Cut.horizon point.point.source point.point.entry point.point.cut
abbrev completeControls (programme : Program model.source.code (horizon domain)) :=
  Prefix.Padding.controls original (clip (actualHorizon model point) programme)

/-- Only the original root's arrived result selects controls. Padding executes
every remaining feedback cut, including stages represented by the last rule. -/
def future (ordinal : Nat) : List (Prefix.Rule model.source.code) :=
  match Runtime.read model domain original reference worker quote quotas point rival ordinal with
  | some (_,some finished) => match finished.choice with
    | some choice => (completeControls model domain original point choice.policy.protocol).drop quotas.length
    | none => []
  | _ => []

theorem future_fits_the_original_remaining_window (ordinal : Nat) :
    (future model domain original reference worker quote quotas point rival ordinal).length ≤ actualHorizon model point := by
  unfold future
  split
  · split
    · change (List.drop quotas.length (Prefix.Padding.controls original _)).length ≤ _
      rw [List.length_drop,Prefix.Padding.length]
      exact Nat.sub_le _ _
    · exact Nat.zero_le _
  · exact Nat.zero_le _

def cutPoint (ordinal count : Nat) : Cursor model.source.code :=
  Splice.install (paidFinal model domain original reference worker quote quotas point rival) rival
    ((future model domain original reference worker quote quotas point rival ordinal).take count)

abbrev full (ordinal : Nat) := cutPoint model domain original reference worker quote quotas point rival ordinal
  (actualHorizon model point)

variable (ordinal : Nat)
  (execution : Scan model domain original reference worker quote quotas rival point none quotas)
  (finished : Finished model domain original reference worker quote quotas)
  (choice : Prefix.Choice model domain original (reserved model original worker quote quotas) reference)
  (released : Runtime.read model domain original reference worker quote quotas point rival ordinal = some (execution,some finished))
  (selected : finished.choice = some choice)

include released in
theorem released_result_is_the_same_source_generated_cache :
    Sparse.result model domain original reference worker quote quotas point rival = some finished := by
  rw [Runtime.read_is_the_arrived_source_generated_outcome] at released
  unfold Runtime.available at released
  dsimp only at released
  split at released
  · exact congrArg Prod.snd (Option.some.inj released)
  · cases released

include released in
private theorem paid_prefix :
    paidFinal model domain original reference worker quote quotas point rival =
      Splice.install point.point rival (reserved model original worker quote quotas) ∧
    quotas.length ≤ horizon domain ∧ quotas.length ≤ actualHorizon model point ∧ 0 < quotas.length := by
  have made := released_result_is_the_same_source_generated_cache model domain original reference worker quote quotas point rival ordinal execution finished released
  obtain ⟨rules,actual,space⟩ := Sparse.a_released_result_has_executed_the_entire_fixed_fee_plan
    model domain original reference worker quote quotas point rival finished made
  obtain ⟨_,closing,present⟩ := Sparse.a_released_finished_cache_is_its_actual_payment_replay_and_has_a_closing_receipt
    model domain original reference worker quote quotas point rival finished made
  have budget := scan_budget model domain original reference worker quote quotas rival
    (Sparse.trace model domain original reference worker quote quotas point rival)
  have positive := closing_has_a_stage model domain original reference worker quote quotas rival
    (Sparse.trace model domain original reference worker quote quotas point rival) closing present
  rw [rules,List.length_replicate] at budget positive
  exact ⟨actual,space,budget,positive⟩

include released in
private theorem controls_keep_the_actual_fee_prefix :
    (completeControls model domain original point choice.policy.protocol).take quotas.length =
      reserved model original worker quote quotas := by
  obtain ⟨_,space,within,_⟩ := paid_prefix model domain original reference worker quote quotas point rival ordinal execution finished released
  have retained := Prefix.the_selected_plan_really_preserves_the_committed_control_prefix
    model domain original (reserved model original worker quote quotas) reference choice (by simpa using space)
  have within' : (reserved model original worker quote quotas).length ≤ actualHorizon model point := by simpa using within
  have normalized : (clip (actualHorizon model point) choice.policy.protocol).controls.take
      (reserved model original worker quote quotas).length = reserved model original worker quote quotas := by
    change (choice.policy.protocol.controls.take (actualHorizon model point)).take _ = _
    rw [List.take_take,Nat.min_eq_left within']
    exact retained
  exact (by simpa only [List.length_replicate] using
    Prefix.Padding.preserves_prefix original _ (reserved model original worker quote quotas) normalized)

include released selected in
theorem the_actual_deployment_is_the_entire_selected_window_without_repaying_its_prefix :
    full model domain original reference worker quote quotas point rival ordinal =
      Splice.install point.point rival (completeControls model domain original point choice.policy.protocol) := by
  have actual := (paid_prefix model domain original reference worker quote quotas point rival ordinal execution finished released).1
  have retained := controls_keep_the_actual_fee_prefix model domain original reference worker quote quotas point rival ordinal execution finished choice released
  have whole := List.take_append_drop quotas.length (completeControls model domain original point choice.policy.protocol)
  rw [retained] at whole
  simp only [full,cutPoint]
  rw [List.take_of_length_le (future_fits_the_original_remaining_window model domain original reference worker quote quotas point rival ordinal)]
  simp only [future,released,selected]
  rw [actual]
  change List.foldl _ (List.foldl _ point.point _) _ = _
  rw [←List.foldl_append,whole]
  rfl

include released selected in
theorem the_installed_input_is_the_complete_original_evaluated_input :
    (full model domain original reference worker quote quotas point rival ordinal).source.input =
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.source point.point original (clip (actualHorizon model point) choice.policy.protocol) rival).input := by
  rw [the_actual_deployment_is_the_entire_selected_window_without_repaying_its_prefix model domain original reference worker quote quotas point rival ordinal execution finished choice released selected]
  have paid := paid_prefix model domain original reference worker quote quotas point rival ordinal execution finished released
  have positive : 0 < actualHorizon model point := Nat.lt_of_lt_of_le paid.2.2.2 paid.2.2.1
  have nonempty : completeControls model domain original point choice.policy.protocol ≠ [] := by
    intro empty
    have size := Prefix.Padding.length original (clip (actualHorizon model point) choice.policy.protocol)
    change (completeControls model domain original point choice.policy.protocol).length = actualHorizon model point at size
    rw [empty] at size
    exact (Nat.ne_of_gt positive) size.symm
  rw [Splice.input_assembly _ _ original _ nonempty,Prefix.Padding.same_entire_source]

include released selected in
theorem the_actual_deployment_finishes_the_original_remaining_budget :
    (full model domain original reference worker quote quotas point rival ordinal).cut = point.point.cut+actualHorizon model point ∧
    (Cut.seed (full model domain original reference worker quote quotas point rival ordinal)).remaining = 0 := by
  rw [the_actual_deployment_is_the_entire_selected_window_without_repaying_its_prefix model domain original reference worker quote quotas point rival ordinal execution finished choice released selected]
  constructor
  · exact (Installation.Chain.fold_cut (model := model) point.point rival _).trans
      (congrArg (point.point.cut+·) (Prefix.Padding.length original _))
  · have remaining := Installation.Chain.fold_remaining (model := model) point.point rival
      (completeControls model domain original point choice.policy.protocol)
    change _ = _ - (Prefix.Padding.controls original _).length at remaining
    rw [Prefix.Padding.length] at remaining
    exact remaining.trans (Nat.sub_self _)

theorem the_charged_selected_programme_protects_every_covered_actual_source
    (covered : Continuation.Covered domain point.point) :
    Synthesis.accepts model.source.code (economicAxes point.point.source point.point.cut)
      (actualEvaluation model point.point original (clip (actualHorizon model point) choice.policy.protocol) rival)
      (actualEvaluation model point.point original reference rival) := by
  have same : actualEvaluation model point.point original (clip (actualHorizon model point) choice.policy.protocol) rival =
      actualEvaluation model point.point original choice.policy.protocol rival := by
    apply stages_generate_the_same_complete_evaluation
    intro offset inside
    exact Continuation.Whole.Complete.clipping_keeps_each_consumed_stage _ _ _ _ inside
  rw [same]
  exact Observation.public_domain_acceptance_protects_every_covered_actual_source model point.point original
    choice.policy.protocol rival domain covered reference choice.policy.accepted

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Deployment
