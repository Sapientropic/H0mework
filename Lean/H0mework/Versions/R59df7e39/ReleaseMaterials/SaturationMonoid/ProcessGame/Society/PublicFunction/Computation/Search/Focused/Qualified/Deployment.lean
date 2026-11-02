import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Finish
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Runtime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Observation

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Deployment
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
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (allocation : List Allocation) (announcements : List (Rule model.source.code))
  (point : View (code := model.source.code)) (rival : Opponent model.source.code) (send : Rule model.source.code)

private theorem scan_budget {before : View (code := model.source.code)}
    {cache : Option (Sparse.Cache model domain original reference worker quote (globalQuotas allocation))} {jobs : List Nat}
    (execution : Sparse.Scan model domain original reference worker quote (globalQuotas allocation) rival before cache jobs) :
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
    {cache : Option (Sparse.Cache model domain original reference worker quote (globalQuotas allocation))} {jobs : List Nat}
    (execution : Sparse.Scan model domain original reference worker quote (globalQuotas allocation) rival before cache jobs)
    (closing : Sparse.PaidSlot model worker quote rival) (present : execution.closingReceipt = some closing) :
    0 < execution.rules.length := by
  cases execution with
  | empty | stopped => cases present
  | next => exact Nat.zero_lt_succ _

abbrev actualHorizon := Cut.horizon point.point.source point.point.entry point.point.cut
abbrev paidFinal := (execution model domain original reference worker quote allocation rival point).final.point
abbrev completeControls (programme : Program model.source.code (horizon domain)) :=
  Prefix.Padding.controls original (clip (actualHorizon model point) programme)

def available (ordinal : Nat) :=
  if arrival (paidFinal model domain original reference worker quote allocation point rival) ≤ ordinal then
    finish model domain original reference worker receiver quote allocation announcements point rival send
  else none

def future (ordinal : Nat) : List (Prefix.Rule model.source.code) :=
  match available model domain original reference worker receiver quote allocation announcements point rival send ordinal with
  | some finished => match finished.choice with
    | some choice => (completeControls model domain original point choice.val.policy.protocol).drop allocation.length
    | none => []
  | none => []

theorem future_fits_the_original_remaining_window (ordinal : Nat) :
    (future model domain original reference worker receiver quote allocation announcements point rival send ordinal).length ≤ actualHorizon model point := by
  unfold future
  split
  · split
    · change (List.drop allocation.length (Prefix.Padding.controls original _)).length ≤ _
      rw [List.length_drop,Prefix.Padding.length]
      exact Nat.sub_le _ _
    · exact Nat.zero_le _
  · exact Nat.zero_le _

def cutPoint (ordinal count : Nat) : Cursor model.source.code :=
  Splice.install (paidFinal model domain original reference worker quote allocation point rival) rival
    ((future model domain original reference worker receiver quote allocation announcements point rival send ordinal).take count)
abbrev full (ordinal : Nat) := cutPoint model domain original reference worker receiver quote allocation announcements point rival send ordinal (actualHorizon model point)

variable (finished : Finished model domain original reference worker receiver quote allocation announcements point rival send)

include finished in
private theorem paid_prefix :
    paidFinal model domain original reference worker quote allocation point rival =
      Splice.install point.point rival (past model original worker quote (globalQuotas allocation)) ∧
    allocation.length ≤ horizon domain ∧ allocation.length ≤ actualHorizon model point ∧ 0 < allocation.length := by
  let scanned := execution model domain original reference worker quote allocation rival point
  obtain ⟨actual,rules,_⟩ := scanned.the_actual_source_contains_exactly_the_executed_fee_prefix
  have same : scanned.rules = past model original worker quote (globalQuotas allocation) := by
    have completed : scanned.remaining = [] := finished.executed
    change scanned.rules = List.replicate (globalQuotas allocation).length (Charge.feeRule quote model worker original)
    simpa only [completed,List.length_nil,Nat.sub_zero] using rules
  have budget := scan_budget model domain original reference worker quote allocation rival scanned
  obtain ⟨closing,present⟩ := Option.isSome_iff_exists.mp finished.closing
  have positive := closing_has_a_stage model domain original reference worker quote allocation rival scanned closing present
  rw [same] at budget positive
  have size : (past model original worker quote (globalQuotas allocation)).length = allocation.length := by
    simp only [past,Segmented.reserved,List.length_replicate,globalQuotas,List.length_map]
  rw [size] at budget positive
  exact ⟨by simpa only [same] using actual,by simpa only [size] using finished.room,budget,positive⟩

variable (choice : {choice : Choice model domain original reference worker quote (globalQuotas allocation) //
  eligible model domain original reference worker receiver quote (globalQuotas allocation) announcements point send choice.policy = true})

include finished in
private theorem controls_keep_the_actual_fee_prefix :
    (completeControls model domain original point choice.val.policy.protocol).take allocation.length =
      past model original worker quote (globalQuotas allocation) := by
  obtain ⟨_,space,within,_⟩ := paid_prefix model domain original reference worker receiver quote allocation announcements point rival send finished
  have size : (past model original worker quote (globalQuotas allocation)).length = allocation.length := by
    simp only [past,Segmented.reserved,List.length_replicate,globalQuotas,List.length_map]
  have retained := Prefix.the_selected_plan_really_preserves_the_committed_control_prefix
    model domain original (past model original worker quote (globalQuotas allocation)) reference choice.val (by simpa only [size] using space)
  have normalized : (clip (actualHorizon model point) choice.val.policy.protocol).controls.take
      (past model original worker quote (globalQuotas allocation)).length = past model original worker quote (globalQuotas allocation) := by
    change (choice.val.policy.protocol.controls.take (actualHorizon model point)).take _ = _
    rw [List.take_take,Nat.min_eq_left (by simpa only [size] using within)]
    exact retained
  simpa only [size] using Prefix.Padding.preserves_prefix original _ (past model original worker quote (globalQuotas allocation)) normalized

variable (ordinal : Nat)
  (released : available model domain original reference worker receiver quote allocation announcements point rival send ordinal = some finished)
  (selected : finished.choice = some choice)
include released selected in
theorem the_actual_deployment_is_the_entire_selected_window_without_repaying_its_prefix :
    full model domain original reference worker receiver quote allocation announcements point rival send ordinal =
      Splice.install point.point rival (completeControls model domain original point choice.val.policy.protocol) := by
  have actual := (paid_prefix model domain original reference worker receiver quote allocation announcements point rival send finished).1
  have retained := controls_keep_the_actual_fee_prefix model domain original reference worker receiver quote allocation announcements point rival send finished choice
  have whole := List.take_append_drop allocation.length (completeControls model domain original point choice.val.policy.protocol)
  rw [retained] at whole
  simp only [full,cutPoint]
  rw [List.take_of_length_le (future_fits_the_original_remaining_window model domain original reference worker receiver quote allocation announcements point rival send ordinal)]
  simp only [future,released,selected]
  rw [actual]
  change List.foldl _ (List.foldl _ point.point _) _ = _
  rw [←List.foldl_append,whole]
  rfl

include released selected in
theorem the_installed_input_is_the_complete_original_evaluated_input :
    (full model domain original reference worker receiver quote allocation announcements point rival send ordinal).source.input =
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.source point.point original (clip (actualHorizon model point) choice.val.policy.protocol) rival).input := by
  rw [the_actual_deployment_is_the_entire_selected_window_without_repaying_its_prefix model domain original reference worker receiver quote allocation announcements point rival send finished choice ordinal released selected]
  have paid := paid_prefix model domain original reference worker receiver quote allocation announcements point rival send finished
  have positive : 0 < actualHorizon model point := Nat.lt_of_lt_of_le paid.2.2.2 paid.2.2.1
  have nonempty : completeControls model domain original point choice.val.policy.protocol ≠ [] := by
    intro empty
    have size := Prefix.Padding.length original (clip (actualHorizon model point) choice.val.policy.protocol)
    change (completeControls model domain original point choice.val.policy.protocol).length = actualHorizon model point at size
    rw [empty] at size
    exact (Nat.ne_of_gt positive) size.symm
  rw [Splice.input_assembly _ _ original _ nonempty,Prefix.Padding.same_entire_source]

include released selected in
theorem the_actual_deployment_finishes_the_original_remaining_budget :
    (full model domain original reference worker receiver quote allocation announcements point rival send ordinal).cut = point.point.cut+actualHorizon model point ∧
    (Cut.seed (full model domain original reference worker receiver quote allocation announcements point rival send ordinal)).remaining = 0 := by
  rw [the_actual_deployment_is_the_entire_selected_window_without_repaying_its_prefix model domain original reference worker receiver quote allocation announcements point rival send finished choice ordinal released selected]
  constructor
  · exact (Installation.Chain.fold_cut (model := model) point.point rival _).trans
      (congrArg (point.point.cut+·) (Prefix.Padding.length original _))
  · have remaining := Installation.Chain.fold_remaining (model := model) point.point rival
      (completeControls model domain original point choice.val.policy.protocol)
    change _ = _ - (Prefix.Padding.controls original _).length at remaining
    rw [Prefix.Padding.length] at remaining
    exact remaining.trans (Nat.sub_self _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Deployment
