import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Chosen
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Publication
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed.Grant

set_option autoImplicit false

open private firstGrant grant_at creates_grant from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed.Grant
open private earlier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Plan

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Consumers

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt inventory)
open ExposureGuard.Consumers.Installed

noncomputable section

private abbrev exitPrior := paidView opened

theorem installedExitApproval : Certified exitPrior yes chosen.word :=
  ⟨of_chosen chosen, chosen.checked.2, chosen.checked.1.1.standing⟩

theorem every_rival_scheduler_writes_the_installed_exit_at_tick_one
    (rival : Scheduler Bool Bool Port Tech Unit) (person : Bool) :
    let reached := visitAt exitPrior yes chosen.word rival person installedExitApproval 1
    reached.history = chosen.word ∧
    HEq reached.state (MandateExit.exercise opened chosen) ∧
    Quantities.Recorded cut reached.history ∧
    cut.raw.clock + 1 = (endAt cut reached.history).raw.clock := by
  let reached := visitAt exitPrior yes chosen.word rival person installedExitApproval 1
  have endpoint : reached = advancePaid exitPrior yes chosen.word installedExitApproval.due :=
    the_priority_endpoint_is_the_same_original_write exitPrior yes chosen.word rival person installedExitApproval
  have original : reached.history = chosen.word :=
    (congrArg (fun visit : PaidVisit cut (id : Bool → Bool) [] => visit.history) endpoint).trans rfl
  refine ⟨original, ?_, Quantities.record _ _, ?_⟩
  · change HEq reached.state (MandateExit.exercise opened chosen)
    rw [endpoint]
    rfl
  · change cut.raw.clock + 1 = (endAt cut reached.history).raw.clock
    rw [original]
    exact the_installed_root_pays_both_original_exits_on_its_actual_clock.2.1

def stopReviewForever : Scheduler Bool Bool Port Tech Unit :=
  ⟨fun _ _ => .rival, fun _ _ => stop, fun _ _ => stop, fun _ _ _ => []⟩

theorem constant_stop_review_still_writes_the_exit_at_tick_one (person : Bool) :
    let reached := visitAt exitPrior yes chosen.word stopReviewForever person installedExitApproval 1
    reached.history = chosen.word ∧
    cut.raw.clock + 1 = (endAt cut reached.history).raw.clock := by
  have written := every_rival_scheduler_writes_the_installed_exit_at_tick_one stopReviewForever person
  exact ⟨written.1, written.2.2.2⟩

private theorem the_original_grant_is_not_a_checked_commitment :
    ¬ Checked cut id [] yes exitPrior.history [proposal] := by
  intro checked
  let item := (originalItems (seed := cut) opened.history proposal)[firstGrant]
  have original : item ∈ inventory (endAt cut exitPrior.history) [proposal] :=
    List.getElem_mem firstGrant.isLt
  have grant : Grants item.request := by
    change Grants (originalItems (seed := cut) opened.history proposal)[firstGrant].request
    rw [grant_at]
    exact creates_grant
  exact checked.no_grants item original grant

private theorem earlier_has_zero_ordinal (left right : PlanFailure exitPrior yes [proposal])
    (zero : left.ordinal exitPrior yes [proposal] = 0 ∨ right.ordinal exitPrior yes [proposal] = 0) :
    (earlier exitPrior yes [proposal] left right).ordinal exitPrior yes [proposal] = 0 := by
  unfold earlier
  split
  · rename_i ordered
    rcases zero with first | second
    · exact first
    · omega
  · rename_i unordered
    rcases zero with first | second
    · omega
    · exact second

/-- The old paid nomination is a real grant. Even the agreeing source
answers cannot put it into the reserved civilian programme. -/
theorem the_honest_original_grant_has_a_typed_refusal_at_ordinal_zero :
    ∃ failed : PlanFailure exitPrior yes [proposal],
      inspectPlan exitPrior yes [proposal] = .inl failed ∧ failed.ordinal exitPrior yes [proposal] = 0 := by
  have denied : ∃ failed : Failure cut id [] yes exitPrior.history [proposal],
      inspect cut id [] yes exitPrior.history [proposal] = .inl failed ∧
        failed.front.length = 0 := by
    cases inspected : inspect cut id [] yes exitPrior.history [proposal] with
    | inr checked => exact (the_original_grant_is_not_a_checked_commitment checked.down).elim
    | inl failed =>
      refine ⟨failed, rfl, ?_⟩
      have length : ([proposal] : Word).length = (failed.front ++ failed.input :: failed.tail).length :=
        congrArg List.length failed.split
      simp only [List.length_append, List.length_cons, List.length_nil] at length
      omega
  obtain ⟨failed, located, zero⟩ := denied
  let grant : PlanFailure exitPrior yes [proposal] := .inl failed
  have grantZero : grant.ordinal exitPrior yes [proposal] = 0 := zero
  unfold inspectPlan
  dsimp only
  rw [located]
  generalize Exit.inspectStanding (Exit.roster cut id [] exitPrior.history)
    (endAt cut exitPrior.history) [proposal] = standing
  generalize Due.inspect (endAt cut []) ((Civil.Persistence.Window.at cut).run [])
    ((exitPrior.history ++ [proposal]).drop ([] : Word).length) = due
  cases standing with
  | inl lost =>
    cases due with
    | inl late => exact ⟨_, rfl, earlier_has_zero_ordinal _ _
        (Or.inr (earlier_has_zero_ordinal _ _ (Or.inl grantZero)))⟩
    | inr kept => exact ⟨_, rfl, earlier_has_zero_ordinal _ _ (Or.inr grantZero)⟩
  | inr kept =>
    cases due with
    | inl late => exact ⟨_, rfl, earlier_has_zero_ordinal _ _ (Or.inl grantZero)⟩
    | inr paid => exact ⟨grant, rfl, grantZero⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Consumers
