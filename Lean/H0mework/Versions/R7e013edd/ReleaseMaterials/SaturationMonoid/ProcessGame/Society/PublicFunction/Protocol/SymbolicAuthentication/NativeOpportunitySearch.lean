import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointOpportunityPrefix

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeOpportunitySearch
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : NativeReviewRun.Stages model)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev prefixAt (offset : Nat) := JointOpportunityPrefix.atCut model start vocabulary encoding law past offset

structure Ready where
  private mk ::
  offset : Nat
  bounded : offset < JointResponse.fuel model start past
  prior : JointResponse.Stages model
  prior_exact : prior = JointOpportunityPrefix.atCut model start vocabulary encoding law past offset
  answer : JointOpportunityGate.Attempt model start vocabulary encoding law prior

-- Carry the already generated prefix; do not replay it separately for each candidate offset.
private def scan : (remaining offset : Nat) → (prior : JointResponse.Stages model) →
    (prior = JointOpportunityPrefix.atCut model start vocabulary encoding law past offset) →
    (offset + remaining ≤ JointResponse.fuel model start past) → Option (Ready model start past vocabulary encoding law)
  | 0, _, _, _, _ => none
  | remaining + 1, offset, prior, actual, room =>
    match JointOpportunityGate.probe model start vocabulary encoding law prior with
    | some answer => some ⟨offset, by omega, prior, actual, answer⟩
    | none => scan remaining (offset + 1) (JointOpportunityPrefix.nextStages model start vocabulary encoding law prior)
        (by rw [JointOpportunityPrefix.the_next_actual_prefix_is_the_same_original_step, ← actual]) (by omega)

def produce : Option (Ready model start past vocabulary encoding law) :=
  scan model start past vocabulary encoding law (JointResponse.fuel model start past) 0 past
    (JointOpportunityPrefix.zero_has_the_original_stages model start vocabulary encoding law past).symm (by omega)

abbrev full (answer : Ready model start past vocabulary encoding law) :=
  JointOpportunityGate.full model start vocabulary encoding law answer.prior answer.answer

private theorem scan_is_empty_exactly_when_the_original_interval_has_no_opportunity
    (remaining offset : Nat) (prior : JointResponse.Stages model)
    (actual : prior = JointOpportunityPrefix.atCut model start vocabulary encoding law past offset)
    (room : offset + remaining ≤ JointResponse.fuel model start past) :
    scan model start past vocabulary encoding law remaining offset prior actual room = none ↔
      ∀ cut, offset ≤ cut → cut < offset + remaining →
        JointOpportunityGate.probe model start vocabulary encoding law (prefixAt model start past vocabulary encoding law cut) = none := by
  induction remaining generalizing offset prior with
  | zero =>
    simp only [scan, true_iff]
    intro cut lower upper
    omega
  | succ remaining ih =>
    cases observed : JointOpportunityGate.probe model start vocabulary encoding law prior with
    | some answer =>
      simp only [scan, observed, Option.some_ne_none, false_iff]
      intro absent
      have impossible := absent offset (Nat.le_refl _) (by omega)
      change JointOpportunityGate.probe model start vocabulary encoding law
        (JointOpportunityPrefix.atCut model start vocabulary encoding law past offset) = none at impossible
      rw [← actual, observed] at impossible
      cases impossible
    | none =>
      simp only [scan, observed]
      rw [ih]
      constructor
      · intro tail cut lower upper
        by_cases same : cut = offset
        · subst cut
          change JointOpportunityGate.probe model start vocabulary encoding law
            (JointOpportunityPrefix.atCut model start vocabulary encoding law past offset) = none
          rw [← actual]
          exact observed
        · exact tail cut (by omega) (by omega)
      · intro whole cut lower upper
        exact whole cut (by omega) (by omega)

theorem no_generated_opportunity_is_exactly_failure_at_every_actual_source_cut :
    produce model start past vocabulary encoding law = none ↔ ∀ offset < JointResponse.fuel model start past,
      JointOpportunityGate.probe model start vocabulary encoding law (prefixAt model start past vocabulary encoding law offset) = none := by
  have checked := scan_is_empty_exactly_when_the_original_interval_has_no_opportunity model start past vocabulary encoding law
    (JointResponse.fuel model start past) 0 past
    (JointOpportunityPrefix.zero_has_the_original_stages model start vocabulary encoding law past).symm (by omega)
  simpa only [produce, Nat.zero_add, Nat.zero_le, true_implies] using checked

theorem every_ready_opportunity_is_the_next_actual_original_run_prefix
    (answer : Ready model start past vocabulary encoding law) :
    full model start past vocabulary encoding law answer =
      prefixAt model start past vocabulary encoding law (answer.offset + 1) := by
  have next := JointOpportunityPrefix.the_next_actual_prefix_is_the_same_original_step model start vocabulary encoding law answer.offset past
  rw [← answer.prior_exact, JointOpportunityPrefix.nextStages, answer.answer.selected] at next
  exact answer.answer.actual.trans next.symm

theorem every_ready_opportunity_retains_the_original_history
    (answer : Ready model start past vocabulary encoding law) :
    past <+: full model start past vocabulary encoding law answer := by
  rw [every_ready_opportunity_is_the_next_actual_original_run_prefix]
  exact JointResponseRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law _ past

theorem every_ready_opportunity_is_a_prefix_of_the_original_source_budget_run
    (answer : Ready model start past vocabulary encoding law) :
    full model start past vocabulary encoding law answer <+:
      (JointResponseRun.produce model start vocabulary encoding law past).stages := by
  have bound := answer.bounded
  have composed := JointOpportunityPrefix.actual_run_prefixes_compose model start vocabulary encoding law
    (answer.offset + 1) (JointResponse.fuel model start past - (answer.offset + 1)) past
  have total : answer.offset + 1 + (JointResponse.fuel model start past - (answer.offset + 1)) = JointResponse.fuel model start past := by omega
  have same : full model start past vocabulary encoding law answer =
      JointOpportunityPrefix.atCut model start vocabulary encoding law past (answer.offset + 1) :=
    every_ready_opportunity_is_the_next_actual_original_run_prefix model start past vocabulary encoding law answer
  rw [total, ← same] at composed
  rw [show (JointResponseRun.produce model start vocabulary encoding law past).stages =
    JointOpportunityPrefix.atCut model start vocabulary encoding law past (JointResponse.fuel model start past) from rfl, composed]
  exact JointResponseRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law _ _

theorem a_generated_opportunity_closes_its_source_selected_original
    (answer : Ready model start past vocabulary encoding law) :
    NativeOpportunity.beforePending model start answer.prior answer.answer.native.ready answer.answer.native.original = true ∧
    (NativeReviewHistory.history model start answer.prior answer.answer.native.ready
      (OriginQueue.environment start) answer.answer.native.original).isPending _ _ = false := by
  have actual := NativeOpportunity.every_selected_opportunity_closes_a_real_previously_pending_original model start answer.prior answer.answer.native
  exact ⟨actual.2.1, actual.2.2.1⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeOpportunitySearch
