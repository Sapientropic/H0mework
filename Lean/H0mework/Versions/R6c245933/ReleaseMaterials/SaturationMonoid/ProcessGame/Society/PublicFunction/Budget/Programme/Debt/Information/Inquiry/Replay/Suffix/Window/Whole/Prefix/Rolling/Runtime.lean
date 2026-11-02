import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Review
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed.Transcript

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Runtime
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (views : List (View (code := model.source.code))) (original : Prefix.Rule model.source.code)

abbrev domain := views.map View.point
variable (reference : Program model.source.code (horizon (domain model views)))
  (work : Work model (domain model views) original reference) (n : Nat)
  (actual : View (code := model.source.code)) (rival : Opponent model.source.code)

abbrev execute := Splice.install actual.point rival (run work n).past
abbrev currentView := Window.Observed.Transcript.actualView (run work n).past actual rival
omit actual rival in
abbrev publicViews := Window.Observed.Transcript.publicViews (run work n).past views

theorem current_view_is_the_actual_installation :
    (currentView model views original reference work n actual rival).point = execute model views original reference work n actual rival := by
  unfold currentView Window.Observed.Transcript.actualView execute Splice.install
  generalize (run work n).past = stages
  induction stages generalizing actual with
  | nil => rfl
  | cons head tail ih => exact ih (Evidence.after actual head rival)

theorem current_public_knowledge_keeps_the_actual_source_and_original_debt
    (covered : Knowledge.Contains views actual) :
    Knowledge.Contains (publicViews model views original reference work n)
      (currentView model views original reference work n actual rival) :=
  Window.Observed.Transcript.every_actual_past_keeps_a_representative_in_the_same_public_domain
    (run work n).past views actual covered rival


theorem each_actual_update_executes_only_the_new_current_stage
    (inside : (run work n).past.length < horizon (domain model views)) :
    execute model views original reference work (n+1) actual rival =
      (execute model views original reference work n actual rival).after
        ((run work n).programme.at original (run work n).past.length) rival := by
  change Splice.install actual.point rival (advance (run work n)).past = _
  rw [advance_really_commits_only_the_current_stage _ inside]
  unfold Splice.install
  rw [List.foldl_append]
  rfl


theorem the_current_future_completion_protects_the_same_original_actual_reference
    (covered : Knowledge.Contains views actual) :
    Synthesis.accepts model.source.code (economicAxes actual.point.source actual.point.cut)
      (actualEvaluation model actual.point original (run work n).programme rival)
      (actualEvaluation model actual.point original reference rival) :=
  Observation.public_domain_acceptance_protects_every_covered_actual_source model actual.point original (run work n).programme rival
    (domain model views) (Knowledge.cursor_covered views actual covered) reference (run work n).accepted


theorem every_actual_cut_keeps_the_complete_original_financial_prefix
    (ordinal : Nat) (earlier : ordinal ≤ arrival actual.point) :
    Native.Coupling.Match model.source.code actual.point.source.input
      (execute model views original reference work n actual rival).source.input
      (Financial.accountAt actual.point.source.input ordinal)
      (Financial.accountAt (execute model views original reference work n actual rival).source.input ordinal) :=
  Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model) actual.point rival _ ordinal earlier

abbrev bound := Replanning.native model (execute model views original reference work n actual rival)
abbrev facade := Native.AuthorityRuntime.facade (bound model views original reference work n actual rival)
abbrev activated := Inquiry.Runtime.readState (bound model views original reference work n actual rival)
  (depth (execute model views original reference work n actual rival))


theorem every_actual_cut_consumes_global_review_completion_finance_knowledge_and_own_next
    (covered : Knowledge.Contains views actual) :
    let currentRoot := activated model views original reference work n actual rival
    verify model (domain model views) original [] reference (run work n).programme = true ∧
      verify model (domain model views) original (run work n).past reference (Review.tail (run work n)) = true ∧
      Synthesis.accepts model.source.code (economicAxes actual.point.source actual.point.cut)
        (actualEvaluation model actual.point original (run work n).programme rival)
        (actualEvaluation model actual.point original reference rival) ∧
      Knowledge.Contains (publicViews model views original reference work n)
        (currentView model views original reference work n actual rival) ∧
      (∀ ordinal ≤ arrival actual.point,Native.Coupling.Match model.source.code actual.point.source.input
        (execute model views original reference work n actual rival).source.input
        (Financial.accountAt actual.point.source.input ordinal)
        (Financial.accountAt (execute model views original reference work n actual rival).source.input ordinal)) ∧
      HEq ((facade model views original reference work n actual rival).readoutAt currentRoot .responsibilities)
        (currentRoot.tick.generated.projectionOutcome (.component ())) ∧
      HEq currentRoot.tick.generated.wholeLedgerWriteBack
        (currentRoot.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt currentRoot.current.visit.current) ∧
      currentRoot.tick.nextCurrent = (facade model views original reference work n actual rival).process.stateAt
        ((facade model views original reference work n actual rival).process.successor currentRoot.state) := by
  let currentRoot := activated model views original reference work n actual rival
  have rooted := (facade model views original reference work n actual rival).readoutAt_factorizes currentRoot .responsibilities
  exact ⟨Review.the_full_original_domain_independently_reviews_every_generated_plan _,
    Review.the_locked_past_and_all_finite_future_tails_are_independently_reviewed _,
    the_current_future_completion_protects_the_same_original_actual_reference model views original reference work n actual rival covered,
    current_public_knowledge_keeps_the_actual_source_and_original_debt model views original reference work n actual rival covered,
    every_actual_cut_keeps_the_complete_original_financial_prefix model views original reference work n actual rival,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Runtime
