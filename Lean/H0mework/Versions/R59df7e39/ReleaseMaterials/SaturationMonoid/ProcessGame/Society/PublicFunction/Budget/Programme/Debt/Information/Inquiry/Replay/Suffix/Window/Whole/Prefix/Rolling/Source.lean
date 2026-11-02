import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Endpoint

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Source
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
  (budget : Nat) (published : List (Prefix.Rule model.source.code)) (original : Prefix.Rule model.source.code)

abbrev views := Window.Observed.Transcript.views model budget published
abbrev domain := Runtime.domain model (views model budget published)
variable (reference : Program model.source.code (horizon (domain model budget published)))
abbrev prepared := start model (domain model budget published) original reference

variable (world : Distributed.Recall.Information.World model budget)
  (pastOpponent rival : Opponent model.source.code) (n : Nat)
abbrev actual := Window.Observed.Transcript.actual model budget published world pastOpponent

def deployment : Cursor model.source.code :=
  match prepared model budget published original reference with
  | .ready work => Runtime.execute model (views model budget published) original reference work n
      (actual model budget published world pastOpponent) rival
  | .blocked _ => (actual model budget published world pastOpponent).point

def finalView : View (code := model.source.code) :=
  match prepared model budget published original reference with
  | .ready work => Runtime.currentView model (views model budget published) original reference work n
      (actual model budget published world pastOpponent) rival
  | .blocked _ => actual model budget published world pastOpponent

omit world pastOpponent rival in
def finalViews : List (View (code := model.source.code)) :=
  match prepared model budget published original reference with
  | .ready work => Runtime.publicViews model (views model budget published) original reference work n
  | .blocked _ => views model budget published

private theorem generated_seed_is_unspent (work : Work model (domain model budget published) original reference)
    (generated : prepared model budget published original reference = .ready work) : work.past = [] := by
  unfold prepared start at generated
  split at generated
  · have same := Start.ready.inj generated
    exact (congrArg Work.past same).symm
  · cases generated

omit n in
def Protection : Start model (domain model budget published) original reference → Prop
  | .blocked rejected => ∀ tail : Complete.FiniteProgram model.source.code,
      ¬ Selection.holds model (domain model budget published) original reference
        (extension (horizon (domain model budget published)) [] tail.2) (rejected tail).row
  | .ready work => ∀ cut : Nat,
      verify model (domain model budget published) original [] reference (run work cut).programme = true ∧
      verify model (domain model budget published) original (run work cut).past reference (Review.tail (run work cut)) = true ∧
      Nondominated model (domain model budget published) original reference (run work cut).programme ∧
      Synthesis.accepts model.source.code
        (economicAxes (actual model budget published world pastOpponent).point.source (actual model budget published world pastOpponent).point.cut)
        (actualEvaluation model (actual model budget published world pastOpponent).point original (run work cut).programme rival)
        (actualEvaluation model (actual model budget published world pastOpponent).point original reference rival) ∧
      (cut = Endpoint.count (actual model budget published world pastOpponent) →
        Synthesis.accepts model.source.code
          (economicAxes (actual model budget published world pastOpponent).point.source (actual model budget published world pastOpponent).point.cut)
          (actualEvaluation model (actual model budget published world pastOpponent).point original (Splice.word (run work cut).past) rival)
          (actualEvaluation model (actual model budget published world pastOpponent).point original reference rival) ∧
        (seed (Runtime.execute model (views model budget published) original reference work cut
          (actual model budget published world pastOpponent) rival)).remaining = 0)

abbrev bound := Replanning.native model (deployment model budget published original reference world pastOpponent rival n)
abbrev facade := Native.AuthorityRuntime.facade (bound model budget published original reference world pastOpponent rival n)
abbrev activated := Inquiry.Runtime.readState (bound model budget published original reference world pastOpponent rival n)
  (depth (deployment model budget published original reference world pastOpponent rival n))

theorem every_original_source_cut_generates_its_global_comparison_paid_chain_knowledge_and_own_next :
    let currentRoot := activated model budget published original reference world pastOpponent rival n
    Protection model budget published original reference world pastOpponent rival (prepared model budget published original reference) ∧
      (finalView model budget published original reference world pastOpponent rival n).point =
        deployment model budget published original reference world pastOpponent rival n ∧
      Knowledge.Contains (finalViews model budget published original reference n)
        (finalView model budget published original reference world pastOpponent rival n) ∧
      (∀ ordinal ≤ arrival (actual model budget published world pastOpponent).point,
        Native.Coupling.Match model.source.code (actual model budget published world pastOpponent).point.source.input
          (deployment model budget published original reference world pastOpponent rival n).source.input
          (Financial.accountAt (actual model budget published world pastOpponent).point.source.input ordinal)
          (Financial.accountAt (deployment model budget published original reference world pastOpponent rival n).source.input ordinal)) ∧
      HEq ((facade model budget published original reference world pastOpponent rival n).readoutAt currentRoot .responsibilities)
        (currentRoot.tick.generated.projectionOutcome (.component ())) ∧
      HEq currentRoot.tick.generated.wholeLedgerWriteBack
        (currentRoot.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt currentRoot.current.visit.current) ∧
      currentRoot.tick.nextCurrent = (facade model budget published original reference world pastOpponent rival n).process.stateAt
        ((facade model budget published original reference world pastOpponent rival n).process.successor currentRoot.state) := by
  let currentRoot := activated model budget published original reference world pastOpponent rival n
  have rooted := (facade model budget published original reference world pastOpponent rival n).readoutAt_factorizes currentRoot .responsibilities
  have covered := Window.Observed.Transcript.actual_coverage_is_generated_without_a_caller_witness model budget published world pastOpponent
  refine ⟨?_,?_,?_,?_,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
  · cases generated : prepared model budget published original reference with
    | blocked rejected => exact fun tail => (rejected tail).broken
    | ready work =>
        intro cut
        refine ⟨Review.the_full_original_domain_independently_reviews_every_generated_plan _,
          Review.the_locked_past_and_all_finite_future_tails_are_independently_reviewed _,(run work cut).maximal,
          Runtime.the_current_future_completion_protects_the_same_original_actual_reference _ _ _ _ _ _ _ _ covered,?_⟩
        intro completed
        subst cut
        have empty := generated_seed_is_unspent model budget published original reference work generated
        exact ⟨Endpoint.the_entire_actual_chain_keeps_the_original_full_responsibility_comparison work empty _ covered rival,
          Endpoint.the_actual_chain_consumes_exactly_its_original_unspent_budget work empty _ covered rival⟩
  · unfold finalView deployment
    cases prepared model budget published original reference with
    | blocked => rfl
    | ready work => exact Runtime.current_view_is_the_actual_installation _ _ _ _ _ _ _ _
  · unfold finalViews finalView
    cases prepared model budget published original reference with
    | blocked => exact covered
    | ready work => exact Runtime.current_public_knowledge_keeps_the_actual_source_and_original_debt _ _ _ _ _ _ _ _ covered
  · intro ordinal earlier
    unfold deployment
    cases prepared model budget published original reference with
    | ready work => exact Runtime.every_actual_cut_keeps_the_complete_original_financial_prefix _ _ _ _ _ _ _ _ ordinal earlier
    | blocked =>
        exact Native.Coupling.History.complete_accounts model.source.code _ _ rfl rfl ordinal
          (fun _ _ => rfl) _ _ rfl rfl ordinal (Nat.le_refl _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Source
