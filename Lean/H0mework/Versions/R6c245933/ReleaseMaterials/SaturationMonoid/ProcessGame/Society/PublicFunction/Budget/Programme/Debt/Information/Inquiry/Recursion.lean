import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Knowledge
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Renewal
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Installation

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Recursion

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (template : Template (code := model.source.code)) (selected : Activation template)

structure Query where
  views : List (View (code := model.source.code))
  reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code
  outcome : Review.Outcome model views template selected reference

def queries : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code} →
    Installation.Chain model fuel domain reference → List (View (code := model.source.code)) →
      List (Query model template selected)
  | _,_,_,.exhausted,_ => []
  | _,_,reference,.blocked _ _,views => [⟨views,reference,Review.generate model views template selected reference⟩]
  | _,_,reference,.selected choice _ tail,views =>
      ⟨views,reference,Review.generate model views template selected reference⟩ ::
        queries tail (successors choice.policy.protocol views)

variable {model} {fuel : Nat} {domain : List (Cursor model.source.code)}
  {reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code}

def QueryIncluded (views : List (View (code := model.source.code)))
    (choice : Replanning.Choice model domain reference) : Prop :=
  match Review.generate model views template selected reference with
  | .accepted query _ _ _ =>
      (∃ candidate ∈ Replanning.candidates model domain reference,candidate.protocol = query) ∧
        ¬ Distributed.Improves (Replanning.axes model domain) (Replanning.benefit model domain)
          choice.policy.protocol query
  | .unsupported _ _ _ | .rejected _ _ _ _ | .actualRefused _ _ _ _ _ _ _ _ _ => True

theorem every_admitted_query_competes_in_the_unchanged_full_search
    (views : List (View (code := model.source.code)))
    (projection : views.map View.point = domain) (choice : Replanning.Choice model domain reference) :
    QueryIncluded template selected views choice := by
  unfold QueryIncluded
  cases result : Review.generate model views template selected reference with
  | accepted query work events accepted =>
    have complete : Replanning.acceptable model domain reference query := by
      simpa only [Review.domain,projection] using accepted
    obtain ⟨candidate,inside,same⟩ := Replanning.every_accepted_protocol_is_generated model domain reference query complete
    have maximal := choice.maximal candidate inside
    change ¬ Distributed.Improves (Replanning.axes model domain) (Replanning.benefit model domain)
      choice.policy.protocol candidate.protocol at maximal
    rw [same] at maximal
    exact ⟨⟨candidate,inside,same⟩,maximal⟩
  | unsupported => trivial
  | rejected => trivial
  | actualRefused => trivial

def Step (views : List (View (code := model.source.code)))
    (actual : View (code := model.source.code)) (choice : Replanning.Choice model domain reference) : Prop :=
  Knowledge.CorrectOrConflict views actual ∧ QueryIncluded template selected views choice ∧
    Replanning.verify model domain reference choice.policy.protocol = true ∧
    (∀ rival : Opponent model.source.code,
      Synthesis.accepts model.source.code (economicAxes actual.point.source actual.point.cut)
        (Replanning.actualEvaluation model actual.point choice.policy.protocol rival)
        (Replanning.actualEvaluation model actual.point reference rival)) ∧
    ((∃ other : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code,
        Replanning.acceptable model domain reference other ∧
          Distributed.Improves (Replanning.axes model domain) (Replanning.benefit model domain) reference other) →
      Distributed.Improves (Replanning.axes model domain) (Replanning.benefit model domain)
        reference choice.policy.protocol)

def AllCuts : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code} →
    Installation.Chain model fuel domain reference → List (View (code := model.source.code)) →
      View (code := model.source.code) → Opponent model.source.code → Prop
  | _,_,_,.exhausted,views,actual,_ => Knowledge.Contains views actual
  | _,_,_,.blocked _ _,views,actual,_ => Knowledge.Contains views actual
  | _,_,_,.selected choice _ tail,views,actual,rival =>
      Step template selected views actual choice ∧
        AllCuts tail (successors choice.policy.protocol views) (Evidence.after actual choice.policy.protocol rival) rival

theorem every_actual_cut_regenerates_knowledge_and_full_responsibility_selection
    (chain : Installation.Chain model fuel domain reference)
    (views : List (View (code := model.source.code))) (projection : views.map View.point = domain)
    (actual : View (code := model.source.code)) (covered : Knowledge.Contains views actual)
    (rival : Opponent model.source.code) : AllCuts template selected chain views actual rival := by
  induction chain generalizing views actual with
  | exhausted => exact covered
  | blocked => exact covered
  | @selected fuel domain reference choice exact tail ih =>
    refine ⟨⟨Knowledge.actual_work_is_correct_or_retains_a_real_conflict views actual covered,
      every_admitted_query_competes_in_the_unchanged_full_search template selected views projection choice,
      Replanning.independently_replayed_choice_is_accepted model domain reference choice,?_,
      Replanning.every_full_responsibility_improvement_is_realized model domain reference choice⟩,
      ih (successors choice.policy.protocol views) ?_ (Evidence.after actual choice.policy.protocol rival)
        (Knowledge.after views actual covered choice.policy.protocol rival)⟩
    · intro opponent
      obtain ⟨representative,inside,matched⟩ := Knowledge.cursor_covered views actual covered
      exact (Acceptance.aligned_acceptance model representative actual.point matched opponent choice.policy.protocol reference).mp
        ((Replanning.acceptable_iff_every_common_external_opponent model domain reference choice.policy.protocol).mp
          choice.policy.accepted ⟨representative,by rw [←projection];exact inside⟩ opponent)
    · rw [Evidence.projected_successors_are_the_original_recursive_domain,projection]

def finalView (chain : Installation.Chain model fuel domain reference)
    (actual : View (code := model.source.code)) (rival : Opponent model.source.code) :=
  chain.rules.foldl (fun current rule => Evidence.after current rule rival) actual

def finalViews (chain : Installation.Chain model fuel domain reference)
    (views : List (View (code := model.source.code))) :=
  chain.rules.foldl (fun current rule => successors rule current) views

theorem final_view_is_the_original_actual_installation
    (chain : Installation.Chain model fuel domain reference)
    (actual : View (code := model.source.code)) (rival : Opponent model.source.code) :
    (finalView chain actual rival).point = chain.realize actual.point rival := by
  rw [Installation.Chain.realization_is_the_actual_installed_rule_fold]
  unfold finalView
  generalize chain.rules = rules
  induction rules generalizing actual with
  | nil => rfl
  | cons rule rest ih => exact ih (Evidence.after actual rule rival)

theorem the_final_domain_retains_the_actual_original_debt_origin
    (chain : Installation.Chain model fuel domain reference)
    (views : List (View (code := model.source.code))) (actual : View (code := model.source.code))
    (covered : Knowledge.Contains views actual) (rival : Opponent model.source.code) :
    Knowledge.Contains (finalViews chain views) (finalView chain actual rival) := by
  unfold finalViews finalView
  generalize chain.rules = rules
  induction rules generalizing views actual with
  | nil => exact covered
  | cons rule rest ih =>
    exact ih (successors rule views) (Evidence.after actual rule rival) (Knowledge.after views actual covered rule rival)

variable (model)
  (views : List (View (code := model.source.code)))
  (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (fuel : Nat)

def plan := Installation.generate model fuel (views.map View.point) reference
abbrev publicQueries := queries model template selected (plan model views reference fuel) views

theorem generated_queries_and_actual_selection_share_every_cut
    (actual : View (code := model.source.code)) (member : actual ∈ views) (rival : Opponent model.source.code) :
    AllCuts template selected (plan model views reference fuel) views actual rival :=
  every_actual_cut_regenerates_knowledge_and_full_responsibility_selection template selected
    (plan model views reference fuel) views rfl actual (Knowledge.member views actual member) rival

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Recursion
