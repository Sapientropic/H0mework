import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Recursion

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Deployment

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
  (views : List (View (code := model.source.code)))
  (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) (fuel : Nat)

abbrev plan := Recursion.plan model views reference fuel

variable (actual : View (code := model.source.code)) (rival : Opponent model.source.code)

abbrev final := Recursion.finalView (plan model views reference fuel) actual rival
abbrev finalViews := Recursion.finalViews (plan model views reference fuel) views
abbrev bound := Replanning.native model (final model views reference fuel actual rival).point
abbrev facade := Native.AuthorityRuntime.facade (bound model views reference fuel actual rival)
abbrev activated (n : Nat) := Runtime.readState (bound model views reference fuel actual rival)
  (depth (final model views reference fuel actual rival).point+n)
abbrev native (n : Nat) := Runtime.read (bound model views reference fuel actual rival)
  (depth (final model views reference fuel actual rival).point+n)

variable (template : Template (code := model.source.code)) (selected : Activation template)

theorem actual_installation_preserves_every_paid_original_financial_prefix
    (ordinal : Nat) (earlier : ordinal ≤ arrival actual.point) :
    Native.Coupling.Match model.source.code actual.point.source.input
      (final model views reference fuel actual rival).point.source.input
      (Financial.accountAt actual.point.source.input ordinal)
      (Financial.accountAt (final model views reference fuel actual rival).point.source.input ordinal) := by
  rw [Recursion.final_view_is_the_original_actual_installation,
    Installation.Chain.realization_is_the_actual_installed_rule_fold]
  exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix
    (model := model) actual.point rival (plan model views reference fuel).rules ordinal earlier

theorem the_original_root_consumes_recursive_queries_selection_finance_and_own_next
    (member : actual ∈ views) (n : Nat) :
    let chain := plan model views reference fuel
    let current := activated model views reference fuel actual rival n
    Recursion.AllCuts template selected chain views actual rival ∧
      chain.review = true ∧ chain.replayActual actual.point rival = true ∧
      chain.InstalledPrefixes actual.point rival ∧
      Knowledge.Contains (finalViews model views reference fuel) (final model views reference fuel actual rival) ∧
      (native model views reference fuel actual rival n).joint.finance =
        Financial.accountAt (final model views reference fuel actual rival).point.source.input
          (arrival (final model views reference fuel actual rival).point+n+1) ∧
      HEq ((facade model views reference fuel actual rival).readoutAt current .responsibilities)
        (current.tick.generated.projectionOutcome (.component ())) ∧
      HEq current.tick.generated.wholeLedgerWriteBack
        (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
      current.tick.nextCurrent = (facade model views reference fuel actual rival).process.stateAt
        ((facade model views reference fuel actual rival).process.successor current.state) := by
  let chain := plan model views reference fuel
  let current := activated model views reference fuel actual rival n
  have known := Knowledge.member views actual member
  have rooted := (facade model views reference fuel actual rival).readoutAt_factorizes current .responsibilities
  refine ⟨Recursion.generated_queries_and_actual_selection_share_every_cut model template selected
      views reference fuel actual member rival,
    chain.every_compiled_step_is_independently_reviewable,
    chain.every_actual_selected_cut_is_independently_reviewable actual.point rival
      (Knowledge.cursor_covered views actual known),
    chain.every_installed_cut_is_retained_by_the_one_final_source actual.point rival,
    Recursion.the_final_domain_retains_the_actual_original_debt_origin chain views actual known rival,
    ?_,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
  rw [(native model views reference fuel actual rival n).joint_exact]
  have account := (Native.generate (final model views reference fuel actual rival).point.source
    (depth (final model views reference fuel actual rival).point+n)).finance_exact
  have index : depth (final model views reference fuel actual rival).point+n+2 =
      arrival (final model views reference fuel actual rival).point+n+1 := by
    dsimp only [depth,arrival];omega
  rw [index] at account
  exact account

abbrev forWorld (budget : Nat) (world : Distributed.Recall.Information.World model budget) :=
  facade model (completeViews model budget) reference fuel (ofWorld model budget world) rival

theorem every_generated_world_installs_its_own_recursive_full_responsibility_plan
    (budget : Nat) (world : Distributed.Recall.Information.World model budget) :
    Recursion.AllCuts template selected
      (plan model (completeViews model budget) reference fuel) (completeViews model budget)
      (ofWorld model budget world) rival :=
  Recursion.generated_queries_and_actual_selection_share_every_cut model template selected
    (completeViews model budget) reference fuel (ofWorld model budget world)
    (every_source_generated_world_is_in_the_information_domain model budget world) rival

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Deployment
