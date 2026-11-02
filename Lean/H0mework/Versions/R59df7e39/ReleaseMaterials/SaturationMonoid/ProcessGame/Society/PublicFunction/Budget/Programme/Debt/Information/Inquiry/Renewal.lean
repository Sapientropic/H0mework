import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Evidence
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Approval
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Acceptance

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Renewal

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
  (template : Template (code := model.source.code)) (selected : Activation template)
  (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (view : View (code := model.source.code)) (member : view ∈ views) (rival : Opponent model.source.code)

abbrev basis := successors reference views
abbrev actual := Evidence.after view reference rival
abbrev decision := Review.generate model (basis model views reference) template selected reference

def cursorAt (n : Nat) : Cursor model.source.code :=
  match decision model views template selected reference with
  | .accepted protocol _ _ _ => {(actual model reference view rival).point.after protocol rival with
      cut := (actual model reference view rival).point.cut+n}
  | .unsupported _ _ _ | .rejected _ _ _ _ | .actualRefused _ _ _ _ _ _ _ _ _ =>
      {(actual model reference view rival).point with cut := (actual model reference view rival).point.cut+n}

abbrev target := (cursorAt model views template selected reference view rival 0).source

include member in
theorem accepted_successor_query_protects_the_actual_source_against_every_common_opponent
    (protocol : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (accepted : Replanning.acceptable model (Review.domain model (basis model views reference)) reference protocol)
    (opponent : Opponent model.source.code) :
    Synthesis.accepts model.source.code
      (economicAxes (actual model reference view rival).point.source (actual model reference view rival).point.cut)
      (Replanning.actualEvaluation model (actual model reference view rival).point protocol opponent)
      (Replanning.actualEvaluation model (actual model reference view rival).point reference opponent) := by
  have covered := every_actual_installation_stays_in_its_own_public_information_domain
    (views.map View.point) view.point
    ⟨view.point,List.mem_map.mpr ⟨view,member,rfl⟩,Aligned.refl _⟩ reference rival
  rw [← Evidence.projected_successors_are_the_original_recursive_domain reference views] at covered
  obtain ⟨representative,original,matched⟩ := covered
  have checkedActual := (Replanning.acceptable_iff_every_common_external_opponent model
    (Review.domain model (basis model views reference)) reference protocol).mp accepted
      ⟨representative,original⟩ opponent
  exact (Acceptance.aligned_acceptance model representative (actual model reference view rival).point
    matched opponent protocol reference).mp checkedActual

def Protected : Prop := match decision model views template selected reference with
  | .accepted protocol _ _ _ => ∀ opponent : Opponent model.source.code,
      Synthesis.accepts model.source.code
        (economicAxes (actual model reference view rival).point.source (actual model reference view rival).point.cut)
        (Replanning.actualEvaluation model (actual model reference view rival).point protocol opponent)
        (Replanning.actualEvaluation model (actual model reference view rival).point reference opponent)
  | .unsupported _ _ _ | .rejected _ _ _ _ | .actualRefused _ _ _ _ _ _ _ _ _ =>
      target model views template selected reference view rival = (actual model reference view rival).point.source

include member in
theorem generated_successor_admission_is_actual_or_preserves_its_original_source :
    Protected model views template selected reference view rival := by
  cases result : decision model views template selected reference with
  | accepted protocol work events checked =>
    simpa only [Protected,result] using
      (accepted_successor_query_protects_the_actual_source_against_every_common_opponent
        model views reference view member rival protocol checked)
  | unsupported key original outside => simp only [Protected,target,cursorAt,decision,result]
  | rejected protocol work events failure => simp only [Protected,target,cursorAt,decision,result]
  | actualRefused protocol work events current original opponent axis admitted worse =>
      simp only [Protected,target,cursorAt,decision,result]

abbrev bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  ⟨model.base,model.scope,target model views template selected reference view rival,model.law_exact,model.task_exact⟩
abbrev facade := Native.AuthorityRuntime.facade (bound model views template selected reference view rival)
abbrev activated (n : Nat) := Runtime.readState (bound model views template selected reference view rival)
  (depth (actual model reference view rival).point+n)
abbrev native (n : Nat) := Runtime.read (bound model views template selected reference view rival)
  (depth (actual model reference view rival).point+n)

include member in
theorem the_original_root_consumes_the_regenerated_successor_query_and_next (n : Nat) :
    let current := activated model views template selected reference view rival n
    Protected model views template selected reference view rival ∧
      (native model views template selected reference view rival n).joint.finance =
        Financial.accountAt (target model views template selected reference view rival).input
          (arrival (actual model reference view rival).point+n+1) ∧
      HEq ((facade model views template selected reference view rival).readoutAt current .responsibilities)
        (current.tick.generated.projectionOutcome (.component ())) ∧
      HEq current.tick.generated.wholeLedgerWriteBack
        (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
      current.tick.nextCurrent = (facade model views template selected reference view rival).process.stateAt
        ((facade model views template selected reference view rival).process.successor current.state) := by
  let current := activated model views template selected reference view rival n
  have rooted := (facade model views template selected reference view rival).readoutAt_factorizes current .responsibilities
  refine ⟨generated_successor_admission_is_actual_or_preserves_its_original_source model views template selected reference view member rival,
    ?_,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
  rw [(native model views template selected reference view rival n).joint_exact]
  have exactAccount := (Native.generate (target model views template selected reference view rival)
    (depth (actual model reference view rival).point+n)).finance_exact
  have address : depth (actual model reference view rival).point+n+2 = arrival (actual model reference view rival).point+n+1 := by
    dsimp only [depth,arrival];omega
  rw [address] at exactAccount
  exact exactAccount

abbrev forWorld (budget : Nat) (world : Distributed.Recall.Information.World model budget) :=
  facade model (completeViews model budget) template selected reference (ofWorld model budget world) rival

theorem every_source_generated_world_has_actual_successor_admission_without_a_coverage_premise
    (budget : Nat) (world : Distributed.Recall.Information.World model budget) :
    Protected model (completeViews model budget) template selected reference (ofWorld model budget world) rival :=
  generated_successor_admission_is_actual_or_preserves_its_original_source model (completeViews model budget)
    template selected reference (ofWorld model budget world)
    (every_source_generated_world_is_in_the_information_domain model budget world) rival

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Renewal
