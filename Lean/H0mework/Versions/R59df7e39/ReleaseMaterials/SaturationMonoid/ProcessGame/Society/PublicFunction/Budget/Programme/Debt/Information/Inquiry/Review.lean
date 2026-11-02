import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Domain

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Review

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (views : List (View (code := model.source.code)))
  (template : Template (code := model.source.code)) (selected : Activation template)
  (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)

def domain := views.map View.point

inductive Outcome where
  | unsupported (key : model.source.code.Key) (original : key ∈ model.source.code.keys)
      (outside : ¬ supported views template selected.site key)
  | accepted (rule : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
      (work : rule.work.val = policy views template selected.site)
      (events : rule.events = eventTable views template selected.site)
      (complete : Replanning.acceptable model (domain model views) reference rule)
  | rejected (rule : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
      (work : rule.work.val = policy views template selected.site)
      (events : rule.events = eventTable views template selected.site)
      (failure : Replanning.Rejection model (domain model views) reference rule)
  | actualRefused (rule : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
      (work : rule.work.val = policy views template selected.site)
      (events : rule.events = eventTable views template selected.site)
      (actual : View (code := model.source.code)) (generated : actual ∈ views)
      (rival : Opponent model.source.code) (axis : EconomicAxis model.source.code)
      (original : axis ∈ economicAxes actual.point.source actual.point.cut)
      (worse : ¬ (Replanning.actualEvaluation model actual.point rule rival).value axis ≤
        (Replanning.actualEvaluation model actual.point reference rival).value axis)

def generate : Outcome model views template selected reference :=
  match compile views template selected.site with
  | .unsupported key original outside => .unsupported key original outside
  | .ready rule work events =>
    match inspect (Replanning.holds model (domain model views) reference rule) (Replanning.rows model (domain model views)) with
    | .accepted all => .accepted rule work events all
    | .rejected row original broken => .rejected rule work events ⟨row,original,broken⟩

def probe (actual : View (code := model.source.code)) (generated : actual ∈ views)
    (rival : Opponent model.source.code) : Outcome model views template selected reference :=
  match compile views template selected.site with
  | .unsupported key original outside => .unsupported key original outside
  | .ready rule work events =>
    match inspect (fun axis => (Replanning.actualEvaluation model actual.point rule rival).value axis ≤
        (Replanning.actualEvaluation model actual.point reference rival).value axis)
        (economicAxes actual.point.source actual.point.cut) with
    | .rejected axis original worse => .actualRefused rule work events actual generated rival axis original worse
    | .accepted _ => generate model views template selected reference

theorem accepted_acquisition_protects_every_common_adaptive_opponent
    (rule : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (checked : Replanning.acceptable model (domain model views) reference rule)
    (view : View (code := model.source.code)) (original : view ∈ views) (rival : Opponent model.source.code) :
    Synthesis.accepts model.source.code (economicAxes view.point.source view.point.cut)
      (Replanning.actualEvaluation model view.point rule rival)
      (Replanning.actualEvaluation model view.point reference rival) :=
  (Replanning.acceptable_iff_every_common_external_opponent model (domain model views) reference rule).mp checked
    ⟨view.point,List.mem_map.mpr ⟨view,original,rfl⟩⟩ rival

theorem every_accepted_acquisition_enters_the_original_non_dominance_search
    (rule : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (checked : Replanning.acceptable model (domain model views) reference rule) :
    ∃ candidate ∈ Replanning.candidates model (domain model views) reference,candidate.protocol = rule :=
  Replanning.every_accepted_protocol_is_generated model (domain model views) reference rule checked

theorem an_actual_cost_refusal_excludes_full_responsibility_admission
    (rule : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (actual : View (code := model.source.code)) (generated : actual ∈ views)
    (rival : Opponent model.source.code) (axis : EconomicAxis model.source.code)
    (original : axis ∈ economicAxes actual.point.source actual.point.cut)
    (worse : ¬ (Replanning.actualEvaluation model actual.point rule rival).value axis ≤
      (Replanning.actualEvaluation model actual.point reference rival).value axis) :
    ¬ Replanning.acceptable model (domain model views) reference rule := by
  intro accepted
  exact worse ((accepted_acquisition_protects_every_common_adaptive_opponent model views reference
    rule accepted actual generated rival).2.2.2.2 axis original)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Review
