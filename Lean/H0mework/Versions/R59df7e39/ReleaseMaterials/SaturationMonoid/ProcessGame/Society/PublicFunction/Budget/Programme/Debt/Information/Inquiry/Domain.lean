import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (view : View (code := code)) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)

def afterFinite (table : Cut.Table view.point.source view.point.entry view.point.cut) : View (code := code) :=
  ⟨view.point.after rule (Cut.opponent view.point.source view.point.entry view.point.cut table),
    ⟨view.origin.val,by
      have bounded := view.origin.isLt
      change view.origin.val < view.point.source.history.length+2+(view.point.cut+1)+1
      change view.origin.val < view.point.source.history.length+2+view.point.cut+1 at bounded
      omega⟩⟩

def successors (views : List (View (code := code))) := views.flatMap fun view =>
  (Cut.tables view.point.source view.point.entry view.point.cut).map (afterFinite view rule)

structure Covered (rival : Opponent code) (next : View (code := code)) : Prop where
  actual : Covers view.point rule rival next.point
  origin : next.origin.val = view.origin.val

theorem every_actual_successor_has_an_origin_preserving_public_view
    (views : List (View (code := code))) (member : view ∈ views) (rival : Opponent code) :
    ∃ next ∈ successors rule views,Covered view rule rival next := by
  let next := afterFinite view rule (externalTable view.point rival)
  refine ⟨next,List.mem_flatMap.mpr ⟨view,member,List.mem_map.mpr
    ⟨externalTable view.point rival,Residual.restriction_is_generated _ _ _ rival,rfl⟩⟩,?_⟩
  exact ⟨⟨rfl,rfl,
    one_original_external_table_preserves_every_actual_ordinal_state view.point rule rival,
    one_external_table_preserves_the_complete_native_financial_history view.point rule rival⟩,rfl⟩

structure Transition (views : List (View (code := code))) where
  domain : List (View (code := code))
  generated : domain = successors rule views
  covered : ∀ view ∈ views,∀ rival : Opponent code,∃ next ∈ domain,Covered view rule rival next

def extend (views : List (View (code := code))) : Transition rule views :=
  ⟨successors rule views,rfl,fun view member rival =>
    every_actual_successor_has_an_origin_preserving_public_view view rule views member rival⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry
