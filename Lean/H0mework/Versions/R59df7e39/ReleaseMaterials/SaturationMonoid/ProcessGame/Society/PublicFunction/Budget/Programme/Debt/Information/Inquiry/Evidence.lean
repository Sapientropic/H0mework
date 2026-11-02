import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Domain
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Transport

set_option autoImplicit false
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Evidence

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (view : View (code := code)) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)

def after (rival : Opponent code) : View (code := code) :=
  ⟨view.point.after rule rival,⟨view.origin.val,by
    have bounded := view.origin.isLt
    change view.origin.val < view.point.source.history.length+2+(view.point.cut+1)+1
    change view.origin.val < view.point.source.history.length+2+view.point.cut+1 at bounded
    omega⟩⟩

structure Faithful (actual representative : View (code := code)) : Prop where
  origin : representative.origin.val = actual.origin.val
  observed : ∀ site,observation representative site = observation actual site
  remaining : ∀ template : Template (code := code),
    Debt.remaining representative.point representative.origin template = Debt.remaining actual.point actual.origin template
  desired : ∀ template : Template (code := code),desired template representative = desired template actual

variable (rival : Opponent code)

theorem projected_successors_are_the_original_recursive_domain
    (views : List (View (code := code))) :
    (successors rule views).map View.point = Continuation.advance code (views.map View.point) rule := by
  induction views with
  | nil => rfl
  | cons first rest ih =>
    simpa only [successors,Continuation.advance,List.flatMap_cons,List.map_cons,List.map_append,
      List.map_flatMap,List.map_map,Function.comp_def,afterFinite] using congrArg
      (fun tail => ((Cut.tables first.point.source first.point.entry first.point.cut).map
        (fun table => first.point.after rule (Cut.opponent first.point.source first.point.entry first.point.cut table))) ++ tail) ih

theorem the_original_external_representative_preserves_local_knowledge :
    Faithful (after view rule rival) (afterFinite view rule (externalTable view.point rival)) := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro site
    exact congrArg (fun state : State code => state.frame.inbox site)
      (one_original_external_table_preserves_every_actual_ordinal_state view.point rule rival 1)
  · intro template
    exact (Transport.matched_original_and_terminal_accounts_preserve_the_original_remaining
      (after view rule rival).point (afterFinite view rule (externalTable view.point rival)).point
      (after view rule rival).origin (afterFinite view rule (externalTable view.point rival)).origin template
      (one_external_table_preserves_the_complete_native_financial_history view.point rule rival view.origin.val)
      (one_external_table_preserves_the_complete_native_financial_history view.point rule rival
        (arrival (after view rule rival).point))).symm
  · intro template
    exact (Transport.matched_original_and_terminal_accounts_generate_the_same_original_word
      (after view rule rival).point (afterFinite view rule (externalTable view.point rival)).point
      (after view rule rival).origin (afterFinite view rule (externalTable view.point rival)).origin template
      (one_external_table_preserves_the_complete_native_financial_history view.point rule rival view.origin.val)
      (one_external_table_preserves_the_complete_native_financial_history view.point rule rival
        (arrival (after view rule rival).point))).symm

theorem every_actual_successor_has_a_faithful_public_representative
    (views : List (View (code := code))) (member : view ∈ views) :
    ∃ next ∈ successors rule views,Covered view rule rival next ∧ Faithful (after view rule rival) next := by
  let next := afterFinite view rule (externalTable view.point rival)
  refine ⟨next,List.mem_flatMap.mpr ⟨view,member,List.mem_map.mpr
    ⟨externalTable view.point rival,Residual.restriction_is_generated _ _ _ rival,rfl⟩⟩,?_,
    the_original_external_representative_preserves_local_knowledge view rule rival⟩
  exact ⟨⟨rfl,rfl,
    one_original_external_table_preserves_every_actual_ordinal_state view.point rule rival,
    one_external_table_preserves_the_complete_native_financial_history view.point rule rival⟩,rfl⟩

theorem every_public_successor_is_an_actual_source
    (views : List (View (code := code))) (next : View (code := code))
    (member : next ∈ successors rule views) :
    ∃ previous ∈ views,∃ opponent : Opponent code,next = after previous rule opponent := by
  obtain ⟨previous,original,present⟩ := List.mem_flatMap.mp member
  obtain ⟨table,generated,equal⟩ := List.mem_map.mp present
  exact ⟨previous,original,Cut.opponent previous.point.source previous.point.entry previous.point.cut table,equal.symm⟩

theorem actual_successor_fibers_are_exact
    (views : List (View (code := code))) (member : view ∈ views)
    (site : Fin code.sites) (signal : Fin code.signals) :
    observation (after view rule rival) site = signal ↔
      ∃ next ∈ fiber (successors rule views) site signal,Faithful (after view rule rival) next := by
  constructor
  · intro observed
    obtain ⟨next,original,_,faithful⟩ := every_actual_successor_has_a_faithful_public_representative view rule rival views member
    exact ⟨next,(mem_fiber _ _ _ _).mpr ⟨original,(faithful.observed site).trans observed⟩,faithful⟩
  · rintro ⟨next,original,faithful⟩
    exact (faithful.observed site).symm.trans ((mem_fiber _ _ _ _).mp original).2

theorem successor_work_is_correct_or_has_an_actual_information_conflict
    (views : List (View (code := code))) (member : view ∈ views)
    (template : Template (code := code)) (site : Fin code.sites) :
    work (successors rule views) template site (observation (after view rule rival) site) =
        desired template (after view rule rival) ∨
      ∃ other ∈ successors rule views,
        observation other site = observation (after view rule rival) site ∧
        desired template other ≠ desired template (after view rule rival) ∧
        work (successors rule views) template site (observation (after view rule rival) site) = [] := by
  obtain ⟨next,original,_,faithful⟩ := every_actual_successor_has_a_faithful_public_representative view rule rival views member
  cases recover (successors rule views) template site next original with
  | resolved correct =>
    exact Or.inl (by rw [faithful.observed site,faithful.desired template] at correct;exact correct)
  | uncertain other generated same different empty =>
    exact Or.inr ⟨other,generated,same.trans (faithful.observed site),by
      rw [faithful.desired template] at different;exact different,by
      rw [faithful.observed site] at empty;exact empty⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Evidence
