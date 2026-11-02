import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.Domain
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

private theorem bounded_horizon (views : List (View (code := code))) (bound : Nat)
    (bounded : ∀ view ∈ views,Cut.horizon view.point.source view.point.entry view.point.cut ≤ bound) :
    horizon (views.map View.point) ≤ bound := by
  induction views with
  | nil => exact Nat.zero_le _
  | cons first rest ih =>
      exact max_le (bounded first (List.mem_cons_self)) (ih (fun view inside => bounded view (List.mem_cons_of_mem _ inside)))

theorem every_public_successor_retains_its_actual_predecessor
    (views : List (View (code := code))) (rule : Prefix.Rule code)
    (next : View (code := code)) (member : next ∈ PublicDomain.next rule views) :
    ∃ previous ∈ views,∃ rival : Opponent code,next = Evidence.after previous rule rival := by
  unfold PublicDomain.next at member
  split at member
  · obtain ⟨previous,inside,same⟩ := List.mem_map.mp member
    exact ⟨previous,inside,PublicDomain.silent,same.symm⟩
  · exact Evidence.every_public_successor_is_an_actual_source rule views next member

theorem one_public_update_cannot_invent_a_larger_physical_window
    (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (views : List (View (code := model.source.code))) (rule : Prefix.Rule model.source.code) :
    horizon ((PublicDomain.next rule views).map View.point) ≤ horizon (views.map View.point) := by
  apply bounded_horizon
  intro next inside
  obtain ⟨previous,old,rival,same⟩ := every_public_successor_retains_its_actual_predecessor views rule next inside
  rw [same]
  have remaining := Installation.Chain.after_remaining (model := model) previous.point rule rival
  change ((previous.point.after rule rival).source.feedbackState (previous.point.after rule rival).entry
    (previous.point.cut+1)).remaining ≤ _
  rw [remaining]
  exact (Nat.sub_le _ 1).trans (Continuation.Whole.Complete.each_remaining_horizon_is_generated
    (views.map View.point) previous.point (List.mem_map.mpr ⟨previous,old,rfl⟩))

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (views : List (View (code := model.source.code)))

theorem the_paid_public_past_bounds_every_current_local_planning_domain
    (past : List (Prefix.Rule model.source.code)) (site : Fin model.source.code.sites) (signal : Fin model.source.code.signals) :
    horizon ((fiber (Window.Observed.Transcript.publicViews past views) site signal).map View.point) ≤
      horizon (views.map View.point) := by
  have global : horizon ((Window.Observed.Transcript.publicViews past views).map View.point) ≤ horizon (views.map View.point) := by
    induction past generalizing views with
    | nil => exact Nat.le_refl _
    | cons rule rest ih =>
        exact (ih (PublicDomain.next rule views)).trans (one_public_update_cannot_invent_a_larger_physical_window model views rule)
  apply le_trans (bounded_horizon _ _ ?_) global
  intro view inside
  exact Continuation.Whole.Complete.each_remaining_horizon_is_generated _ view.point
    (List.mem_map.mpr ⟨view,((mem_fiber _ _ _ _).mp inside).1,rfl⟩)

theorem every_received_local_domain_covers_all_finite_future_programs
    (past : List (Prefix.Rule model.source.code)) (original : Prefix.Rule model.source.code)
    (reference : Program model.source.code (horizon (views.map View.point)))
    (site : Fin model.source.code.sites) (signal : Fin model.source.code.signals) :
    match plan model (Window.Observed.Transcript.publicViews past views) original reference site signal with
    | none => True
    | some outcome => Complete.Contract model
        (localDomain model (Window.Observed.Transcript.publicViews past views) site signal) original reference outcome := by
  unfold plan
  split
  · trivial
  · exact Complete.every_generated_outcome_covers_all_finite_programs _ _ _
      (the_paid_public_past_bounds_every_current_local_planning_domain model views past site signal) _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.Domain
