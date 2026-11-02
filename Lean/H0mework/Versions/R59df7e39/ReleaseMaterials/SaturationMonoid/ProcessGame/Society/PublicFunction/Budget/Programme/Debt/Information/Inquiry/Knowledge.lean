import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Evidence
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Alignment

set_option autoImplicit false
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Knowledge

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

structure Matched (representative actual : View (code := code)) : Prop where
  cursor : Aligned representative.point actual.point
  origin : representative.origin.val = actual.origin.val

def Contains (views : List (View (code := code))) (actual : View (code := code)) : Prop :=
  ∃ representative ∈ views,Matched representative actual

theorem member (views : List (View (code := code))) (actual : View (code := code))
    (inside : actual ∈ views) : Contains views actual :=
  ⟨actual,inside,Aligned.refl _,rfl⟩

theorem Matched.remaining {representative actual : View (code := code)}
    (matched : Matched representative actual) (template : Template (code := code)) :
    Debt.remaining representative.point representative.origin template =
      Debt.remaining actual.point actual.origin template := by
  have inputs := matched.cursor.input
  have origins := matched.origin
  have arrivals : arrival representative.point = arrival actual.point := by
    change representative.point.history.length+2+representative.point.cut =
      actual.point.history.length+2+actual.point.cut
    rw [matched.cursor.history,matched.cursor.cut]
  apply Transport.matched_original_and_terminal_accounts_preserve_the_original_remaining
  · constructor
    · simpa only [Debt.account,origins] using congrArg
        (fun input => Identity.financeImage code input (Financial.accountAt input actual.origin.val)) inputs.symm
    · simpa only [Debt.account,origins] using congrArg
        (fun input => Native.Coupling.eventHistory code input (Financial.accountAt input actual.origin.val)) inputs.symm
  · constructor
    · simpa only [arrivals] using congrArg
        (fun input => Identity.financeImage code input (Financial.accountAt input (arrival actual.point))) inputs.symm
    · simpa only [arrivals] using congrArg
        (fun input => Native.Coupling.eventHistory code input (Financial.accountAt input (arrival actual.point))) inputs.symm

theorem Matched.faithful {representative actual : View (code := code)}
    (matched : Matched representative actual) : Evidence.Faithful actual representative :=
  ⟨matched.origin,
    fun site => congrArg (fun state : State code => state.frame.inbox site) matched.cursor.seed,
    matched.remaining,fun template => equal_retained_original_share_summaries_generate_the_same_word
      _ _ template _ _ (matched.remaining template)⟩

theorem after (views : List (View (code := code))) (actual : View (code := code))
    (covered : Contains views actual) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) : Contains (successors rule views) (Evidence.after actual rule rival) := by
  obtain ⟨representative,inside,matched⟩ := covered
  refine ⟨afterFinite representative rule (externalTable representative.point rival),
    List.mem_flatMap.mpr ⟨representative,inside,List.mem_map.mpr
      ⟨externalTable representative.point rival,Residual.restriction_is_generated _ _ _ rival,rfl⟩⟩,
    (Aligned.representative representative.point rule rival).trans (matched.cursor.after rule rival),matched.origin⟩

theorem cursor_covered (views : List (View (code := code))) (actual : View (code := code))
    (covered : Contains views actual) : Continuation.Covered (views.map View.point) actual.point := by
  obtain ⟨representative,inside,matched⟩ := covered
  exact ⟨representative.point,List.mem_map.mpr ⟨representative,inside,rfl⟩,matched.cursor⟩

def CorrectOrConflict (views : List (View (code := code))) (actual : View (code := code)) : Prop :=
  ∀ (template : Template (code := code)) (site : Fin code.sites),
    work views template site (observation actual site) = desired template actual ∨
      ∃ other ∈ views,observation other site = observation actual site ∧
        desired template other ≠ desired template actual ∧
        work views template site (observation actual site) = []

theorem actual_work_is_correct_or_retains_a_real_conflict
    (views : List (View (code := code))) (actual : View (code := code))
    (covered : Contains views actual) : CorrectOrConflict views actual := by
  obtain ⟨representative,inside,matched⟩ := covered
  have faithful := matched.faithful
  intro template site
  cases recover views template site representative inside with
  | resolved correct =>
    exact Or.inl (by rw [faithful.observed site,faithful.desired template] at correct;exact correct)
  | uncertain other original same different empty =>
    exact Or.inr ⟨other,original,same.trans (faithful.observed site),by
      rw [faithful.desired template] at different;exact different,by
      rw [faithful.observed site] at empty;exact empty⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Knowledge
