import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.AllocationStep
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Slot

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good : Type} [DecidableEq Party] [DecidableEq Good]
  (source : ProgrammeSource.Input Party Good Bool Nat Unit) (depth count : Nat)

theorem the_original_zero_use_step_keeps_every_slot_and_the_same_quota
    (origin : Epoch.Finance.ActualItem source depth count)
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (index : Fin state.current.slots.length)
    (obligation : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (present : state.current.slots.get index = .live obligation)
    (receipt : Epoch.Finance.Review source depth count obligation.content)
    (read : Epoch.Finance.readReview source depth count obligation.content origin = some receipt)
    (available : ℚ) (nonnegative : 0 ≤ available) (holder : Party)
    (kind : receipt.kind = .payment holder)
    (unused : receipt.allocated source depth count obligation.residual (min available receipt.quantity) = 0)
    (nonzero : obligation.residual ≠ 0) :
    (nativeAt source depth count origin state index available nonnegative).after.current.slots = state.current.slots ∧
      (nativeAt source depth count origin state index available nonnegative).remaining = available := by
  obtain ⟨slots,quota⟩ := nativeAt_live source depth count origin state index obligation present receipt read available nonnegative
  have unchanged : (nativeReviewBoundary source depth count state index obligation present receipt available nonnegative).event.after
      source depth count = obligation.residual := by
    change receipt.after source depth count obligation.residual (min available receipt.quantity) = obligation.residual
    exact Slot.zero_use_keeps_the_same_original_balance source depth count receipt _ _ holder kind unused
  have same := Slot.an_unchanged_nonzero_original_boundary_keeps_the_same_live_obligation source depth count
    obligation (nativeReviewBoundary source depth count state index obligation present receipt available nonnegative) unchanged nonzero
  refine ⟨?_,?_⟩
  · rw [same] at slots
    refine slots.trans ?_
    rw [← present,List.get_eq_getElem]
    exact List.set_getElem_self index.isLt
  · change _ = available - receipt.allocated source depth count obligation.residual (min available receipt.quantity) at quota
    simpa only [unused,sub_zero] using quota

theorem the_original_fully_paid_step_generates_its_exact_archive_and_remaining_quota
    (origin : Epoch.Finance.ActualItem source depth count)
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (index : Fin state.current.slots.length)
    (obligation : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (present : state.current.slots.get index = .live obligation)
    (receipt : Epoch.Finance.Review source depth count obligation.content)
    (read : Epoch.Finance.readReview source depth count obligation.content origin = some receipt)
    (available : ℚ) (nonnegative : 0 ≤ available) (holder : Party) (quantity : ℚ)
    (kind : receipt.kind = .payment holder)
    (original : obligation.residual = Finsupp.single holder quantity)
    (affordable : quantity ≤ available) (withinSource : quantity ≤ receipt.quantity) :
    ∃ archive : TerminalArchive (Epoch.Finance.vocabulary source depth count),
      (nativeAt source depth count origin state index available nonnegative).after.current.slots =
        state.current.slots.set index (.terminal archive) ∧
      archive.obligation = obligation ∧
      (nativeAt source depth count origin state index available nonnegative).remaining = available - quantity ∧
      archive.sourceEvent = (nativeReviewBoundary source depth count state index obligation present receipt available nonnegative).event := by
  have used : receipt.allocated source depth count obligation.residual (min available receipt.quantity) = quantity := by
    simp only [Epoch.Finance.Review.allocated,Epoch.Finance.Review.fromHolder,kind,original,Finsupp.single_eq_same]
    exact min_eq_right (le_min affordable withinSource)
  have cleared : (nativeReviewBoundary source depth count state index obligation present receipt available nonnegative).event.after
      source depth count = 0 := by
    change receipt.after source depth count obligation.residual (min available receipt.quantity) = 0
    exact Slot.exact_use_pays_the_same_original_singleton source depth count receipt _ _ holder quantity kind original used
  obtain ⟨archive,terminal,old,event⟩ := Slot.a_cleared_original_boundary_retains_its_exact_terminal_obligation source depth count
    obligation (nativeReviewBoundary source depth count state index obligation present receipt available nonnegative) cleared
  obtain ⟨slots,quota⟩ := nativeAt_live source depth count origin state index obligation present receipt read available nonnegative
  refine ⟨archive,?_,old,?_,event⟩
  · exact slots.trans (congrArg (fun slot => state.current.slots.set index slot) terminal)
  · change _ = available - receipt.allocated source depth count obligation.residual (min available receipt.quantity) at quota
    simpa only [used] using quota

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement
