import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Bound.Native
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Snapshot

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Bound

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

local notation "F" => Runtime.Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount

def minor (frame : F) := rank (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
  frame.start frame.proposal frame.sourcePosition frame.cursor

def after (frame : F) : Nat → F
  | 0 => frame
  | steps + 1 => (after frame steps).next

theorem after_next (frame : F) (steps : Nat) : after frame.next steps = after frame (steps + 1) := by
  induction steps with
  | zero => rfl
  | succ steps prior => exact congrArg Runtime.Frame.next prior

theorem work_has_pending_items (frame : F)
    (work : Inquiry.HasWork frame.package.source frame.visit.current) : 0 < minor frame := by
  by_contra none
  have zero : minor frame = 0 := by omega
  have complete := (zero_rank_iff_complete (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    frame.start frame.proposal frame.sourcePosition frame.cursor).mp zero
  exact Raw.complete_has_no_internal_work frame.package.source frame.visit.current complete work

theorem ordinary_minor (frame : F) (work : Inquiry.HasWork frame.package.source frame.visit.current) :
    minor frame.ordinary + 1 = minor frame :=
  every_pending_root_successor_consumes_one_unit (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current
    (frame.package.frame.successor frame.visit.current) (work_has_pending_items frame work)

theorem born_minor (frame : F)
    (work : Inquiry.HasWork frame.package.source frame.visit.current)
    (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current) :
    minor (frame.born registered) + 1 = minor frame := by
  have same := (frame.package.born registered).frame.next_exact (Admission.initial frame.package.frame registered)
  exact (congrArg (fun current => rank (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    frame.start frame.proposal frame.sourcePosition current + 1) same).trans
    (each_pending_source_step_consumes_one_unit (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      frame.start frame.proposal frame.sourcePosition frame.cursor (work_has_pending_items frame work))

theorem every_pending_accounting_query_pays_one_original_item
    (frame : F) (query : frame.presentation.Query) (pending : 0 < minor frame) :
    minor (frame.nextAt query) + 1 = minor frame ∧
      (frame.nextAt query).snapshot = frame.snapshot := by
  cases query with
  | internal work =>
      change minor frame.internalNext + 1 = minor frame ∧ frame.internalNext.snapshot = frame.snapshot
      unfold Runtime.Frame.internalNext
      split
      · exact ⟨born_minor frame work _, rfl⟩
      · exact ⟨ordinary_minor frame work, rfl⟩
  | raw germ =>
      have zero := (zero_rank_iff_complete (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
        frame.start frame.proposal frame.sourcePosition frame.cursor).mpr germ.complete
      change minor frame = 0 at zero
      omega

/-- Only the already generated accounting inventory is drained. Each step
is the same root's actual next, including native debt admission. -/
theorem exact_original_inventory_closes_its_own_bookkeeping (frame : F) :
    minor (after frame (minor frame)) = 0 ∧
      (after frame (minor frame)).snapshot = frame.snapshot := by
  generalize bound : minor frame = steps
  induction steps generalizing frame with
  | zero => exact ⟨bound, rfl⟩
  | succ steps inherited =>
      have paid := every_pending_accounting_query_pays_one_original_item frame frame.query (by omega)
      have exactPaid : minor frame.next + 1 = minor frame := paid.1
      have nextBound : minor frame.next = steps := by omega
      have later := inherited frame.next nextBound
      rw [← after_next]
      exact ⟨later.1, later.2.trans paid.2⟩

theorem generated_bookkeeping_completion (frame : F) :
    let finished := after frame (minor frame)
    Complete (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      finished.start finished.proposal finished.sourcePosition finished.cursor ∧
      finished.snapshot = frame.snapshot :=
  ⟨(zero_rank_iff_complete (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      _ _ _ _).mp (exact_original_inventory_closes_its_own_bookkeeping frame).1,
    (exact_original_inventory_closes_its_own_bookkeeping frame).2⟩

#print axioms every_pending_accounting_query_pays_one_original_item
#print axioms generated_bookkeeping_completion

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Bound
