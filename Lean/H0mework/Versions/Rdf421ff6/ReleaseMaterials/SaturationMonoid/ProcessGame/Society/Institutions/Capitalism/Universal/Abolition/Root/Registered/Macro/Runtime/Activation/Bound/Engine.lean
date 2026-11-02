import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Bound.Boundary
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Bound.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.ActivatedFrame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

local notation "F" => ActivatedFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount

/-- The terminal raw action is included: the finite bound closes internal
work, while its original compiler still produces the whole-ledger next. -/
theorem finite_internal_engine_cone (frame : F) :
    frame.complete.steps ≤ internalMass frame ∧
    internalMass frame.completed = 0 ∧
    (∀ index < frame.complete.steps, 0 < internalMass (after frame index)) ∧
    (∀ index ≤ frame.complete.steps,
      frame.account.current.slots.map (Epoch.Finance.slotClaim input depth count) <+:
        (after frame index).account.current.slots.map (Epoch.Finance.slotClaim input depth count)) ∧
    (∀ index ≤ frame.complete.steps,
      frame.account.current.history <+: (after frame index).account.current.history) ∧
    (∀ index ≤ frame.complete.steps,
      (after frame index).next.presentation.erase =
          (RootInquiryProcessNode.answered (after frame index).presentation (after frame index).query).erase ∧
        (RootInquiryProcessNode.active (after frame index).presentation).PreservesGeneratedLivingLawAt
          (after frame index).query (.active (after frame index).next.presentation)) :=
  ⟨frame.complete.within, frame.complete.finished,
    (completion_is_the_first_actual_raw_boundary frame).2,
    fun index _ => every_actual_prefix_keeps_all_original_claims frame index,
    fun index _ => every_actual_prefix_keeps_the_complete_native_history frame index,
    fun index _ => (after frame index).successor_valid (after frame index).query⟩

theorem every_selected_internal_path_is_finite
    (path : Nat → F)
    (selected : ∀ tick, 0 < internalMass (path tick) → path (tick + 1) = (path tick).next) :
    ∃ tick ≤ internalMass (path 0), internalMass (path tick) = 0 := by
  suffices ∀ fuel (route : Nat → F), internalMass (route 0) = fuel →
      (∀ tick, 0 < internalMass (route tick) → route (tick + 1) = (route tick).next) →
      ∃ tick ≤ fuel, internalMass (route tick) = 0 from this _ path rfl selected
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel smaller =>
    intro route sourceEq lawful
    by_cases positive : 0 < internalMass (route 0)
    · have stepEq := lawful 0 positive
      have spent := every_pending_internal_next_spends_one (route 0) positive
      have nextSmall : internalMass (route 1) < fuel := by rw [stepEq]; omega
      obtain ⟨tick, within, done⟩ := smaller (internalMass (route 1)) nextSmall
        (fun index => route (index + 1)) rfl (fun index work => lawful (index + 1) work)
      exact ⟨tick + 1, by rw [stepEq] at within; omega, done⟩
    · exact ⟨0, Nat.zero_le _, by omega⟩

theorem an_empty_old_inventory_does_not_wait_for_the_old_physical_rank
    (frame : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)
    (done : Bound.minor frame = 0) :
    (ActivatedFrame.original frame : F).complete.steps = 0 := by
  rw [(completion_is_the_first_actual_raw_boundary (.original frame : F)).1]
  exact done

#print axioms finite_internal_engine_cone
#print axioms every_selected_internal_path_is_finite
#print axioms an_empty_old_inventory_does_not_wait_for_the_old_physical_rank

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.ActivatedFrame
