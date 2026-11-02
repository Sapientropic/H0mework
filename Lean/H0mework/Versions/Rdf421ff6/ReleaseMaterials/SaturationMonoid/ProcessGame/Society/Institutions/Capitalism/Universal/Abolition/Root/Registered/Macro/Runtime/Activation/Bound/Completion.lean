import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Bound.Prefix

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

structure Completion (frame : F) where
  steps : Nat
  within : steps ≤ internalMass frame
  finished : internalMass (after frame steps) = 0

/-- Each branch consumes its existing source inventory producer. The common
fold stops at the first raw boundary, before choosing a new physical word. -/
def complete (frame : F) : Completion frame := by
  cases frame with
  | original current =>
    refine ⟨Bound.minor current, Nat.le_refl _, ?_⟩
    rw [original_internal_prefix_is_the_original_paid_inventory current _ (Nat.le_refl _)]
    exact (Bound.exact_original_inventory_closes_its_own_bookkeeping current).1
  | enacted origin admission current =>
    refine ⟨current.drain.1, current.drain.2.1, ?_⟩
    rw [enacted_prefix_is_the_same_public_source]
    change current.drained.sourceMass = 0
    have done := current.drain.2.2
    have nonpositive : ¬ 0 < current.drained.sourceMass :=
      fun positive => done (current.drained.work_iff_positive_mass.mpr positive)
    omega

def completed (frame : F) : F := after frame frame.complete.steps

theorem completion_uses_only_the_actual_inventory (frame : F) :
    frame.complete.steps ≤ internalMass frame ∧ internalMass frame.completed = 0 :=
  ⟨frame.complete.within, frame.complete.finished⟩

theorem every_internal_prefix_retains_its_unspent_position (frame : F) (steps : Nat)
    (within : steps ≤ internalMass frame) :
    internalMass (after frame steps) + steps = internalMass frame := by
  induction steps generalizing frame with
  | zero => simp only [after, Function.iterate_zero, id_eq, Nat.add_zero]
  | succ steps inherited =>
    have positive : 0 < internalMass frame := by omega
    have spent := every_pending_internal_next_spends_one frame positive
    have tail : steps ≤ internalMass frame.next := by omega
    have retained := inherited frame.next tail
    rw [after_next] at retained
    omega

theorem completion_is_the_first_actual_raw_boundary (frame : F) :
    frame.complete.steps = internalMass frame ∧
      ∀ index < frame.complete.steps, 0 < internalMass (after frame index) := by
  have retained := every_internal_prefix_retains_its_unspent_position frame _ frame.complete.within
  have done := frame.complete.finished
  constructor
  · omega
  · intro index before
    have within : index ≤ internalMass frame := by omega
    have atIndex := every_internal_prefix_retains_its_unspent_position frame index within
    omega

#print axioms complete
#print axioms completion_is_the_first_actual_raw_boundary

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.ActivatedFrame
