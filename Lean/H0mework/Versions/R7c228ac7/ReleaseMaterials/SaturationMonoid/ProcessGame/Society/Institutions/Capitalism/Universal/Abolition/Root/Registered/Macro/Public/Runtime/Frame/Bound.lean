import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Rank

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Abolition.Functions.Revision.InitialAdmissionAt origin}

def visits (frame : Frame origin admission) (tick : Nat) : Frame origin admission := (next^[tick]) frame

/-- This finite fold follows the same source-selected next. It stops before
reading a fresh raw proposal; neither birth nor a new account anchor refills
an already consumed position in this occurrence. -/
def drain (frame : Frame origin admission) :
    {tick : Nat // tick ≤ frame.sourceMass ∧ ¬ (frame.visits tick).HasWork} :=
  if work : frame.HasWork then
    let tail := drain frame.next
    ⟨tail.1 + 1, by have spent := frame.next_spends_one_source_position work; omega,
      by simpa only [visits, Function.iterate_succ_apply] using tail.2.2⟩
  else ⟨0, Nat.zero_le _, by simpa only [visits, Function.iterate_zero, id_eq] using work⟩
termination_by frame.sourceMass
decreasing_by exact frame.every_internal_next_strictly_lowers_the_actual_source work

def drained (frame : Frame origin admission) : Frame origin admission := frame.visits frame.drain.1

theorem the_generated_drain_is_ready_for_the_actual_raw_query (frame : Frame origin admission) :
    frame.drain.1 ≤ frame.sourceMass ∧ ¬ frame.drained.HasWork := frame.drain.2

theorem every_selected_internal_path_is_finite
    (path : Nat → Frame origin admission)
    (selected : ∀ tick, (path tick).HasWork → path (tick + 1) = (path tick).next) :
    ∃ tick ≤ (path 0).sourceMass, ¬ (path tick).HasWork := by
  suffices ∀ fuel (route : Nat → Frame origin admission), (route 0).sourceMass = fuel →
      (∀ tick, (route tick).HasWork → route (tick + 1) = (route tick).next) →
      ∃ tick ≤ fuel, ¬ (route tick).HasWork from this _ path rfl selected
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel smaller =>
    intro route sourceEq lawful
    by_cases work : (route 0).HasWork
    · have stepEq := lawful 0 work
      have spent := (route 0).next_spends_one_source_position work
      have nextSmall : (route 1).sourceMass < fuel := by rw [stepEq]; omega
      obtain ⟨tick, within, done⟩ := smaller (route 1).sourceMass nextSmall
        (fun index => route (index + 1)) rfl (fun index work => lawful (index + 1) work)
      exact ⟨tick + 1, by rw [stepEq] at within; omega, done⟩
    · exact ⟨0, Nat.zero_le _, work⟩

#print axioms drain
#print axioms the_generated_drain_is_ready_for_the_actual_raw_query
#print axioms every_selected_internal_path_is_finite

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
