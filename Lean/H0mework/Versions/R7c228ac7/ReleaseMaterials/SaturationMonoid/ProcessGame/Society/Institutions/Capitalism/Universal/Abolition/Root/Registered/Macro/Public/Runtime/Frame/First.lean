import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Bound

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

/-- The generated drain is the first actual raw-query boundary. It cannot
silently pass a pending issue, enter a later batch, and count that endpoint. -/
theorem drain_does_not_skip_internal_work (frame : Frame origin admission) (index : Nat)
    (before : index < frame.drain.1) : (frame.visits index).HasWork := by
  by_cases work : frame.HasWork
  · have count : frame.drain.1 = frame.next.drain.1 + 1 := by rw [drain, dif_pos work]
    cases index with
    | zero => simpa only [visits, Function.iterate_zero, id_eq] using work
    | succ index =>
      have smaller : index < frame.next.drain.1 := by omega
      have actual := drain_does_not_skip_internal_work frame.next index smaller
      simpa only [visits, Function.iterate_succ_apply] using actual
  · have empty : frame.drain.1 = 0 := by rw [drain, dif_neg work]
    omega
termination_by frame.sourceMass
decreasing_by exact frame.every_internal_next_strictly_lowers_the_actual_source work

#print axioms drain_does_not_skip_internal_work

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
