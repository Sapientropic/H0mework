import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Next

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
  (frame : Frame origin admission)

theorem snapshot_is_the_literal_after : frame.snapshot = Physical.next frame.start := by
  simp only [snapshot, Inquiry.ActualAt.snapshot, frame.paid, if_true]

theorem ordinary_snapshot (work : frame.HasWork)
    (noIssue : Accounting.registration? input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual = none) :
    (frame.ordinary work noIssue).snapshot = frame.snapshot := by
  rw [(frame.ordinary work noIssue).snapshot_is_the_literal_after, frame.snapshot_is_the_literal_after]
  rfl

theorem born_snapshot
    (registered : Accounting.Registration input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual) :
    (frame.born registered).snapshot = frame.snapshot := by
  rw [(frame.born registered).snapshot_is_the_literal_after, frame.snapshot_is_the_literal_after]
  rfl

theorem reentry_past_is_the_actual_source_extension (complete : ¬ frame.HasWork) :
    (frame.reenter complete).snapshot.past = frame.snapshot.past ++
      [Scope.executionRaw input depth count prefixLimit renewalLimit origin.germ.snapshot.past
        frame.snapshot (frame.actual.proposal frame.reader)] := by
  rw [(frame.reenter complete).snapshot_is_the_literal_after]
  rfl

theorem reentry_adds_one_actual_input (complete : ¬ frame.HasWork) :
    (frame.reenter complete).snapshot.past.length = frame.snapshot.past.length + 1 := by
  rw [frame.reentry_past_is_the_actual_source_extension complete, List.length_append, List.length_singleton]

#print axioms snapshot_is_the_literal_after
#print axioms reentry_past_is_the_actual_source_extension
#print axioms reentry_adds_one_actual_input

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
