import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Next

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

theorem work_iff_positive_mass : frame.HasWork ↔ 0 < frame.sourceMass :=
  Accounting.Drain.actual_work_iff_positive_source_mass frame.source frame.actual.actual

theorem zero_mass_is_an_actual_exhausted_source (zero : frame.sourceMass = 0) :
    ¬ frame.HasWork ∧
      Accounting.item? input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual = none := by
  refine ⟨fun work => Nat.ne_of_gt (frame.work_iff_positive_mass.mp work) zero, ?_⟩
  exact (Accounting.zero_source_mass_has_no_unpaid_internal_work input depth count prefixLimit renewalLimit
    origin.germ.snapshot.past frame.start frame.actual.actual zero).2

theorem every_internal_next_strictly_lowers_the_actual_source (work : frame.HasWork) :
    frame.next.sourceMass < frame.sourceMass := by
  have spent := frame.next_spends_one_source_position work
  omega

#print axioms work_iff_positive_mass
#print axioms every_internal_next_strictly_lowers_the_actual_source

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
