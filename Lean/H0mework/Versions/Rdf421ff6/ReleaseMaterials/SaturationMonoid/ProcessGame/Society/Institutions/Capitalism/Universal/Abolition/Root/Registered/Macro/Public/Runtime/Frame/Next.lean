import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Ordinary
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Born
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Reentry

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

def internalNext (work : frame.HasWork) : Frame origin admission :=
  match parsed : Accounting.registration? input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past frame.start frame.actual.actual with
  | some registered => frame.born registered
  | none => frame.ordinary work parsed

def next : Frame origin admission :=
  if work : frame.HasWork then frame.internalNext work else frame.reenter work

theorem internal_next_spends_one_source_position (work : frame.HasWork) :
    (frame.internalNext work).sourceMass + 1 = frame.sourceMass := by
  unfold internalNext
  split
  · exact frame.born_spends_one_source_position _
  · exact frame.ordinary_spends_one_source_position work _

theorem next_spends_one_source_position (work : frame.HasWork) :
    frame.next.sourceMass + 1 = frame.sourceMass := by
  rw [next, dif_pos work]
  exact frame.internal_next_spends_one_source_position work

#print axioms next
#print axioms next_spends_one_source_position

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
