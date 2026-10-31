import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Drain.Source

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
  (registered : Accounting.Registration input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual)

def born : Frame origin admission where
  start := frame.start
  reader := frame.reader
  source := Accounting.Born.Action.targetFrame frame.full (.finite frame.visit) frame.actual.actual registered
  visit := (Accounting.Born.Action.completeFrame frame.full (.finite frame.visit) frame.actual.actual registered frame.reader).root.toAuthoritativeRoot.toRoot.initialVisit.next
    (Accounting.Born.Source.firstSuccessor frame.full.family frame.actual.actual registered).next_eq
  actual := ⟨registered.next, Accounting.Born.Source.first_visit_is_the_literal_registered_next frame.full.family frame.actual.actual registered⟩
  authority := Accounting.Born.Action.completeNextAuthority frame.full (.finite frame.visit) frame.actual.actual frame.actual.aligned registered frame.reader frame.authority
  paid := rfl

theorem born_spends_one_source_position :
    (frame.born registered).sourceMass + 1 = frame.sourceMass :=
  Accounting.the_original_admission_spends_exactly_its_actual_head input depth count prefixLimit renewalLimit
    origin.germ.snapshot.past frame.start registered

#print axioms born
#print axioms born_spends_one_source_position

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
