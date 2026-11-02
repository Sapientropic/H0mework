import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Projection.Shape
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Next
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Initial

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
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

namespace Frame

variable (frame : Frame origin admission)

abbrev Layout := ProjectionLayout frame.source.root.toAuthoritativeRoot.source.projectionLaw.Projection

def layoutOrdinary (layout : frame.Layout) (work : frame.HasWork)
    (noIssue : Accounting.registration? input depth count prefixLimit renewalLimit origin.germ.snapshot.past
      frame.start frame.actual.actual = none) : (frame.ordinary work noIssue).Layout := layout

def layoutBorn (layout : frame.Layout)
    (registered : Accounting.Registration input depth count prefixLimit renewalLimit origin.germ.snapshot.past
      frame.start frame.actual.actual) : (frame.born registered).Layout where
  births := layout.births + 1
  source_eq := congrArg (fun projection => SourceNativeProjectionCoface Accounting.Born.Source.Projection
    (SourceNativeProjectionCoface projection Inquiry.Projection)) layout.source_eq

def layoutReenter (complete : ¬ frame.HasWork) : (frame.reenter complete).Layout := by
  cases admission <;> exact ⟨0, rfl⟩

def layoutNext (layout : frame.Layout) : frame.next.Layout := by
  unfold Frame.next
  split
  · unfold Frame.internalNext
    split
    · exact frame.layoutBorn layout _
    · exact frame.layoutOrdinary layout _ _
  · exact frame.layoutReenter _

end Frame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime
