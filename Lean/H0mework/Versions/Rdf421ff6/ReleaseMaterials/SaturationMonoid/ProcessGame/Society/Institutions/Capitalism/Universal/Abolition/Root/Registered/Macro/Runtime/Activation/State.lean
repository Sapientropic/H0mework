import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Query
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Initial
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Inquiry.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Rank

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (review : Option (ReviewPhase.ContextAt input))

inductive ActivatedFrame : Type 4
  | original (frame : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)
  | enacted (origin : Abolition.Functions.Revision.Context (input := input) (review := review)
      depth count prefixLimit renewalLimit sourceDepth sourceCount)
      (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)
      (frame : Public.Runtime.Frame origin admission)

variable {input depth count prefixLimit renewalLimit sourceDepth sourceCount review}

namespace ActivatedFrame

variable (frame : ActivatedFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

def presentation : RootInquiryStatePresentation := match frame with
  | .original current => Abolition.Functions.Revision.InitialAdmission.Inquiry.presentation
      current.package (.finite current.visit) current.authority
  | .enacted _ _ current => current.presentation

def query : frame.presentation.Query := match frame with
  | .original current => current.query
  | .enacted _ _ current => current.query

theorem query_unique (candidate : frame.presentation.Query) : candidate = frame.query := by
  cases frame with
  | original current => exact current.query_unique candidate
  | enacted origin admission current => exact current.query_unique candidate

end ActivatedFrame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
