import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Faces.Installed
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.SourceRank
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.Installed
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)

/-- A dependent package of the existing source and visit. The canonical
Engine obtains it from the source-owned initial and step producers. -/
structure Frame (_admission : Abolition.Functions.Revision.InitialAdmissionAt origin) where
  start : Physical.Cursor Party Good Port Technology Instrument
  reader : Macro.Raw.Reader input depth count
  source : NativeFrame input depth count prefixLimit renewalLimit origin.germ.snapshot.past start
  visit : RootVisit (Inquiry.installedFrame source reader).root.toAuthoritativeRoot.toRoot
  actual : Inquiry.ActualAt source visit.current
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (Inquiry.installedFrame source reader).root
    (.finite visit) ((Inquiry.installedFrame source reader).entry visit.current)
  paid : actual.actual.bodyPaid = true

variable {origin admission}
namespace Frame

variable (frame : Frame origin admission)

def full := Inquiry.installedFrame frame.source frame.reader

def actualForFull : Inquiry.ActualAt frame.full frame.visit.current :=
  ⟨frame.actual.actual, frame.actual.aligned⟩

def HasWork : Prop := Inquiry.HasWork frame.source frame.actual.actual

instance : Decidable frame.HasWork := inferInstanceAs (Decidable (Inquiry.HasWork _ _))

def snapshot := frame.actual.snapshot

def account := frame.actual.actual.account

def sourceMass := Accounting.mass input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual

end Frame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime
