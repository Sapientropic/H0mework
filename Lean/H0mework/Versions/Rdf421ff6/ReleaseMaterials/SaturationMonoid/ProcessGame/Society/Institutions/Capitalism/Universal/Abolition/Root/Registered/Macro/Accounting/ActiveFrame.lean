import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Component

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

def activeFrame := Inquiry.installFrame
  (nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (Inquiry.baseBasis (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)

def activeInstallation := Inquiry.installation
  (nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (Inquiry.baseBasis (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)

def internalInput (visit : SourceNativeTemporalVisitAt
      (activeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).root.toAuthoritativeRoot.toLedgerRoot)
    (work : Inquiry.HasWork
      (nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) visit.current) :
    SourceNativeRootInquiryInputAt
      (activeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).root visit PUnit :=
  Inquiry.registeredInput
    (nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (Inquiry.baseBasis (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) visit work

theorem complete_inquiry_root_keeps_the_same_material_source :
    (activeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).root.toAuthoritativeRoot.toLedgerRoot =
      (livingRoot (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).toAuthoritativeRoot.toLedgerRoot := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting
