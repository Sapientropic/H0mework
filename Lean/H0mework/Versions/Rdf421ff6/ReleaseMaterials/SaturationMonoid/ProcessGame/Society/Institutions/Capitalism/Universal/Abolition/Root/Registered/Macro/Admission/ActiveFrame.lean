import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.NativeFrame
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Component

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  {origin : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)
  (basis : Inquiry.Basis frame.N)

def inquiryBasis : Inquiry.Basis (N frame registered) where
  entry := fun support => oldEntry (state? := support.2) (basis.entry support.1)
  disposition := fun support kind => match kind with
    | .supportSettlement => basis.disposition support.1 .supportSettlement
    | .transfer => .inl (basis.disposition support.1 .transfer)
    | .lawSurfaceExtension => .inl (basis.disposition support.1 .lawSurfaceExtension)

def activeFrame := Inquiry.installFrame (nativeFrame frame registered) (inquiryBasis frame registered basis)

def activeInstallation := Inquiry.installation (nativeFrame frame registered) (inquiryBasis frame registered basis)

theorem old_projection_outcome_is_preserved
    (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((activeFrame frame registered basis).root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (.inherited (.inl projection)) ((activeFrame frame registered basis).root.emitted (initial frame registered)))
      (frame.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (frame.root.emitted origin)) := by
  have lifted := (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (livingRoot frame registered).source.base
    (Inquiry.component (nativeFrame frame registered) (inquiryBasis frame registered basis))).outcome_heq
      (emitted frame registered (initial frame registered)) (.inl projection)
  refine lifted.trans ?_
  change HEq ((projectionLaw frame registered).outcomeAt (.inl projection)
    (emitted frame registered (initial frame registered)))
    (frame.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (frame.root.emitted origin))
  unfold SourceNativeProjectionLaw.outcomeAt
  dsimp only [projectionLaw, classify, initial]
  cases frame.root.toAuthoritativeRoot.source.projectionLaw.classify projection (frame.root.emitted origin) <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
