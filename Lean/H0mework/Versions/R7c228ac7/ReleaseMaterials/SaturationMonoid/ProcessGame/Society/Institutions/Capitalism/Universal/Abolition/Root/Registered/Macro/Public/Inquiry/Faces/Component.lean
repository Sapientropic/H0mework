import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Faces.Types

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start)

variable (reader : Macro.Raw.Reader input depth count)

def component : SourceNativeProjectionLaw frame.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := ActiveAt frame
  InactiveAt := InactiveAt frame
  classify := classify frame
  PayloadAt := fun projection {_current} occurrence active => match projection with
    | .query => PUnit
    | .answer => InternalAnswer frame
    | .compilation => SourceNativeInquiryCompilationTokenAt (frame.family.entry occurrence.1) PUnit.unit
        (ULift.up.{1, 0} occurrence)
        (.answered : SourceNativeInquiryFrontAuditAt frame.basis.U7 frame.basis.calculus
          frame.root.toAuthoritativeRoot.source.lawSurface occurrence.1)
        (active.AnswerAt reader)
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit (ULift.up.{1, 0} occurrence)
        (frame.family.entry occurrence.1) (internalAnswer frame active.val.actual)
    | .snapshot => Snapshot (input := input) (depth := depth) (count := count)
    | .nativeAccount => (Epoch.Finance.process input depth count).GeneratedState
    | .publicLaw => Source.Program.RawLaw Party Good Port Technology Instrument
    | .sourceReport => active.val.RawAnswer reader
  project := fun projection {_current} _occurrence active => match projection with
    | .query => PUnit.unit
    | .answer => internalAnswer frame active.val.actual
    | .compilation => .canonical (active.sourceAnswer reader)
    | .consumer => .canonical
    | .snapshot => {
        oldPast := oldPast
        physical := active.snapshot
        actual := Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast active.snapshot.past
        account := active.actual.account
        planningWindow := (prefixLimit, renewalLimit)
        fullAccount := Abolition.Completion.Actual.Dividend.Financial.check
          input depth count prefixLimit renewalLimit oldPast active.snapshot }
    | .nativeAccount => active.actual.account
    | .publicLaw => Physical.Public.interpreter input
    | .sourceReport => active.val.rawAnswer reader

def installedFrame : NativeFrame input depth count prefixLimit renewalLimit oldPast start :=
  frame.withProjectionCoface (component frame reader)

def installation : SourceNativeProjectionLaw.InstallationAt (component frame reader)
    (installedFrame frame reader).root.source.base.projectionLaw :=
  .componentCoface frame.root.source.base (component frame reader)

#print axioms component

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry
