import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Compilation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Compilation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (package : Macro.Inquiry.Package (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (visit : SourceNativeTemporalVisitAt package.frame.root.toAuthoritativeRoot.toLedgerRoot)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt package.frame.root visit (package.frame.entry visit.current))

def contextAt (germ : Macro.Raw.GermAt package.source package.sourceData package.reader visit.current) :
    Context (input := input) (review := review) depth count prefixLimit renewalLimit sourceDepth sourceCount where
  start := start
  proposal := proposal
  sourcePosition := sourcePosition
  native := package.source
  data := package.sourceData
  reader := package.reader
  basis := package.basis
  visit := visit
  germ := germ
  authority := authority

abbrev Query := Macro.Inquiry.Query package visit

def compilation (query : Query package visit) :
    SourceNativeInquiryCompilationAt package.frame.root visit package.basis.U7 package.basis.calculus
      package.frame.root.toAuthoritativeRoot.source.lawSurface query
      (ULift.up.{1, 0} (package.frame.root.emitted visit.current)) (package.frame.entry visit.current) authority :=
  match query with
  | .internal work => Macro.Inquiry.compilation package visit authority (.internal work)
  | .raw germ =>
      let context := contextAt package visit authority germ
      match Trigger.select context with
      | .enactment ready => .actualAction (generated context ready)
      | _ => Macro.Inquiry.compilation package visit authority (.raw germ)

theorem compilation_audit (query : Query package visit) :
    (compilation package visit authority query).audit = .answered := by
  cases query with
  | internal work => exact Macro.Inquiry.compilation_audit package visit authority (.internal work)
  | raw germ =>
      dsimp only [compilation]
      cases selected : Trigger.select (contextAt package visit authority germ) <;> rfl

theorem compilation_answer (query : Query package visit) :
    HEq (compilation package visit authority query).answerReadout (Macro.Inquiry.sourceAnswer package visit query) := by
  cases query with
  | internal work => exact Macro.Inquiry.compilation_answer package visit authority (.internal work)
  | raw germ =>
      dsimp only [compilation]
      cases selected : Trigger.select (contextAt package visit authority germ) <;> exact HEq.rfl

#print axioms compilation
#print axioms compilation_answer

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Inquiry
