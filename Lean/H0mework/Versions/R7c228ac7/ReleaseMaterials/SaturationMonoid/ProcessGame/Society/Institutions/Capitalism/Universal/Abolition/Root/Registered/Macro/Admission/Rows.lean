import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.ActiveFrame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
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

def generatedRow (visit : SourceNativeTemporalVisitAt (activeFrame frame registered basis).root.toAuthoritativeRoot.toLedgerRoot)
    (entry : OpenResponsibilityAt (N frame registered) (supportAt frame registered visit.current)) :
    ((activeFrame frame registered basis).root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit).GeneratedEntryRowAt entry := by
  let compiler := ledgerCompiler frame registered
  let occurrence := emitted frame registered visit.current
  let selected := sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt
    compiler.writeRowSource compiler.terminalRowSource (compiler.compile occurrence) (compiler.compilePatch occurrence) entry
  have present : selected.isSome = true := by
    let check (packet : Σ image : SourceNativeLedgerEvolutionAt _ occurrence,
        SourceNativeFiniteLedgerPatchAt _ compiler.ExactTransitionAt compiler.writeRowSource compiler.terminalRowSource image) : Bool :=
      (sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt
        compiler.writeRowSource compiler.terminalRowSource packet.1 packet.2 entry).isSome
    change check (sourcePacket frame registered occurrence) = true
    dsimp only [occurrence, sourcePacket]
    split <;> rfl
  exact SourceNativeTemporalVisitGeneratedEvolutionAt.GeneratedEntryRowAt.ofSourceRow (selected.get present)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
