import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.Target
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Faces.Component

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (actual : Accounting.Current input depth count frame.anchor)
  (aligned : frame.cursor visit.current = some actual)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start actual)
  (reader : Macro.Raw.Reader input depth count)

include aligned

def completeFrame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start :=
  Public.Inquiry.installedFrame (targetFrame frame visit actual registered) reader

variable (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current))

/-- The next query grammar is part of the source before the first write.
The inherited target keeps the exact old event, financial write and next. -/
def completeTargetAt (event : ExactTemporalCausalRootEventAt frame.root.toAuthoritativeRoot.toLedgerRoot visit) :
    SourceNativeDebtAdmissionActualActionTargetAt frame.root visit event (frame.entry visit.current) authority := by
  rw [event.eq_generated]
  let core := targetAt frame visit actual aligned registered authority
    (frame.root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit)
  let base := targetFrame frame visit actual registered
  let extra := Public.Inquiry.component base reader
  refine { core with
    targetRoot := (completeFrame frame visit actual registered reader).root
    oldProjection := fun projection => .inherited (core.oldProjection projection)
    oldProjection_injective := ?_
    oldOutcome_heq := ?_
    canonical_targetNextVisit_eq := ?_ }
  · intro left right same
    exact core.oldProjection_injective (SourceNativeProjectionCoface.inherited.inj same)
  · intro projection
    exact ((SourceNativeProjectionLaw.InstallationAt.inheritedCoface base.root.source.base extra).outcome_heq
      (base.root.emitted base.root.toAuthoritativeRoot.toRoot.source.initial) (core.oldProjection projection)).trans
      (core.oldOutcome_heq projection)
  · exact Registered.Macro.Ingress.next_is_the_same_generated_successor
      (completeFrame frame visit actual registered reader).root
      (Source.initialVisit frame.family actual registered) (Source.firstSuccessor frame.family actual registered)

def completeProgram : SourceNativeDebtAdmissionActualActionProgramAt frame.root visit (frame.entry visit.current) authority where
  targetAt := completeTargetAt frame visit actual aligned registered reader authority

#print axioms completeTargetAt
#print axioms completeProgram

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action
