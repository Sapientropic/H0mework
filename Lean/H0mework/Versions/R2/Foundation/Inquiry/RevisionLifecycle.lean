import H0mework.Versions.R2.Foundation.Inquiry.SemanticRevision
import H0mework.Versions.R2.Foundation.Authority.EntryDisposition

/-!
# First-write lifecycle of a typed semantic world revision

A non-conservative U8 revision has generated two exact live rows in the
revised root's initial finite patch: the migrated old causal obligation and a
new-only semantic incidence.  This kernel advances both through the revised
root's literal first write.

Each initial authority is generated from its exact patch row.  Each successor
uses the same compiler-generated first target, and each target authority is
derived from the predecessor authority and its generated disposition.  No
target-side row can create a fresh admission.

This closes first-write lifecycle continuity.  It does not claim that the old
expressibility obstruction has been independently settled.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace TypedSemanticWorldNetworkU8Lifecycle

open TypedSemanticWorldNetworkU8

universe u

/-- Literal revised-ledger entry corresponding to the old causal obligation. -/
def revisedOldEntryAtRoot
    {N : WorldRelationNetwork.{u}}
    {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N}
    {oldTheory : TheoryState N}
    {support : N.Support}
    {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : ObstructionGeneratedMinimalCoface.RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}
    (generated : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :
    OpenResponsibilityAt generated.NewN
      (generated.newRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (generated.newRoot.toLedgerRoot.emitted
          generated.newRoot.toRoot.source.initial)) :=
  generated.oldTargetOpenLedger.forward rooted.oldTargetEntry

/-- Literal revised-ledger entry generated as the new semantic incidence. -/
def revisedNewOnlyEntryAtRoot
    {N : WorldRelationNetwork.{u}}
    {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N}
    {oldTheory : TheoryState N}
    {support : N.Support}
    {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : ObstructionGeneratedMinimalCoface.RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}
    (generated : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :
    OpenResponsibilityAt generated.NewN
      (generated.newRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (generated.newRoot.toLedgerRoot.emitted
          generated.newRoot.toRoot.source.initial)) :=
  generated.newOnlyEntry

variable
    {N : WorldRelationNetwork.{u}}
    {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N}
    {oldTheory : TheoryState N}
    {support : N.Support}
    {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : ObstructionGeneratedMinimalCoface.RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}

/-- Initial authority of the migrated old responsibility is the exact row in
the revised root's source-generated initial patch.  The public mouth consumes
the source compiler, not a bare generated revision record. -/
def oldInitialAuthority
    (source : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      source.generate.newLivingRoot
      (.finite source.generate.newRoot.toRoot.initialVisit)
      (revisedOldEntryAtRoot source.generate) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    source.generate.newLivingRoot (revisedOldEntryAtRoot source.generate)
    source.generate.oldEntryRow

/-- The migrated old responsibility advances through the literal first write
already carried by the typed revision. -/
def oldFirstWriteSuccessor
    (source : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted) :
    CausalEntrySuccessorAt
      source.generate.newRoot.toLedgerRoot
      (.finite source.generate.newRoot.toRoot.initialVisit)
      (revisedOldEntryAtRoot source.generate) :=
  CausalEntrySuccessorAt.ofNonterminal source.generate.firstWrite.next_eq

/-- Target authority of the migrated old responsibility is derived from its
initial row and that same first-write successor. -/
def oldFirstWriteTargetAuthority
    (source : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      source.generate.newLivingRoot
      (oldFirstWriteSuccessor source).targetVisit
      (oldFirstWriteSuccessor source).targetEntry :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.next
    (oldInitialAuthority source) (oldFirstWriteSuccessor source).next_eq

/-- Initial authority of the genuinely new incidence is the other exact row
in the same revised-root initial patch and is likewise source-indexed. -/
def newInitialAuthority
    (source : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      source.generate.newLivingRoot
      (.finite source.generate.newRoot.toRoot.initialVisit)
      (revisedNewOnlyEntryAtRoot source.generate) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    source.generate.newLivingRoot (revisedNewOnlyEntryAtRoot source.generate)
    source.generate.newOnlyEntryRow

/-- The new-only incidence advances through the very same first write. -/
def newFirstWriteSuccessor
    (source : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted) :
    CausalEntrySuccessorAt
      source.generate.newRoot.toLedgerRoot
      (.finite source.generate.newRoot.toRoot.initialVisit)
      (revisedNewOnlyEntryAtRoot source.generate) :=
  CausalEntrySuccessorAt.ofNonterminal source.generate.firstWrite.next_eq

/-- Target authority of the new-only incidence is likewise a direct root
readout, not a field in a parallel lifecycle bundle. -/
def newFirstWriteTargetAuthority
    (source : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      source.generate.newLivingRoot
      (newFirstWriteSuccessor source).targetVisit
      (newFirstWriteSuccessor source).targetEntry :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.next
    (newInitialAuthority source) (newFirstWriteSuccessor source).next_eq

end TypedSemanticWorldNetworkU8Lifecycle
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
