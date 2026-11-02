import H0mework.Versions.R2.Foundation.Inquiry.SemanticRevision
import H0mework.Versions.R2.Foundation.Runtime.AnswerNext

/-! A query coface changes the old authority epoch while preserving its
literal lower ledger, emitter, row and causal successor.  A richer revision
then keeps its already generated world and complete first write unchanged. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Transport.ProjectionCofaceRevision

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface ConstructiveRoot.TypedSemanticWorldNetworkU8

universe u

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
  {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
  {support : N.Support} {obstruction : N.ObstructionAt support}
  {failure : ActualExpressibilityFailure oldTheory obstruction}
  (component : SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource)
  (before : RootedActualExpressibilityFailureAt root.toAuthoritativeRoot visit U7 failure)
  (after : RootedActualExpressibilityFailureAt
    (root.withProjectionCoface component).toAuthoritativeRoot visit U7 failure)
  (sameRow : after.rootEntry = before.rootEntry)
  (sameSuccessor : HEq after.oldSuccessor before.oldSuccessor)

def generated (revision : GeneratedTypedSemanticWorldNetworkRevisionAt before) :
    GeneratedTypedSemanticWorldNetworkRevisionAt after where
  NewN := revision.NewN
  translation := revision.translation
  NewV := revision.NewV
  newLivingRoot := revision.newLivingRoot
  new_support_restricts := by
    rcases before with ⟨calculus, event, event_eq, audit, support_eq, entry, entry_eq, disposition, authority, successor⟩
    rcases after with ⟨calculus', event', event_eq', audit', support_eq', entry', entry_eq', disposition', authority', successor'⟩
    change entry' = entry at sameRow
    cases sameRow
    have successor_eq : successor' = successor := eq_of_heq sameSuccessor
    cases successor_eq
    exact revision.new_support_restricts
  oldTargetOpenLedger := by
    rcases before with ⟨calculus, event, event_eq, audit, support_eq, entry, entry_eq, disposition, authority, successor⟩
    rcases after with ⟨calculus', event', event_eq', audit', support_eq', entry', entry_eq', disposition', authority', successor'⟩
    change entry' = entry at sameRow
    cases sameRow
    have successor_eq : successor' = successor := eq_of_heq sameSuccessor
    cases successor_eq
    exact revision.oldTargetOpenLedger
  oldTargetOpenClaim_commutes := by
    rcases before with ⟨calculus, event, event_eq, audit, support_eq, entry, entry_eq, disposition, authority, successor⟩
    rcases after with ⟨calculus', event', event_eq', audit', support_eq', entry', entry_eq', disposition', authority', successor'⟩
    change entry' = entry at sameRow
    cases sameRow
    have successor_eq : successor' = successor := eq_of_heq sameSuccessor
    cases successor_eq
    exact revision.oldTargetOpenClaim_commutes
  oldTargetOpenProgressBudget_not_refilled := by
    rcases before with ⟨calculus, event, event_eq, audit, support_eq, entry, entry_eq, disposition, authority, successor⟩
    rcases after with ⟨calculus', event', event_eq', audit', support_eq', entry', entry_eq', disposition', authority', successor'⟩
    change entry' = entry at sameRow
    cases sameRow
    have successor_eq : successor' = successor := eq_of_heq sameSuccessor
    cases successor_eq
    exact revision.oldTargetOpenProgressBudget_not_refilled
  occurrencePresentation := by
    rcases before with ⟨calculus, event, event_eq, audit, support_eq, entry, entry_eq, disposition, authority, successor⟩
    rcases after with ⟨calculus', event', event_eq', audit', support_eq', entry', entry_eq', disposition', authority', successor'⟩
    change entry' = entry at sameRow
    cases sameRow
    have successor_eq : successor' = successor := eq_of_heq sameSuccessor
    cases successor_eq
    exact revision.occurrencePresentation
  occurrence_commutes := by
    rcases before with ⟨calculus, event, event_eq, audit, support_eq, entry, entry_eq, disposition, authority, successor⟩
    rcases after with ⟨calculus', event', event_eq', audit', support_eq', entry', entry_eq', disposition', authority', successor'⟩
    change entry' = entry at sameRow
    cases sameRow
    have successor_eq : successor' = successor := eq_of_heq sameSuccessor
    cases successor_eq
    exact revision.occurrence_commutes
  firstWrite := revision.firstWrite
  newOnlyEntry := revision.newOnlyEntry
  newOnlyProgressBudget_eq_zero := revision.newOnlyProgressBudget_eq_zero
  revisedClaimHolds := revision.revisedClaimHolds
  semanticChange := revision.semanticChange
  revisedClaim_hasNoOldPreimage := revision.revisedClaim_hasNoOldPreimage
  newOnlyIncidence_hasNoOldPreimage := revision.newOnlyIncidence_hasNoOldPreimage
  oldEntryRows := by
    rcases before with ⟨calculus, event, event_eq, audit, support_eq, entry, entry_eq, disposition, authority, successor⟩
    rcases after with ⟨calculus', event', event_eq', audit', support_eq', entry', entry_eq', disposition', authority', successor'⟩
    change entry' = entry at sameRow
    cases sameRow
    have successor_eq : successor' = successor := eq_of_heq sameSuccessor
    cases successor_eq
    exact revision.oldEntryRows
  newOnlyEntry_hasNoOldPreimage := by
    rcases before with ⟨calculus, event, event_eq, audit, support_eq, entry, entry_eq, disposition, authority, successor⟩
    rcases after with ⟨calculus', event', event_eq', audit', support_eq', entry', entry_eq', disposition', authority', successor'⟩
    change entry' = entry at sameRow
    cases sameRow
    have successor_eq : successor' = successor := eq_of_heq sameSuccessor
    cases successor_eq
    exact revision.newOnlyEntry_hasNoOldPreimage
  newOnlyEntryRow := revision.newOnlyEntryRow

theorem newLivingRoot_preserved (revision : GeneratedTypedSemanticWorldNetworkRevisionAt before) :
    (generated component before after sameRow sameSuccessor revision).newLivingRoot =
      revision.newLivingRoot := rfl

theorem firstWrite_preserved (revision : GeneratedTypedSemanticWorldNetworkRevisionAt before) :
    (generated component before after sameRow sameSuccessor revision).firstWrite =
      revision.firstWrite := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Transport.ProjectionCofaceRevision
