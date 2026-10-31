import H0mework.Foundation.Semantics.TheoryEvolution
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Settlement.GeneratedSettlement

/-!
# Semantic law disposition and actual claim-authority lifecycle

A semantic law disposition and the authority lifecycle of an inherited live
claim are different coordinates of one revision occurrence.  This module
joins them without allowing the semantic labels `preserved`, `weakened`, or
`replaced` to close an active responsibility.

The migration compiler reuses the exact occurrence emitted by an existing
`LawRevisionDispositionSourceAt`.  At that same occurrence it must compile an
actual responsibility edge whose native classifier produces a
`SupersededRolloverAt`.  The inherited claim therefore remains live through
`SupersededRolloverAt.open`; no second occurrence, claim registry, ledger, or
retirement schedule is introduced.

A later retirement is indexed by a `ResidualConsumerAt` of that exact live
successor.  It can be generated only after the downstream edge carries an
actual `FulfilledSettlementAt`, and its closed readout is definitionally
`FulfilledSettlementAt.closed`.  Nothing in this file preconstructs such a
later event or asserts that one will occur.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Theory
namespace Revision

open ResponsibilityLifecycle LivingLawEvolution Settlement

universe u

variable {N : WorldRelationNetwork.{u}}
variable {oldTheory : TheoryState N}
variable {revisedInventory : LawInventory N}
variable {relation : LawRevisionRelation oldTheory.inventory revisedInventory}
variable {dispositionSource : LawRevisionDispositionSourceAt relation}

variable {V : Vocabulary.{u}}
variable {P : NativeResponsibilityProcess V}
variable {firstWriteSource : ResponsibilityState V}

/-! ## Existing-settlement transporters -/

/-- A closed exact settlement occupies its generated target slot with the
same terminal archive. -/
theorem closedSettlement_target_terminal
    {source : ResponsibilityState V}
    {settlement : ExactSettlementEdge P source}
    (closed : ExactSettlementEdge.ClosedSettlementAt settlement) :
    settlement.edge.target.slots[settlement.slot.val]? =
      some (.terminal closed.archive) := by
  unfold ExactSettlementEdge.edge
  rw [NativeResponsibilityProcess.cross_target_slot]
  change some settlement.disposition.targetSlot =
    some (.terminal closed.archive)
  rw [closed.targetSlot_eq]

/-- A fulfilled exact settlement has the exact lifecycle classification used
by final claim retirement. -/
theorem fulfilledSettlement_classification
    {source : ResponsibilityState V}
    {settlement : ExactSettlementEdge P source}
    (fulfilled : ExactSettlementEdge.FulfilledSettlementAt settlement) :
    settlement.classification = ExactSettlementEdge.Class.fulfilled := by
  unfold ExactSettlementEdge.classification
  rw [fulfilled.disposition_eq]

/-! ## Same-occurrence first-write compiler -/

/--
A source-owned bridge from one exact generated law-disposition occurrence to
the actual responsibility edge used by the revision first write.

`compileFirstWrite` returns an existing `ExactSettlementEdge`, so its source
slot is already live and its boundary event is owned by `P`.  `compileRollover`
then certifies what that fixed process actually classified; it does not accept
a caller-selected successor or target slot.
-/
structure SourceOwnedInheritedClaimMigrationCompilerAt
    (dispositionSource : LawRevisionDispositionSourceAt relation)
    (P : NativeResponsibilityProcess V)
    (firstWriteSource : ResponsibilityState V) : Type (u + 1) where
  compileFirstWrite : (law : oldTheory.inventory.Law) →
    dispositionSource.OccurrenceAt law →
      ExactSettlementEdge P firstWriteSource
  compileRollover : (law : oldTheory.inventory.Law) →
    (occurrence : dispositionSource.OccurrenceAt law) →
      ExactSettlementEdge.SupersededRolloverAt
        (compileFirstWrite law occurrence)

namespace SourceOwnedInheritedClaimMigrationCompilerAt

variable
  (compiler : SourceOwnedInheritedClaimMigrationCompilerAt
    dispositionSource P firstWriteSource)

/-- The exact occurrence is the existing disposition source's emitted law
occurrence; the migration compiler does not mint another one. -/
def exactOccurrence
    (_compiler : SourceOwnedInheritedClaimMigrationCompilerAt
      dispositionSource P firstWriteSource)
    (law : oldTheory.inventory.Law) :
    dispositionSource.OccurrenceAt law :=
  dispositionSource.emit law

/-- Semantic law disposition compiled at the exact shared occurrence. -/
def semanticDispositionAt
    (_compiler : SourceOwnedInheritedClaimMigrationCompilerAt
      dispositionSource P firstWriteSource)
    (law : oldTheory.inventory.Law)
    (occurrence : dispositionSource.OccurrenceAt law) :
    LawRevisionDispositionAt relation law :=
  dispositionSource.compileDisposition law occurrence

/-- Existing generated semantic-disposition token for the same law. -/
def generatedLawDisposition
    (_compiler : SourceOwnedInheritedClaimMigrationCompilerAt
      dispositionSource P firstWriteSource)
    (law : oldTheory.inventory.Law) :
    GeneratedLawRevisionDispositionAt dispositionSource law :=
  dispositionSource.generated law

/-- Actual first-write responsibility edge compiled at one exact occurrence. -/
def firstWriteAt
    (law : oldTheory.inventory.Law)
    (occurrence : dispositionSource.OccurrenceAt law) :
    ExactSettlementEdge P firstWriteSource :=
  compiler.compileFirstWrite law occurrence

/-- Actual source-classified supersession at one exact occurrence. -/
def rolloverAt
    (law : oldTheory.inventory.Law)
    (occurrence : dispositionSource.OccurrenceAt law) :
    ExactSettlementEdge.SupersededRolloverAt
      (compiler.firstWriteAt law occurrence) :=
  compiler.compileRollover law occurrence

/-- Every purported occurrence is the sole source-emitted occurrence. -/
theorem occurrence_eq_exactOccurrence
    (law : oldTheory.inventory.Law)
    (occurrence : dispositionSource.OccurrenceAt law) :
    occurrence = compiler.exactOccurrence law :=
  dispositionSource.event_eq_emit law occurrence

/-- Deleting or replacing the generated first-write event by another value is
impossible: every occurrence compiles to the same exact edge. -/
theorem firstWriteAt_eq_generated
    (law : oldTheory.inventory.Law)
    (occurrence : dispositionSource.OccurrenceAt law) :
    compiler.firstWriteAt law occurrence =
      compiler.firstWriteAt law (compiler.exactOccurrence law) := by
  rw [compiler.occurrence_eq_exactOccurrence law occurrence]

/-- Semantic and lifecycle compilation literally consume the same emitted
occurrence. -/
theorem semanticDispositionAt_eq_generated
    (law : oldTheory.inventory.Law)
    (occurrence : dispositionSource.OccurrenceAt law) :
    compiler.semanticDispositionAt law occurrence =
      compiler.semanticDispositionAt law (compiler.exactOccurrence law) := by
  rw [compiler.occurrence_eq_exactOccurrence law occurrence]

end SourceOwnedInheritedClaimMigrationCompilerAt

/-! ## Generated inherited-claim migration -/

/--
Zero-field token generated from one exact old-law occurrence.  The semantic
disposition, first-write edge, and supersession receipt are recomputed from
the indexed source compiler; none is accepted as a field of this token.
-/
inductive SourceGeneratedInheritedClaimMigrationAt
    (compiler : SourceOwnedInheritedClaimMigrationCompilerAt
      dispositionSource P firstWriteSource)
    (law : oldTheory.inventory.Law) : Type u where
  | private generated

namespace SourceGeneratedInheritedClaimMigrationAt

/-- Sole migration producer for one emitted law occurrence. -/
def generate
    (compiler : SourceOwnedInheritedClaimMigrationCompilerAt
      dispositionSource P firstWriteSource)
    (law : oldTheory.inventory.Law) :
    SourceGeneratedInheritedClaimMigrationAt compiler law :=
  .generated

variable
  {compiler : SourceOwnedInheritedClaimMigrationCompilerAt
    dispositionSource P firstWriteSource}
  {law : oldTheory.inventory.Law}
  (migration : SourceGeneratedInheritedClaimMigrationAt compiler law)

theorem eq_generate : migration = generate compiler law := by
  cases migration
  rfl

/-- Exact source occurrence jointly used by the semantic disposition and the
actual first write. -/
def exactOccurrence : dispositionSource.OccurrenceAt law := by
  cases migration
  exact compiler.exactOccurrence law

/-- Existing generated semantic-disposition token at this occurrence. -/
def generatedLawDisposition :
    GeneratedLawRevisionDispositionAt dispositionSource law := by
  cases migration
  exact compiler.generatedLawDisposition law

/-- Semantic classification remains a `LawRevisionDispositionAt`; it is not
an active-claim disposition. -/
def semanticDisposition : LawRevisionDispositionAt relation law :=
  migration.generatedLawDisposition.disposition

theorem semanticDisposition_eq_compiledAt_exactOccurrence :
    migration.semanticDisposition =
      compiler.semanticDispositionAt law migration.exactOccurrence := by
  cases migration
  rfl

/-- The semantic coordinate retains the exact three-way revision grammar; no
lifecycle status is inserted into or inferred from this classification. -/
theorem semanticDisposition_exhaustive :
    (∃ (revisedLaw : revisedInventory.Law)
        (receipt : relation.PreservedAt law revisedLaw),
      migration.semanticDisposition =
        LawRevisionDispositionAt.preserved revisedLaw receipt) ∨
    (∃ (revisedLaw : revisedInventory.Law)
        (receipt : relation.WeakenedAt law revisedLaw),
      migration.semanticDisposition =
        LawRevisionDispositionAt.weakened revisedLaw receipt) ∨
    (∃ (revisedLaw : revisedInventory.Law)
        (receipt : relation.ReplacedAt law revisedLaw),
      migration.semanticDisposition =
        LawRevisionDispositionAt.replaced revisedLaw receipt) := by
  cases dispositionEq : migration.semanticDisposition with
  | preserved revisedLaw receipt =>
      exact Or.inl ⟨revisedLaw, receipt, rfl⟩
  | weakened revisedLaw receipt =>
      exact Or.inr (Or.inl ⟨revisedLaw, receipt, rfl⟩)
  | replaced revisedLaw receipt =>
      exact Or.inr (Or.inr ⟨revisedLaw, receipt, rfl⟩)

/-- Actual first-write responsibility edge generated at the same exact source
occurrence as the semantic disposition. -/
def firstWriteSettlement : ExactSettlementEdge P firstWriteSource := by
  cases migration
  exact compiler.firstWriteAt law (compiler.exactOccurrence law)

/-- Actual native supersession generated at that first-write edge. -/
def firstWriteRollover :
    ExactSettlementEdge.SupersededRolloverAt
      migration.firstWriteSettlement := by
  cases migration
  exact compiler.rolloverAt law (compiler.exactOccurrence law)

/-- The inherited active claim is the obligation already live at the exact
first-write slot. -/
def inheritedClaim : AdmittedObligation V :=
  migration.firstWriteSettlement.obligation

/-- Exact source-state liveness of the inherited claim. -/
theorem inheritedClaim_live_at_firstWriteSource :
    firstWriteSource.LiveAt migration.firstWriteSettlement.slot.val := by
  refine ⟨migration.inheritedClaim, ?_⟩
  calc
    firstWriteSource.slots[migration.firstWriteSettlement.slot.val]? =
        some (firstWriteSource.slots.get
          migration.firstWriteSettlement.slot) :=
      List.getElem?_eq_getElem migration.firstWriteSettlement.slot.isLt
    _ = some (.live migration.inheritedClaim) :=
      congrArg some migration.firstWriteSettlement.present

/-- Claim migration is definitionally the existing supersession-open
producer, never a semantic disposition readout. -/
def liveSuccessor : ExactSettlementEdge.LiveResidualAt
    migration.firstWriteSettlement :=
  migration.firstWriteRollover.open

/-- The migrated live successor generated by the first write. -/
def successorClaim : AdmittedObligation V :=
  migration.liveSuccessor.obligation

theorem successorClaim_eq_rollover_successor :
    migration.successorClaim =
      migration.firstWriteRollover.receipt.successor :=
  rfl

/-- Supersession preserves the inherited claim lineage. -/
theorem successorClaim_lineage_eq :
    migration.successorClaim.lineage = migration.inheritedClaim.lineage := by
  change migration.firstWriteRollover.receipt.successor.lineage =
    migration.firstWriteSettlement.obligation.lineage
  exact migration.firstWriteRollover.receipt.successor_lineage

/-- The actual first-write target keeps the generated successor live. -/
theorem firstWrite_target_live :
    migration.firstWriteSettlement.edge.target.slots[
        migration.firstWriteSettlement.slot.val]? =
      some (.live migration.successorClaim) :=
  migration.liveSuccessor.target_live

/-- Exact lifecycle classification of the first write. -/
theorem firstWrite_classification_eq_superseded :
    migration.firstWriteSettlement.classification =
      ExactSettlementEdge.Class.supersededRollover := by
  unfold ExactSettlementEdge.classification
  rw [migration.firstWriteRollover.disposition_eq]

/-- A superseded obligation remains live and therefore is not closed. -/
theorem firstWrite_not_closed :
    ¬ Nonempty (ExactSettlementEdge.ClosedSettlementAt
      migration.firstWriteSettlement) :=
  migration.firstWriteSettlement.live_not_closed ⟨migration.liveSuccessor⟩

/-- Semantic replacement is not claim retirement.  Even in the literal
`replaced` branch, the actual first write is the same live supersession. -/
def SemanticReplacementAt : Prop :=
  ∃ (revisedLaw : revisedInventory.Law)
      (receipt : relation.ReplacedAt law revisedLaw),
    migration.semanticDisposition =
      LawRevisionDispositionAt.replaced revisedLaw receipt

theorem semanticReplacement_retains_live_claim
    (_replacement : migration.SemanticReplacementAt) :
    Nonempty (ExactSettlementEdge.LiveResidualAt
        migration.firstWriteSettlement) ∧
      ¬ Nonempty (ExactSettlementEdge.ClosedSettlementAt
        migration.firstWriteSettlement) :=
  ⟨⟨migration.liveSuccessor⟩, migration.firstWrite_not_closed⟩

/-! ## Sparse readout omission has no lifecycle authority -/

/-- Observer-only omission from an arbitrary sparse readout.  This predicate
is not stored by the migration and cannot mutate the responsibility state. -/
def SparseReadoutOmissionAt
    (readout : List (AdmittedObligation V)) : Prop :=
  migration.inheritedClaim ∉ readout

/-- Sparse omission leaves both exact source liveness and the actual migrated
successor intact. -/
theorem sparseOmission_preserves_actual_liveness
    {readout : List (AdmittedObligation V)}
    (_omission : migration.SparseReadoutOmissionAt readout) :
    firstWriteSource.LiveAt migration.firstWriteSettlement.slot.val ∧
      Nonempty (ExactSettlementEdge.LiveResidualAt
        migration.firstWriteSettlement) :=
  ⟨migration.inheritedClaim_live_at_firstWriteSource,
    ⟨migration.liveSuccessor⟩⟩

/-- In particular, sparse omission cannot serve as a retirement receipt. -/
theorem sparseOmission_is_not_firstWriteRetirement
    {readout : List (AdmittedObligation V)}
    (_omission : migration.SparseReadoutOmissionAt readout) :
    ¬ Nonempty (ExactSettlementEdge.ClosedSettlementAt
      migration.firstWriteSettlement) :=
  migration.firstWrite_not_closed

/-! ## Later actual fulfillment -/

/-- Exact downstream settlement induced by an actual consumer of the migrated
live successor.  Its source state is definitionally the first-write target. -/
def laterSettlement
    (consumer : ExactSettlementEdge.ResidualConsumerAt
      migration.liveSuccessor) :
    ExactSettlementEdge P migration.firstWriteSettlement.edge.target where
  slot := migration.firstWriteSettlement.targetSlot
  obligation := migration.successorClaim
  present := migration.liveSuccessor.target_present
  event := consumer.event

/-- The downstream exact-settlement edge is the existing residual-consumer
edge, not a sibling future path. -/
theorem laterSettlement_edge_eq_consumerEdge
    (consumer : ExactSettlementEdge.ResidualConsumerAt
      migration.liveSuccessor) :
    (migration.laterSettlement consumer).edge = consumer.edge :=
  rfl

end SourceGeneratedInheritedClaimMigrationAt

/-! ## Event-indexed final retirement -/

/--
Zero-field final-retirement token.  It can be generated only after an exact
downstream consumer event has produced `FulfilledSettlementAt` on the
migration's live target.  No existential consumer, schedule, or completed
future is stored here.
-/
inductive SourceGeneratedInheritedClaimRetirementAt
    {compiler : SourceOwnedInheritedClaimMigrationCompilerAt
      dispositionSource P firstWriteSource}
    {law : oldTheory.inventory.Law}
    (migration : SourceGeneratedInheritedClaimMigrationAt compiler law)
    (consumer : ExactSettlementEdge.ResidualConsumerAt
      migration.liveSuccessor)
    (fulfilled : ExactSettlementEdge.FulfilledSettlementAt
      (migration.laterSettlement consumer)) : Type u where
  | private generated

namespace SourceGeneratedInheritedClaimRetirementAt

/-- Sole retirement producer; the exact later fulfillment is an index, not a
preinstalled future field. -/
def generate
    {compiler : SourceOwnedInheritedClaimMigrationCompilerAt
      dispositionSource P firstWriteSource}
    {law : oldTheory.inventory.Law}
    (migration : SourceGeneratedInheritedClaimMigrationAt compiler law)
    (consumer : ExactSettlementEdge.ResidualConsumerAt
      migration.liveSuccessor)
    (fulfilled : ExactSettlementEdge.FulfilledSettlementAt
      (migration.laterSettlement consumer)) :
    SourceGeneratedInheritedClaimRetirementAt
      migration consumer fulfilled :=
  .generated

variable
  {compiler : SourceOwnedInheritedClaimMigrationCompilerAt
    dispositionSource P firstWriteSource}
  {law : oldTheory.inventory.Law}
  {migration : SourceGeneratedInheritedClaimMigrationAt compiler law}
  {consumer : ExactSettlementEdge.ResidualConsumerAt
    migration.liveSuccessor}
  {fulfilled : ExactSettlementEdge.FulfilledSettlementAt
    (migration.laterSettlement consumer)}
  (retirement : SourceGeneratedInheritedClaimRetirementAt
    migration consumer fulfilled)

theorem eq_generate : retirement = generate migration consumer fulfilled := by
  cases retirement
  rfl

/-- Exact actual fulfillment required by this retirement occurrence. -/
def actualFulfillment : ExactSettlementEdge.FulfilledSettlementAt
    (migration.laterSettlement consumer) := by
  cases retirement
  exact fulfilled

/-- Final closure is read only through the existing fulfilled-settlement
producer. -/
def closed : ExactSettlementEdge.ClosedSettlementAt
    (migration.laterSettlement consumer) :=
  retirement.actualFulfillment.closed

theorem closed_eq_actualFulfillment_closed :
    retirement.closed = retirement.actualFulfillment.closed :=
  rfl

/-- Exact lifecycle classification of the later retirement event. -/
theorem later_classification_eq_fulfilled
    (actualRetirement : SourceGeneratedInheritedClaimRetirementAt
      migration consumer fulfilled) :
    (migration.laterSettlement consumer).classification =
      ExactSettlementEdge.Class.fulfilled :=
  fulfilledSettlement_classification (actualRetirement.actualFulfillment)

/-- The revised-root later edge closes the same stable slot which held the
first-write successor. -/
theorem later_target_closed :
    (migration.laterSettlement consumer).edge.target.slots[
        (migration.laterSettlement consumer).slot.val]? =
      some (.terminal retirement.closed.archive) :=
  closedSettlement_target_terminal retirement.closed

/-- Actual final disappearance follows from the later fulfilled edge; it is
not inferred from semantic replacement or sparse omission. -/
theorem later_actual_disappearance
    (actualRetirement : SourceGeneratedInheritedClaimRetirementAt
      migration consumer fulfilled) :
    ResponsibilityState.DisappearsAt
      migration.firstWriteSettlement.edge.target
      (migration.laterSettlement consumer).edge.target
      (migration.laterSettlement consumer).slot.val := by
  constructor
  · refine ⟨(migration.laterSettlement consumer).obligation, ?_⟩
    calc
      migration.firstWriteSettlement.edge.target.slots[
          (migration.laterSettlement consumer).slot.val]? =
          some (migration.firstWriteSettlement.edge.target.slots.get
            (migration.laterSettlement consumer).slot) :=
        List.getElem?_eq_getElem
          (migration.laterSettlement consumer).slot.isLt
      _ = some (.live (migration.laterSettlement consumer).obligation) :=
        congrArg some (migration.laterSettlement consumer).present
  · rintro ⟨targetObligation, targetLive⟩
    rw [later_target_closed actualRetirement] at targetLive
    cases targetLive

end SourceGeneratedInheritedClaimRetirementAt

end Revision
end Theory
end Society
end ProcessGame
end SaturationMonoid
