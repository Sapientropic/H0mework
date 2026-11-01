import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Theory.SourceGeneratedContributionCapacityRepresentationPairIntentTheory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Compiler.SourceGeneratedLossAllocationRestructuring

/-!
# Pair-intent target compiler

The target has exactly two structural currents.  `false` is the conservative
ingress from revised-Q current `1`; its sole native write goes to `true`.
`true` is the generated representation-intent occurrence and continues by an
ordinary self-loop.  Both currents use the same existing revised-Q target
support and complete open ledger.

The first finite patch explicitly generates only the existing target-
obstruction row and carries every other row through the identity remainder.
Thus the sequential-action source entry receives exact row authority without
creating a responsibility, claim-bearing ledger row, second ledger, or
parallel successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedLossAllocationCompiler
open M14SourceGeneratedLossAllocationRestructuring
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreaking
open M14SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference
open M14SourceGeneratedContributionCapacityFinitePrefixOperationalCode
open M14SourceInstalledContributionCapacityFinitePrefixRepresentation
open M14SourceGeneratedContributionCapacityRepresentationIntentActionMaterial
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory
open M14SourceGeneratedPostSettlementObserverSubmissionU8

abbrev RepresentationIntentNAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  RepresentationClaimNAt oldVisit sourceIndex boundary

def representationIntentSupportAtCurrent
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) (_current : Bool) :
    (RepresentationIntentNAt oldVisit sourceIndex boundary).Support :=
  representationIntentSupportAt oldVisit sourceIndex boundary

def representationIntentNativeTarget : Bool → Bool
  | false => true
  | true => true

def representationIntentVocabulary
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConstructiveRoot.Vocabulary where
  Current := Bool
  Anchor := (RepresentationIntentNAt oldVisit sourceIndex boundary).Anchor
  Incidence := (RepresentationIntentNAt oldVisit sourceIndex boundary).Incidence
  Lineage := (RepresentationIntentNAt oldVisit sourceIndex boundary).Lineage
  anchorAt := fun current =>
    (RepresentationIntentNAt oldVisit sourceIndex boundary).anchorAt
      (representationIntentSupportAtCurrent oldVisit sourceIndex boundary
        current)
  incidenceAt := fun current =>
    (RepresentationIntentNAt oldVisit sourceIndex boundary).incidenceAt
      (representationIntentSupportAtCurrent oldVisit sourceIndex boundary
        current)
  lineageAt := fun current =>
    (RepresentationIntentNAt oldVisit sourceIndex boundary).lineageAt
      (representationIntentSupportAtCurrent oldVisit sourceIndex boundary
        current)
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => representationIntentNativeTarget current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev RepresentationIntentVAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  representationIntentVocabulary oldVisit sourceIndex boundary

/-- Low-universe occurrence seal.  The exact P→Q action material and collision
proof stay in the sequential receipt; the ledger compiler needs only its
support and the existing loss-allocation lifecycle material. -/
structure SourceGeneratedRepresentationIntentEventAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (current : Bool)
    (support : (RepresentationIntentNAt oldVisit sourceIndex boundary).Support) :
    Type where
  private mk ::
  supportExact : PLift
    (support = representationIntentSupportAtCurrent oldVisit sourceIndex
      boundary current)
  materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness
  materialExact : materialWitness =
    exactSourceGeneratedLossAllocationMaterialWitness

def representationIntentEventLaw
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeEventAlgebra
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      (RepresentationIntentVAt oldVisit sourceIndex boundary) where
  EventAt := SourceGeneratedRepresentationIntentEventAt oldVisit sourceIndex
    boundary
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun {_} {support} _ =>
    OpenResponsibilityAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by
    intro current support event
    cases event.supportExact.down
    rfl
  incidence_commutes := by
    intro current support event
    cases event.supportExact.down
    rfl
  lineage_commutes := by
    intro current support event
    cases event.supportExact.down
    rfl

def representationIntentSource
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeSource
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      (RepresentationIntentVAt oldVisit sourceIndex boundary) where
  initial := false
  law := representationIntentEventLaw oldVisit sourceIndex boundary

def representationIntentEmitted
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (current : Bool) :
    (representationIntentSource oldVisit sourceIndex boundary
      ).toRootSource.actual.OccurrenceAt current :=
  ⟨representationIntentSupportAtCurrent oldVisit sourceIndex boundary current,
    ⟨PLift.up rfl, exactSourceGeneratedLossAllocationMaterialWitness, rfl⟩⟩

theorem representationIntentOccurrence_eq_emitted
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) :
    occurrence = representationIntentEmitted oldVisit sourceIndex boundary
      current := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  cases event.materialExact
  cases event
  rfl

abbrev RepresentationIntentLedgerAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    CompleteLiveLedgerAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary) :=
  ⟨representationIntentSupportAt oldVisit sourceIndex boundary⟩

/-- The one explicit first-patch row is exactly the existing revised-Q target
obstruction entry, re-read in the claim-extended world. -/
def representationIntentGeneratedEntryAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (RepresentationIntentLedgerAt oldVisit sourceIndex boundary).Entry :=
  let entry :=
    M9ProofCarryingRenewalU8RevisedLedger.revisedTargetObstructionAt
      (oldRootVisitAt oldVisit sourceIndex boundary)
  ⟨entry.1, entry.2⟩

def representationIntentEntryAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Fin 3 → (RepresentationIntentLedgerAt oldVisit sourceIndex boundary).Entry :=
  fun index =>
    let entry := lossAllocationFirstTargetEntryAt
      (rootedFailureAt oldVisit sourceIndex boundary) index
    ⟨entry.1, entry.2⟩

def representationIntentEntryIndex
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (RepresentationIntentLedgerAt oldVisit sourceIndex boundary).Entry →
      Fin 3 :=
  fun entry =>
    lossAllocationTargetEntryIndex
      (rootedFailureAt oldVisit sourceIndex boundary) ⟨entry.1, entry.2⟩

theorem representationIntentEntryAt_index
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (entry : (RepresentationIntentLedgerAt oldVisit sourceIndex boundary).Entry) :
    representationIntentEntryAt oldVisit sourceIndex boundary
        (representationIntentEntryIndex oldVisit sourceIndex boundary entry) =
      entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  exact lossAllocationFirstTargetEntryAt_index
    (rootedFailureAt oldVisit sourceIndex boundary) ⟨responsibility, isOpen⟩

@[simp] theorem representationIntentEntryAt_two_generated
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    representationIntentEntryAt oldVisit sourceIndex boundary
        ⟨2, by decide⟩ =
      representationIntentGeneratedEntryAt oldVisit sourceIndex boundary :=
  rfl

def RepresentationIntentExactTransitionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    {current : Bool} →
    (occurrence :
      (representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) →
    {targetSupport :
      (RepresentationIntentNAt oldVisit sourceIndex boundary).Support} →
    OpenResponsibilityAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      ((representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.account.supportOf occurrence) →
    OpenResponsibilityAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary) targetSupport →
      Type :=
  fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary) sourceEntry
      targetEntry

def representationIntentWriteRowSource
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    LedgerWriteRowSourceAt
      (representationIntentSource oldVisit sourceIndex boundary)
      (RepresentationIntentExactTransitionAt oldVisit sourceIndex boundary) where
  IncidenceOccurrenceAt := fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary) sourceEntry
      targetEntry
  compileEvolution := fun evolution => evolution
  compileExact := fun evolution => evolution

def representationIntentFirstRows
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt
      (representationIntentWriteRowSource oldVisit sourceIndex boundary)
      occurrence
      ⟨(representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.account.supportOf occurrence⟩ := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact
    { size := 3
      sourceEntryAt :=
        representationIntentEntryAt oldVisit sourceIndex boundary
      targetEntryAt :=
        representationIntentEntryAt oldVisit sourceIndex boundary
      rowAt := fun _ =>
        (representationIntentWriteRowSource oldVisit sourceIndex boundary
          ).generate (.carried rfl HEq.rfl) }

def representationIntentFirstCoverage
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt
      (representationIntentFirstRows oldVisit sourceIndex boundary
        occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact
    { destinationIndex :=
        representationIntentEntryIndex oldVisit sourceIndex boundary
      originIndex :=
        representationIntentEntryIndex oldVisit sourceIndex boundary
      destination_sound :=
        representationIntentEntryAt_index oldVisit sourceIndex boundary
      origin_sound :=
        representationIntentEntryAt_index oldVisit sourceIndex boundary }

def representationIntentFirstPatch
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt
      (representationIntentWriteRowSource oldVisit sourceIndex boundary)
      occurrence
      ⟨(representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.account.supportOf occurrence⟩ :=
  .complete
    (representationIntentFirstRows oldVisit sourceIndex boundary occurrence)
    (representationIntentFirstCoverage oldVisit sourceIndex boundary occurrence)

def representationIntentFirstEvolution
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) :
    LedgerWriteEvolutionAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      ⟨(representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.account.supportOf occurrence⟩
      ⟨(representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.account.supportOf occurrence⟩ :=
  (representationIntentFirstPatch oldVisit sourceIndex boundary occurrence
    ).toLedgerWriteEvolution

@[simp] theorem representationIntentFirstEvolution_destination_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current)
    (entry : OpenResponsibilityAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      ((representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.account.supportOf occurrence)) :
    ((representationIntentFirstEvolution oldVisit sourceIndex boundary
      occurrence).destination entry).1 = entry := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  change representationIntentEntryAt oldVisit sourceIndex boundary
      (representationIntentEntryIndex oldVisit sourceIndex boundary entry) =
    entry
  exact representationIntentEntryAt_index oldVisit sourceIndex boundary entry

@[simp] theorem representationIntentFirstEvolution_origin_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current)
    (entry : OpenResponsibilityAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      ((representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.account.supportOf occurrence)) :
    ((representationIntentFirstEvolution oldVisit sourceIndex boundary
      occurrence).origin entry).1 = entry := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  change representationIntentEntryAt oldVisit sourceIndex boundary
      (representationIntentEntryIndex oldVisit sourceIndex boundary entry) =
    entry
  exact representationIntentEntryAt_index oldVisit sourceIndex boundary entry

def representationIntentLedgerCompiler
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLedgerCompiler
      (representationIntentSource oldVisit sourceIndex boundary) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt :=
    RepresentationIntentExactTransitionAt oldVisit sourceIndex boundary
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := by
    intro current occurrence targetSupport sourceEntry targetEntry evolution
    cases evolution with
    | carried support_eq entry_eq =>
        cases support_eq
        cases entry_eq
        rfl
    | maintained _ _ lineage_eq _ _ _ => exact lineage_eq
    | transferred _ lineage_eq _ _ => exact lineage_eq
  writeRowSource :=
    representationIntentWriteRowSource oldVisit sourceIndex boundary
  terminalRowSource := LedgerTerminalRowSourceAt.empty
    (representationIntentSource oldVisit sourceIndex boundary)
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event.supportExact.down
    exact .nativeWrite PUnit.unit rfl
      (representationIntentEmitted oldVisit sourceIndex boundary
        (representationIntentNativeTarget current))
      (representationIntentFirstEvolution oldVisit sourceIndex boundary
        ⟨representationIntentSupportAt oldVisit sourceIndex boundary, event⟩)
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event.supportExact.down
    exact ⟨representationIntentFirstPatch oldVisit sourceIndex boundary
      ⟨representationIntentSupportAt oldVisit sourceIndex boundary, event⟩,
      rfl⟩

theorem representationIntentCompiler_commutes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (current : Bool) :
    SourceNativeLedgerEvolutionAt.CommutesWith
      (representationIntentEmitted oldVisit sourceIndex boundary)
      ((representationIntentLedgerCompiler oldVisit sourceIndex boundary
        ).compile
          (representationIntentEmitted oldVisit sourceIndex boundary current)) := by
  cases current <;> rfl

def representationIntentRestructuringLaw
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLedgerRestructuringLaw
      (representationIntentSource oldVisit sourceIndex boundary) where
  vocabulary := lossAllocationRestructuringVocabulary
    (rootedFailureAt oldVisit sourceIndex boundary)
  sourceEventAt := fun occurrence =>
    ((representationIntentSource oldVisit sourceIndex boundary
      ).toRootSource.account.supportOf occurrence,
      occurrence.2.materialWitness)
  obligationAt := by
    intro current occurrence support entry
    exact lossAllocationObligationAt
      (rootedFailureAt oldVisit sourceIndex boundary)
      occurrence.2.materialWitness ⟨entry.1, entry.2⟩
  responsibilityKey := AdmittedObligation.content
  anchorKey := fun _ => ()
  incidenceKey := id
  lineageKey := id
  responsibility_commutes := by
    intro current occurrence support entry
    rfl
  anchor_commutes := by
    intro current occurrence support entry
    rfl
  incidence_commutes := by
    intro current occurrence support entry
    rfl
  lineage_commutes := by
    intro current occurrence support entry
    rfl
  obligationAt_injective := by
    intro current occurrence support left right obligation_eq
    exact lossAllocationObligationAt_injective
      (rootedFailureAt oldVisit sourceIndex boundary)
      occurrence.2.materialWitness obligation_eq

def representationIntentRestructuringCertification
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentSource oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (representationIntentRestructuringLaw oldVisit sourceIndex boundary)
      ((representationIntentLedgerCompiler oldVisit sourceIndex boundary
        ).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  apply ExactLedgerRestructuringCertificationAt.ofInjective
  · intro left right origin_eq
    exact
      (representationIntentFirstEvolution_origin_exact oldVisit sourceIndex
        boundary
        ⟨representationIntentSupportAt oldVisit sourceIndex boundary,
          event⟩ left).symm.trans
        (origin_eq.trans
          (representationIntentFirstEvolution_origin_exact oldVisit sourceIndex
            boundary
            ⟨representationIntentSupportAt oldVisit sourceIndex boundary,
              event⟩ right))
  · intro left right destination_eq
    exact
      (representationIntentFirstEvolution_destination_exact oldVisit
        sourceIndex boundary
        ⟨representationIntentSupportAt oldVisit sourceIndex boundary,
          event⟩ left).symm.trans
        (destination_eq.trans
          (representationIntentFirstEvolution_destination_exact oldVisit
            sourceIndex boundary
            ⟨representationIntentSupportAt oldVisit sourceIndex boundary,
              event⟩ right))

def representationIntentRestructuringCompiler
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeRestructuringLedgerCompiler
      (representationIntentSource oldVisit sourceIndex boundary) where
  ledgerCompiler :=
    representationIntentLedgerCompiler oldVisit sourceIndex boundary
  restructuringLaw :=
    representationIntentRestructuringLaw oldVisit sourceIndex boundary
  certifyRestructuring :=
    representationIntentRestructuringCertification oldVisit sourceIndex boundary

def representationIntentRestructuringSource
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeRestructuringLedgerSource
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      (RepresentationIntentVAt oldVisit sourceIndex boundary) where
  source := representationIntentSource oldVisit sourceIndex boundary
  compiler :=
    representationIntentRestructuringCompiler oldVisit sourceIndex boundary

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler.representationIntentOccurrence_eq_emitted
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler.representationIntentFirstEvolution_destination_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler.representationIntentFirstEvolution_origin_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler.representationIntentLedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler.representationIntentCompiler_commutes
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler.representationIntentRestructuringSource
