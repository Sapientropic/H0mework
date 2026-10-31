import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.World.SourceGeneratedContributionCapacityJointSettlementWorld
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Source.SourceGeneratedContributionCapacityJointSettlementMaterial

/-!
# Whole-ledger compiler for joint survivor settlement

The action-generated target network begins on the exact translated two-row
survivor ledger.  Its first occurrence carries both rows definitionally; its
second occurrence is a faithful terminal whose private incidences are indexed
by the complete `Fin 2` presentation.  Row `0` consumes same-depth common
clearing and row `1` consumes same-depth clearing backstop.  Both also retain
their exact survivor authority and independent answer consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityJointSettlementCompiler

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open Lifecycle Universal Relations Exchange Settlement
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M4AutomaticFullFulfillmentRegression
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14PeriodicCommonClearingRenewal
open M14PeriodicClearingBackstopRenewal

abbrev JointMaterialAt (oldVisit : OldVisit) (sourceIndex : Nat) :=
  SourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
    sourceIndex

inductive ContributionCapacityJointSettlementNativeWriteAt : Bool → Type
  | ingress : ContributionCapacityJointSettlementNativeWriteAt false

inductive ContributionCapacityJointSettlementFaithfulTerminalAt : Bool → Type
  | settled : ContributionCapacityJointSettlementFaithfulTerminalAt true

def contributionCapacityJointSettlementVocabulary
    (oldVisit : OldVisit) : ConstructiveRoot.Vocabulary where
  Current := Bool
  Anchor := (JointSettlementNAt oldVisit).Anchor
  Incidence := (JointSettlementNAt oldVisit).Incidence
  Lineage := (JointSettlementNAt oldVisit).Lineage
  anchorAt := fun _ => (JointSettlementNAt oldVisit).anchorAt
    (contributionCapacityJointSettlementLiveSupport oldVisit)
  incidenceAt := fun _ => (JointSettlementNAt oldVisit).incidenceAt
    (contributionCapacityJointSettlementLiveSupport oldVisit)
  lineageAt := fun _ => (JointSettlementNAt oldVisit).lineageAt
    (contributionCapacityJointSettlementLiveSupport oldVisit)
  NativeWriteAt := ContributionCapacityJointSettlementNativeWriteAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := ContributionCapacityJointSettlementFaithfulTerminalAt
  nativeTarget := fun write => match write with | .ingress => true
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev ContributionCapacityJointSettlementVAt (oldVisit : OldVisit) :=
  contributionCapacityJointSettlementVocabulary oldVisit

inductive SourceGeneratedContributionCapacityJointSettlementEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    (current : Bool) → (JointSettlementNAt oldVisit).Support → Type
  | private ingress :
      SourceGeneratedContributionCapacityJointSettlementEventAt oldVisit
        sourceIndex material false
        (contributionCapacityJointSettlementLiveSupport oldVisit)
  | private terminal :
      SourceGeneratedContributionCapacityJointSettlementEventAt oldVisit
        sourceIndex material true
        (contributionCapacityJointSettlementLiveSupport oldVisit)

def contributionCapacityJointSettlementEventLaw
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeEventAlgebra (JointSettlementNAt oldVisit)
      (ContributionCapacityJointSettlementVAt oldVisit) where
  EventAt := SourceGeneratedContributionCapacityJointSettlementEventAt
    oldVisit sourceIndex material
  compile := fun event => match event with
    | .ingress => .nativeWrite .ingress
    | .terminal => .faithfulTerminal .settled
  AffectedInventoryAt := fun {_} {support} _ =>
    OpenResponsibilityAt (JointSettlementNAt oldVisit) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event <;> rfl
  incidence_commutes := by intro current support event; cases event <;> rfl
  lineage_commutes := by intro current support event; cases event <;> rfl

def contributionCapacityJointSettlementSource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeSource (JointSettlementNAt oldVisit)
      (ContributionCapacityJointSettlementVAt oldVisit) where
  initial := false
  law := contributionCapacityJointSettlementEventLaw oldVisit sourceIndex
    material

def contributionCapacityJointSettlementEmitted
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    (current : Bool) →
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt current
  | false =>
      ⟨contributionCapacityJointSettlementLiveSupport oldVisit, .ingress⟩
  | true =>
      ⟨contributionCapacityJointSettlementLiveSupport oldVisit, .terminal⟩

theorem contributionCapacityJointSettlementOccurrence_eq_emitted
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    {current : Bool}
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt current) :
    occurrence = contributionCapacityJointSettlementEmitted oldVisit
      sourceIndex material current := by
  rcases occurrence with ⟨support, event⟩
  cases event <;> rfl

/-! ## Complete two-row ingress -/

def ContributionCapacityJointSettlementExactTransitionAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    {current : Bool} →
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (JointSettlementNAt oldVisit).Support} →
    OpenResponsibilityAt (JointSettlementNAt oldVisit) occurrence.1 →
    OpenResponsibilityAt (JointSettlementNAt oldVisit) targetSupport → Type :=
  fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (JointSettlementNAt oldVisit) sourceEntry targetEntry

def contributionCapacityJointSettlementWriteRowSource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    LedgerWriteRowSourceAt
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
      (ContributionCapacityJointSettlementExactTransitionAt oldVisit
        sourceIndex material) where
  IncidenceOccurrenceAt := fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (JointSettlementNAt oldVisit) sourceEntry targetEntry
  compileEvolution := id
  compileExact := id

def contributionCapacityJointSettlementWriteRows
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt false) :
    FiniteGeneratedLedgerWriteRowsAt
      (contributionCapacityJointSettlementWriteRowSource oldVisit sourceIndex
        material) occurrence
      (contributionCapacityJointSettlementLiveLedger oldVisit) := by
  rw [contributionCapacityJointSettlementOccurrence_eq_emitted oldVisit
    sourceIndex material occurrence]
  exact
    { size := 2
      sourceEntryAt := contributionCapacityJointSettlementLiveEntryAt oldVisit
      targetEntryAt := contributionCapacityJointSettlementLiveEntryAt oldVisit
      rowAt := fun _ =>
        (contributionCapacityJointSettlementWriteRowSource oldVisit sourceIndex
          material).generate (.carried rfl HEq.rfl) }

def contributionCapacityJointSettlementWritePatch
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt false) :
    FiniteGeneratedLedgerWritePatchAt
      (contributionCapacityJointSettlementWriteRowSource oldVisit sourceIndex
        material) occurrence
      (contributionCapacityJointSettlementLiveLedger oldVisit) := by
  rw [contributionCapacityJointSettlementOccurrence_eq_emitted oldVisit
    sourceIndex material occurrence]
  exact .complete
    (contributionCapacityJointSettlementWriteRows oldVisit sourceIndex material
      (contributionCapacityJointSettlementEmitted oldVisit sourceIndex material
        false))
    { destinationIndex :=
        contributionCapacityJointSettlementLiveEntryIndex oldVisit
      originIndex := contributionCapacityJointSettlementLiveEntryIndex oldVisit
      destination_sound :=
        contributionCapacityJointSettlementLiveEntryAt_index oldVisit
      origin_sound :=
        contributionCapacityJointSettlementLiveEntryAt_index oldVisit }

def contributionCapacityJointSettlementWriteEvolution
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt false) :
    LedgerWriteEvolutionAt (JointSettlementNAt oldVisit)
      (contributionCapacityJointSettlementLiveLedger oldVisit)
      (contributionCapacityJointSettlementLiveLedger oldVisit) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact (contributionCapacityJointSettlementWritePatch oldVisit sourceIndex
    material (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
      material false)).toLedgerWriteEvolution

@[simp] theorem contributionCapacityJointSettlementWriteEvolution_destination
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt false)
    (entry : (contributionCapacityJointSettlementLiveLedger oldVisit).Entry) :
    ((contributionCapacityJointSettlementWriteEvolution oldVisit sourceIndex
      material occurrence).destination entry).1 = entry := by
  rw [contributionCapacityJointSettlementOccurrence_eq_emitted oldVisit
    sourceIndex material occurrence]
  have indexed :=
    contributionCapacityJointSettlementLiveEntryAt_index oldVisit entry
  generalize index_eq :
    contributionCapacityJointSettlementLiveEntryIndex oldVisit entry = index
      at indexed
  revert indexed
  refine Fin.cases ?_ (fun tail => ?_) index
  · intro equality
    subst entry
    rfl
  · change Fin 1 at tail
    have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
    subst tail
    intro equality
    subst entry
    rfl

@[simp] theorem contributionCapacityJointSettlementWriteEvolution_origin
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt false)
    (entry : (contributionCapacityJointSettlementLiveLedger oldVisit).Entry) :
    ((contributionCapacityJointSettlementWriteEvolution oldVisit sourceIndex
      material occurrence).origin entry).1 = entry := by
  rw [contributionCapacityJointSettlementOccurrence_eq_emitted oldVisit
    sourceIndex material occurrence]
  have indexed :=
    contributionCapacityJointSettlementLiveEntryAt_index oldVisit entry
  generalize index_eq :
    contributionCapacityJointSettlementLiveEntryIndex oldVisit entry = index
      at indexed
  revert indexed
  refine Fin.cases ?_ (fun tail => ?_) index
  · intro equality
    subst entry
    rfl
  · change Fin 1 at tail
    have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
    subst tail
    intro equality
    subst entry
    rfl

/-! ## Row-indexed actual material and faithful terminal -/

def ContributionCapacityJointSettlementRowAxisAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) : Fin 2 → Type :=
  Fin.cases
    (PLift (material.commonClearing =
        sourceGeneratedProofCarryingPeriodicSymmetricClearingAt
          (contributionCapacityJointSettlementDepthAt sourceIndex)) ×
      PLift (IsEmpty
        (OpenSettlementAt automaticCompiler automaticOccurrence)))
    (fun _ =>
      PLift (material.clearingBackstop =
          sourceGeneratedProofCarryingPeriodicClearingBackstopAt
            (contributionCapacityJointSettlementDepthAt sourceIndex)) ×
        PLift (Nonempty
          (AutomaticFullFulfillment.FulfilledSlotAt
            (exchangeLaw := exchangeLaw) exactExchangeSeed
            material.clearingBackstop.localActivation.nextGeneratedState.current
            (.b : Leg))))

def contributionCapacityJointSettlementRowAxisAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (entryIndex : Fin 2) :
    ContributionCapacityJointSettlementRowAxisAt oldVisit sourceIndex material
      entryIndex := by
  refine Fin.cases ?_ (fun _ => ?_) entryIndex
  · exact ⟨PLift.up material.commonClearingExact,
      PLift.up material.commonClearing.closedTarget⟩
  · exact ⟨PLift.up material.clearingBackstopExact,
      PLift.up material.clearingBackstop.localNextFulfilledB⟩

structure ContributionCapacityJointSettlementTerminalRowEvidenceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (entryIndex : Fin 2) : Type where
  authorityExact : PLift
    (material.authorityAt entryIndex =
      contributionCapacitySettlementSurvivorEntryAuthorityAt oldVisit
        sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex
        entryIndex)
  consumerExact : PLift
    (material.consumerAt entryIndex =
      contributionCapacitySettlementSurvivorEntryAnswerConsumerAt oldVisit
        sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex
        entryIndex)
  settlementAxis : ContributionCapacityJointSettlementRowAxisAt oldVisit
    sourceIndex material entryIndex

def contributionCapacityJointSettlementTerminalRowEvidenceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (entryIndex : Fin 2) :
    ContributionCapacityJointSettlementTerminalRowEvidenceAt oldVisit
      sourceIndex material entryIndex where
  authorityExact := PLift.up (congrFun material.authorityAtExact entryIndex)
  consumerExact := PLift.up (congrFun material.consumerAtExact entryIndex)
  settlementAxis := contributionCapacityJointSettlementRowAxisAt oldVisit
    sourceIndex material entryIndex

inductive SourceGeneratedContributionCapacityJointSettlementTerminalIncidenceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt true) →
    OpenResponsibilityAt (JointSettlementNAt oldVisit) occurrence.1 → Type
  | private row (entryIndex : Fin 2)
      (evidence : ContributionCapacityJointSettlementTerminalRowEvidenceAt
        oldVisit sourceIndex material entryIndex) :
      SourceGeneratedContributionCapacityJointSettlementTerminalIncidenceAt
        oldVisit sourceIndex material
        (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
          material true)
        (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex)

private def contributionCapacityJointSettlementSupportReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    {occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt true}
    {entry : OpenResponsibilityAt (JointSettlementNAt oldVisit) occurrence.1}
    (incidence :
      SourceGeneratedContributionCapacityJointSettlementTerminalIncidenceAt
        oldVisit sourceIndex material occurrence entry) :
    (JointSettlementNAt oldVisit).DispositionAt occurrence.1
      .supportSettlement := by
  cases incidence
  exact GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ()

def contributionCapacityJointSettlementTerminalRowSource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    LedgerTerminalRowSourceAt
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material) where
  IncidenceOccurrenceAt := fun {current} occurrence entry =>
    match current with
    | false => PEmpty
    | true =>
        SourceGeneratedContributionCapacityJointSettlementTerminalIncidenceAt
          oldVisit sourceIndex material occurrence entry
  compile := by
    intro current occurrence entry incidence
    cases current with
    | false => exact nomatch incidence
    | true =>
        exact ⟨contributionCapacityJointSettlementSupportReceiptAt oldVisit
          sourceIndex material incidence⟩

def contributionCapacityJointSettlementTerminalPatch
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt true) :
    FiniteGeneratedLedgerTerminalPatchAt
      (contributionCapacityJointSettlementTerminalRowSource oldVisit
        sourceIndex material) occurrence := by
  rw [contributionCapacityJointSettlementOccurrence_eq_emitted oldVisit
    sourceIndex material occurrence]
  exact
    { size := 2
      entryAt := contributionCapacityJointSettlementLiveEntryAt oldVisit
      rowAt := fun entryIndex =>
        (contributionCapacityJointSettlementTerminalRowSource oldVisit
          sourceIndex material).generate
            (.row entryIndex
              (contributionCapacityJointSettlementTerminalRowEvidenceAt
                oldVisit sourceIndex material entryIndex))
      entryIndex := contributionCapacityJointSettlementLiveEntryIndex oldVisit
      entry_sound :=
        contributionCapacityJointSettlementLiveEntryAt_index oldVisit }

def contributionCapacityJointSettlementTerminalEvolution
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt true) :
    LedgerTerminalEvolutionAt (JointSettlementNAt oldVisit)
      (contributionCapacityJointSettlementLiveLedger oldVisit) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact (contributionCapacityJointSettlementTerminalPatch oldVisit sourceIndex
    material (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
      material true)).toLedgerTerminalEvolution

def contributionCapacityJointSettlementLedgerCompiler
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeLedgerCompiler
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := ContributionCapacityJointSettlementExactTransitionAt
    oldVisit sourceIndex material
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport sourceEntry targetEntry evolution
    cases evolution with
    | carried support_eq entry_eq => cases support_eq; cases entry_eq; rfl
    | maintained _ _ lineage_eq _ _ _ => exact lineage_eq
    | transferred _ lineage_eq _ _ => exact lineage_eq
  writeRowSource := contributionCapacityJointSettlementWriteRowSource oldVisit
    sourceIndex material
  terminalRowSource := contributionCapacityJointSettlementTerminalRowSource
    oldVisit sourceIndex material
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    · exact .nativeWrite .ingress rfl
        (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
          material true)
        (contributionCapacityJointSettlementWriteEvolution oldVisit sourceIndex
          material
          (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
            material false))
    · exact .faithfulTerminal .settled rfl
        (contributionCapacityJointSettlementTerminalEvolution oldVisit
          sourceIndex material
          (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
            material true))
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    · exact ⟨contributionCapacityJointSettlementWritePatch oldVisit
        sourceIndex material
        (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
          material false), rfl⟩
    · exact ⟨.finite (contributionCapacityJointSettlementTerminalPatch oldVisit
        sourceIndex material
        (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
          material true)), rfl⟩

end
end M14SourceGeneratedContributionCapacityJointSettlementCompiler
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementCompiler.contributionCapacityJointSettlementLedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementCompiler.contributionCapacityJointSettlementTerminalPatch
