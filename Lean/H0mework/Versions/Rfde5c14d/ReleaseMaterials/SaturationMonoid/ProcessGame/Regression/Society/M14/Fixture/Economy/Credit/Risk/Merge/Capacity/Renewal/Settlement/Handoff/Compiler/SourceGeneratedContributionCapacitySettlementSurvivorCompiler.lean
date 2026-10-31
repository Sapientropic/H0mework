import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Action.SourceGeneratedContributionCapacitySettlementActionSource

/-!
# Survivor compiler after contribution-capacity settlement

The target is the capacity-U8 coface's already existing old face.  Its two
rows are explicitly enumerated on every write so causal authority remains
available after the terminal handoff.  Every current also generates a fresh
period-indexed actual-service UBI occurrence; no schedule or completed future
is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14UBIPeriodicActualServiceCapacity

def contributionCapacitySettlementSurvivorInitialCurrentAt
    (sourceIndex : Nat) : Nat :=
  contributionCapacityReopeningDepthAtCurrent sourceIndex 3 + 2

@[simp] theorem contributionCapacitySettlementSurvivorInitialCurrentAt_one :
    contributionCapacitySettlementSurvivorInitialCurrentAt 1 = 10 :=
  rfl

def contributionCapacitySettlementSurvivorDepthAt
    (_sourceIndex current : Nat) : Nat :=
  current

/-- Every survivor native write is paid by the actual-service witness carried
by that exact survivor event.  This proposition contains no target, next, or
completed schedule. -/
abbrev ContributionCapacitySettlementSurvivorExactWholeLedgerPaymentAt
    (current : Nat) :=
  PLift (Nonempty (PeriodicActualServiceExitAt current))

def contributionCapacitySettlementSurvivorVocabulary
    (oldVisit : OldVisit) : ConstructiveRoot.Vocabulary where
  Current := Nat
  Anchor := (ReopeningNAt oldVisit).Anchor
  Incidence := (ReopeningNAt oldVisit).Incidence
  Lineage := (ReopeningNAt oldVisit).Lineage
  anchorAt := fun _ => (ReopeningNAt oldVisit).anchorAt
    (contributionCapacitySettlementSurvivorSupport oldVisit)
  incidenceAt := fun _ => (ReopeningNAt oldVisit).incidenceAt
    (contributionCapacitySettlementSurvivorSupport oldVisit)
  lineageAt := fun _ => (ReopeningNAt oldVisit).lineageAt
    (contributionCapacitySettlementSurvivorSupport oldVisit)
  NativeWriteAt :=
    ContributionCapacitySettlementSurvivorExactWholeLedgerPaymentAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _payment => current + 1
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev ContributionCapacitySettlementSurvivorVAt
    (oldVisit : OldVisit) :=
  contributionCapacitySettlementSurvivorVocabulary oldVisit

structure SourceGeneratedContributionCapacitySettlementSurvivorEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    (current : Nat) (support : (ReopeningNAt oldVisit).Support) : Type where
  private mk ::
  supportExact : PLift
    (support = contributionCapacitySettlementSurvivorSupport oldVisit)
  sourceOccurrenceExact : settlementSource.occurrence =
    (ContributionCapacitySettlementActionRootAt oldVisit sourceIndex).emitted
      (contributionCapacitySettlementActionVisitAt oldVisit
        sourceIndex).current
  materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness
  materialExact : materialWitness =
    exactSourceGeneratedLossAllocationMaterialWitness
  periodicExitGenerated : Nonempty (PeriodicActualServiceExitAt
    (contributionCapacitySettlementSurvivorDepthAt sourceIndex current))

def contributionCapacitySettlementSurvivorEventLaw
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeEventAlgebra (ReopeningNAt oldVisit)
      (ContributionCapacitySettlementSurvivorVAt oldVisit) where
  EventAt := SourceGeneratedContributionCapacitySettlementSurvivorEventAt
    oldVisit sourceIndex settlementSource
  compile := fun event =>
    .nativeWrite (PLift.up event.periodicExitGenerated)
  AffectedInventoryAt := fun {_} {support} _ =>
    OpenResponsibilityAt (ReopeningNAt oldVisit) support
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

def contributionCapacitySettlementSurvivorSource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeSource (ReopeningNAt oldVisit)
      (ContributionCapacitySettlementSurvivorVAt oldVisit) where
  initial := contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex
  law := contributionCapacitySettlementSurvivorEventLaw oldVisit sourceIndex
    settlementSource

def contributionCapacitySettlementSurvivorEmitted
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    (current : Nat) :
    (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
      settlementSource).toRootSource.actual.OccurrenceAt current :=
  ⟨contributionCapacitySettlementSurvivorSupport oldVisit,
    { supportExact := PLift.up rfl
      sourceOccurrenceExact := rfl
      materialWitness := exactSourceGeneratedLossAllocationMaterialWitness
      materialExact := rfl
      periodicExitGenerated := ⟨periodicActualServiceExitAt
        (contributionCapacitySettlementSurvivorDepthAt sourceIndex current)⟩ }⟩

theorem contributionCapacitySettlementSurvivorOccurrence_eq_emitted
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource).toRootSource.actual.OccurrenceAt current) :
    occurrence = contributionCapacitySettlementSurvivorEmitted oldVisit
      sourceIndex settlementSource current := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  cases event.sourceOccurrenceExact
  cases event.materialExact
  cases event
  rfl

def ContributionCapacitySettlementSurvivorExactTransitionAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    {current : Nat} →
    (occurrence :
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (ReopeningNAt oldVisit).Support} →
    OpenResponsibilityAt (ReopeningNAt oldVisit) occurrence.1 →
    OpenResponsibilityAt (ReopeningNAt oldVisit) targetSupport → Type :=
  fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (ReopeningNAt oldVisit) sourceEntry targetEntry

def contributionCapacitySettlementSurvivorWriteRowSource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    LedgerWriteRowSourceAt
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource)
      (ContributionCapacitySettlementSurvivorExactTransitionAt oldVisit
        sourceIndex settlementSource) where
  IncidenceOccurrenceAt := fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (ReopeningNAt oldVisit) sourceEntry targetEntry
  compileEvolution := id
  compileExact := id

def contributionCapacitySettlementSurvivorRows
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt
      (contributionCapacitySettlementSurvivorWriteRowSource oldVisit
        sourceIndex settlementSource) occurrence
      (contributionCapacitySettlementSurvivorLedger oldVisit) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact
    { size := 2
      sourceEntryAt := contributionCapacitySettlementSurvivorEntryAt oldVisit
      targetEntryAt := contributionCapacitySettlementSurvivorEntryAt oldVisit
      rowAt := fun _ =>
        (contributionCapacitySettlementSurvivorWriteRowSource oldVisit
          sourceIndex settlementSource).generate (.carried rfl HEq.rfl) }

def contributionCapacitySettlementSurvivorPatch
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt
      (contributionCapacitySettlementSurvivorWriteRowSource oldVisit
        sourceIndex settlementSource) occurrence
      (contributionCapacitySettlementSurvivorLedger oldVisit) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact .complete
    (contributionCapacitySettlementSurvivorRows oldVisit sourceIndex
      settlementSource
      ⟨contributionCapacitySettlementSurvivorSupport oldVisit, event⟩)
    { destinationIndex :=
        contributionCapacitySettlementSurvivorEntryIndex oldVisit
      originIndex := contributionCapacitySettlementSurvivorEntryIndex oldVisit
      destination_sound :=
        contributionCapacitySettlementSurvivorEntryAt_index oldVisit
      origin_sound :=
        contributionCapacitySettlementSurvivorEntryAt_index oldVisit }

def contributionCapacitySettlementSurvivorEvolution
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource).toRootSource.actual.OccurrenceAt current) :
    LedgerWriteEvolutionAt (ReopeningNAt oldVisit)
      (contributionCapacitySettlementSurvivorLedger oldVisit)
      (contributionCapacitySettlementSurvivorLedger oldVisit) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact (contributionCapacitySettlementSurvivorPatch oldVisit sourceIndex
    settlementSource
    ⟨contributionCapacitySettlementSurvivorSupport oldVisit, event⟩
    ).toLedgerWriteEvolution

@[simp] theorem contributionCapacitySettlementSurvivorEvolution_destination
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource).toRootSource.actual.OccurrenceAt current)
    (entry : (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :
    ((contributionCapacitySettlementSurvivorEvolution oldVisit sourceIndex
      settlementSource occurrence).destination entry).1 = entry := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  rcases contributionCapacitySettlementSurvivorEntry_cases oldVisit entry with
      equality | equality <;> subst entry <;> rfl

@[simp] theorem contributionCapacitySettlementSurvivorEvolution_origin
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource).toRootSource.actual.OccurrenceAt current)
    (entry : (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :
    ((contributionCapacitySettlementSurvivorEvolution oldVisit sourceIndex
      settlementSource occurrence).origin entry).1 = entry := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  rcases contributionCapacitySettlementSurvivorEntry_cases oldVisit entry with
      equality | equality <;> subst entry <;> rfl

def contributionCapacitySettlementSurvivorLedgerCompiler
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeLedgerCompiler
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt :=
    ContributionCapacitySettlementSurvivorExactTransitionAt oldVisit
      sourceIndex settlementSource
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport sourceEntry targetEntry evolution
    cases evolution with
    | carried support_eq entry_eq =>
        cases support_eq
        cases entry_eq
        rfl
    | maintained _ _ lineage_eq _ _ _ => exact lineage_eq
    | transferred _ lineage_eq _ _ => exact lineage_eq
  writeRowSource := contributionCapacitySettlementSurvivorWriteRowSource
    oldVisit sourceIndex settlementSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty
    (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
      settlementSource)
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event.supportExact.down
    let exactOccurrence :
        (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
          settlementSource).toRootSource.actual.OccurrenceAt current :=
      ⟨contributionCapacitySettlementSurvivorSupport oldVisit, event⟩
    exact .nativeWrite (PLift.up event.periodicExitGenerated) rfl
      (contributionCapacitySettlementSurvivorEmitted oldVisit sourceIndex
        settlementSource ((show Nat from current) + 1))
      (contributionCapacitySettlementSurvivorEvolution oldVisit sourceIndex
        settlementSource exactOccurrence)
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event.supportExact.down
    exact ⟨contributionCapacitySettlementSurvivorPatch oldVisit sourceIndex
      settlementSource
      ⟨contributionCapacitySettlementSurvivorSupport oldVisit, event⟩,
      rfl⟩

def contributionCapacitySettlementSurvivorRestructuringLaw
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeLedgerRestructuringLaw
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource) where
  vocabulary := contributionCapacityReopeningRestructuringVocabulary oldVisit
  sourceEventAt := fun occurrence =>
    (occurrence.1.1, occurrence.2.materialWitness)
  obligationAt := by
    intro current occurrence support entry
    exact contributionCapacityU8ObligationAt oldVisit
      occurrence.2.materialWitness
      (⟨entry.1, entry.2⟩ : OpenResponsibilityAt
        (CapacityU8NAt oldVisit) support.1)
  responsibilityKey := AdmittedObligation.content
  anchorKey := fun _ => ()
  incidenceKey := id
  lineageKey := id
  responsibility_commutes := by intros; rfl
  anchor_commutes := by intros; rfl
  incidence_commutes := by intros; rfl
  lineage_commutes := by intros; rfl
  obligationAt_injective := by
    intro current occurrence support left right equality
    exact contributionCapacityU8ObligationAt_injective oldVisit
      occurrence.2.materialWitness equality

def contributionCapacitySettlementSurvivorRestructuringCompiler
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeRestructuringLedgerCompiler
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource) where
  ledgerCompiler := contributionCapacitySettlementSurvivorLedgerCompiler
    oldVisit sourceIndex settlementSource
  restructuringLaw := contributionCapacitySettlementSurvivorRestructuringLaw
    oldVisit sourceIndex settlementSource
  certifyRestructuring := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event.supportExact.down
    exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right equality => by
        exact
          (contributionCapacitySettlementSurvivorEvolution_origin oldVisit
            sourceIndex settlementSource
            ⟨contributionCapacitySettlementSurvivorSupport oldVisit, event⟩
            left).symm.trans
              (equality.trans
                (contributionCapacitySettlementSurvivorEvolution_origin
                  oldVisit sourceIndex settlementSource
                  ⟨contributionCapacitySettlementSurvivorSupport oldVisit,
                    event⟩ right)))
      (fun left right equality => by
        exact
          (contributionCapacitySettlementSurvivorEvolution_destination oldVisit
            sourceIndex settlementSource
            ⟨contributionCapacitySettlementSurvivorSupport oldVisit, event⟩
            left).symm.trans
              (equality.trans
                (contributionCapacitySettlementSurvivorEvolution_destination
                  oldVisit sourceIndex settlementSource
                  ⟨contributionCapacitySettlementSurvivorSupport oldVisit,
                    event⟩ right)))

def contributionCapacitySettlementSurvivorRestructuringSource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeRestructuringLedgerSource (ReopeningNAt oldVisit)
      (ContributionCapacitySettlementSurvivorVAt oldVisit) where
  source := contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
    settlementSource
  compiler := contributionCapacitySettlementSurvivorRestructuringCompiler
    oldVisit sourceIndex settlementSource

end
end M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler.contributionCapacitySettlementSurvivorLedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler.contributionCapacitySettlementSurvivorRestructuringSource
