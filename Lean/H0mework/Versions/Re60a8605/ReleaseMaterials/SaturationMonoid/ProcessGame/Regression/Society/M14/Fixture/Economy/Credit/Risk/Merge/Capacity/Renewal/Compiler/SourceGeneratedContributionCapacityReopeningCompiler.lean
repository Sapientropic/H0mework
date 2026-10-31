import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.World.SourceGeneratedContributionCapacityReopeningWorld

/-!
# Source-generated capacity reopening compiler

The target event jointly records the exact exhausted residual occurrence and
the canonical periodic actual-service UBI occurrence determined by its source
index.  The whole-ledger write is a three-row bijective phase transport;
every budget remains zero.  Positive actionable-exit capacity lives only in
the generated UBI payload.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityReopeningCompiler

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14UBIPeriodicActualServiceCapacity

abbrev ReopeningSourceVisitAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacityU8RuntimeVisitAt oldVisit sourceIndex

abbrev ReopeningSourceEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ExactTemporalCausalRootEventAt
    (CapacityU8RootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
    (ReopeningSourceVisitAt oldVisit sourceIndex)

def contributionCapacityReopeningPhaseAt : Nat → Bool
  | 0 => false
  | _ + 1 => true

def contributionCapacityReopeningSupportAt
    (oldVisit : OldVisit) (current : Nat) : (ReopeningNAt oldVisit).Support :=
  ((CapacityCofaceAt oldVisit).cofaceSupport,
    contributionCapacityReopeningPhaseAt current)

/-- The source index is part of the vocabulary because it fixes the global
actual-service occurrence paid by this local current. -/
abbrev ContributionCapacityReopeningExactWholeLedgerPaymentAt
    (sourceIndex current : Nat) :=
  PLift (Nonempty (PeriodicActualServiceExitAt
    (contributionCapacityReopeningDepthAtCurrent sourceIndex current)))

/-- Compiler-level target: the payment is an existence gate, while the
structural current still fixes the numeric successor. -/
def contributionCapacityReopeningNextPaidBy
    {sourceIndex current : Nat}
    (_payment : ContributionCapacityReopeningExactWholeLedgerPaymentAt
      sourceIndex current) : Nat :=
  current + 1

def contributionCapacityReopeningVocabulary
    (oldVisit : OldVisit) (sourceIndex : Nat) : ConstructiveRoot.Vocabulary where
  Current := Nat
  Anchor := (ReopeningNAt oldVisit).Anchor
  Incidence := (ReopeningNAt oldVisit).Incidence
  Lineage := (ReopeningNAt oldVisit).Lineage
  anchorAt := fun current =>
    (ReopeningNAt oldVisit).anchorAt
      (contributionCapacityReopeningSupportAt oldVisit current)
  incidenceAt := fun current =>
    (ReopeningNAt oldVisit).incidenceAt
      (contributionCapacityReopeningSupportAt oldVisit current)
  lineageAt := fun current =>
    (ReopeningNAt oldVisit).lineageAt
      (contributionCapacityReopeningSupportAt oldVisit current)
  NativeWriteAt := ContributionCapacityReopeningExactWholeLedgerPaymentAt
    sourceIndex
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := contributionCapacityReopeningNextPaidBy
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev ReopeningVAt (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacityReopeningVocabulary oldVisit sourceIndex

structure SourceGeneratedContributionCapacityReopeningEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (current : Nat) (support : (ReopeningNAt oldVisit).Support) : Type where
  private mk ::
  supportExact :
    PLift (support = contributionCapacityReopeningSupportAt oldVisit current)
  sourceOccurrenceExact : sourceEvent.occurrence =
    (CapacityU8RootAt oldVisit).emitted
      (ReopeningSourceVisitAt oldVisit sourceIndex).current
  materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness
  materialExact : materialWitness =
    exactSourceGeneratedLossAllocationMaterialWitness
  periodicExitGenerated : Nonempty (PeriodicActualServiceExitAt
    (contributionCapacityReopeningDepthAtCurrent sourceIndex current))

def contributionCapacityReopeningEventLaw
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex) :
    SourceNativeEventAlgebra (ReopeningNAt oldVisit)
      (ReopeningVAt oldVisit sourceIndex) where
  EventAt := SourceGeneratedContributionCapacityReopeningEventAt oldVisit
    sourceIndex sourceEvent
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

def contributionCapacityReopeningSource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex) :
    SourceNativeSource (ReopeningNAt oldVisit)
      (ReopeningVAt oldVisit sourceIndex) where
  initial := (0 : Nat)
  law := contributionCapacityReopeningEventLaw oldVisit sourceIndex sourceEvent

def contributionCapacityReopeningEmitted
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (current : Nat) :
    (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
      |>.toRootSource.actual.OccurrenceAt current :=
  ⟨contributionCapacityReopeningSupportAt oldVisit current,
    { supportExact := PLift.up rfl
      sourceOccurrenceExact :=
        contributionCapacityU8Occurrence_eq_emitted oldVisit
          sourceEvent.occurrence
      materialWitness := exactSourceGeneratedLossAllocationMaterialWitness
      materialExact := rfl
      periodicExitGenerated :=
        ⟨contributionCapacityReopeningPeriodicExitAt sourceIndex current⟩ }⟩

theorem contributionCapacityReopeningOccurrence_eq_emitted
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current) :
    occurrence = contributionCapacityReopeningEmitted oldVisit sourceIndex
      sourceEvent current := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  cases event.sourceOccurrenceExact
  cases event.materialExact
  cases event
  rfl

def contributionCapacityReopeningLedgerAtCurrent
    (oldVisit : OldVisit) (current : Nat) :
    CompleteLiveLedgerAt (ReopeningNAt oldVisit) :=
  contributionCapacityReopeningLedgerAt oldVisit
    (contributionCapacityReopeningPhaseAt current)

def contributionCapacityReopeningCurrentEntryAt
    (oldVisit : OldVisit) (current : Nat) :
    Fin 3 → (contributionCapacityReopeningLedgerAtCurrent oldVisit current).Entry :=
  contributionCapacityReopeningEntryAt oldVisit
    (contributionCapacityReopeningPhaseAt current)

def contributionCapacityReopeningCurrentEntryIndex
    (oldVisit : OldVisit) (current : Nat) :
    (contributionCapacityReopeningLedgerAtCurrent oldVisit current).Entry → Fin 3 :=
  contributionCapacityReopeningEntryIndex oldVisit
    (contributionCapacityReopeningPhaseAt current)

theorem contributionCapacityReopeningCurrentEntryAt_index
    (oldVisit : OldVisit) (current : Nat)
    (entry : (contributionCapacityReopeningLedgerAtCurrent oldVisit current).Entry) :
    contributionCapacityReopeningCurrentEntryAt oldVisit current
        (contributionCapacityReopeningCurrentEntryIndex oldVisit current entry) =
      entry := by
  exact contributionCapacityReopeningEntryAt_index oldVisit
    (contributionCapacityReopeningPhaseAt current) entry

def contributionCapacityReopeningForwardEntry
    (oldVisit : OldVisit) (current : Nat) :
    (contributionCapacityReopeningLedgerAtCurrent oldVisit current).Entry →
      (contributionCapacityReopeningLedgerAtCurrent oldVisit
        (current + 1)).Entry :=
  (contributionCapacityReopeningPhaseRetract oldVisit
    (contributionCapacityReopeningPhaseAt current)
    (contributionCapacityReopeningPhaseAt (current + 1))).forward

def contributionCapacityReopeningBackwardEntry
    (oldVisit : OldVisit) (current : Nat) :
    (contributionCapacityReopeningLedgerAtCurrent oldVisit
        (current + 1)).Entry →
      (contributionCapacityReopeningLedgerAtCurrent oldVisit current).Entry :=
  (contributionCapacityReopeningPhaseRetract oldVisit
    (contributionCapacityReopeningPhaseAt current)
    (contributionCapacityReopeningPhaseAt (current + 1))).backward

theorem contributionCapacityReopeningForwardEntry_injective
    (oldVisit : OldVisit) (current : Nat) :
    Function.Injective
      (contributionCapacityReopeningForwardEntry oldVisit current) :=
  contributionCapacityReopeningPhaseForward_injective oldVisit _ _

theorem contributionCapacityReopeningBackwardEntry_injective
    (oldVisit : OldVisit) (current : Nat) :
    Function.Injective
      (contributionCapacityReopeningBackwardEntry oldVisit current) :=
  by
    simpa only [contributionCapacityReopeningBackwardEntry,
      contributionCapacityReopeningLedgerAtCurrent,
      contributionCapacityReopeningPhaseRetract] using
      (contributionCapacityReopeningPhaseForward_injective oldVisit
        (contributionCapacityReopeningPhaseAt (current + 1))
        (contributionCapacityReopeningPhaseAt current))

def contributionCapacityReopeningRowEvolution
    (oldVisit : OldVisit) (current : Nat)
    (index : Fin 3) :
    LedgerEntryEvolutionAt (ReopeningNAt oldVisit)
      (contributionCapacityReopeningCurrentEntryAt oldVisit current index)
      (contributionCapacityReopeningCurrentEntryAt oldVisit (current + 1)
        index) := by
  cases current with
  | zero =>
      exact contributionCapacityReopeningTransferAt oldVisit
        (contributionCapacityU8EntryAt oldVisit index)
  | succ current => exact .carried rfl HEq.rfl

def ContributionCapacityReopeningExactTransitionAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex) :
    {current : Nat} →
    (occurrence :
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (ReopeningNAt oldVisit).Support} →
    OpenResponsibilityAt (ReopeningNAt oldVisit)
      ((contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.account.supportOf occurrence) →
    OpenResponsibilityAt (ReopeningNAt oldVisit) targetSupport → Type :=
  fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (ReopeningNAt oldVisit) sourceEntry targetEntry

def contributionCapacityReopeningWriteRowSource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex) :
    LedgerWriteRowSourceAt
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
      (ContributionCapacityReopeningExactTransitionAt oldVisit sourceIndex
        sourceEvent) where
  IncidenceOccurrenceAt := fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (ReopeningNAt oldVisit) sourceEntry targetEntry
  compileEvolution := fun evolution => evolution
  compileExact := fun evolution => evolution

def contributionCapacityReopeningRows
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt
      (contributionCapacityReopeningWriteRowSource oldVisit sourceIndex
        sourceEvent) occurrence
      (contributionCapacityReopeningLedgerAtCurrent oldVisit (current + 1)) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact
    { size := 3
      sourceEntryAt := contributionCapacityReopeningCurrentEntryAt oldVisit current
      targetEntryAt := contributionCapacityReopeningCurrentEntryAt oldVisit
        (current + 1)
      rowAt := fun index =>
        (contributionCapacityReopeningWriteRowSource oldVisit sourceIndex
          sourceEvent).generate
            (contributionCapacityReopeningRowEvolution oldVisit current index) }

def contributionCapacityReopeningPatch
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt
      (contributionCapacityReopeningWriteRowSource oldVisit sourceIndex
        sourceEvent) occurrence
      (contributionCapacityReopeningLedgerAtCurrent oldVisit (current + 1)) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact .complete
    (contributionCapacityReopeningRows oldVisit sourceIndex sourceEvent
      ⟨contributionCapacityReopeningSupportAt oldVisit current, event⟩)
    { destinationIndex :=
        contributionCapacityReopeningCurrentEntryIndex oldVisit current
      originIndex :=
        contributionCapacityReopeningCurrentEntryIndex oldVisit (current + 1)
      destination_sound :=
        contributionCapacityReopeningCurrentEntryAt_index oldVisit current
      origin_sound :=
        contributionCapacityReopeningCurrentEntryAt_index oldVisit (current + 1) }

def contributionCapacityReopeningEvolution
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current) :
    LedgerWriteEvolutionAt (ReopeningNAt oldVisit)
      (contributionCapacityReopeningLedgerAtCurrent oldVisit current)
      (contributionCapacityReopeningLedgerAtCurrent oldVisit (current + 1)) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact (contributionCapacityReopeningPatch oldVisit sourceIndex sourceEvent
    ⟨contributionCapacityReopeningSupportAt oldVisit current, event⟩
    ).toLedgerWriteEvolution

@[simp] theorem contributionCapacityReopeningEvolution_destination
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current)
    (entry : (contributionCapacityReopeningLedgerAtCurrent oldVisit current).Entry) :
    ((contributionCapacityReopeningEvolution oldVisit sourceIndex sourceEvent
      occurrence).destination entry).1 =
        contributionCapacityReopeningForwardEntry oldVisit current entry := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  cases current with
  | zero =>
      rcases contributionCapacityReopeningEntry_cases oldVisit false entry with
          entry_eq | entry_eq | entry_eq <;> subst entry <;> rfl
  | succ current =>
      rcases contributionCapacityReopeningEntry_cases oldVisit true entry with
          entry_eq | entry_eq | entry_eq <;> subst entry <;> rfl

@[simp] theorem contributionCapacityReopeningEvolution_origin
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current)
    (entry :
      (contributionCapacityReopeningLedgerAtCurrent oldVisit (current + 1)).Entry) :
    ((contributionCapacityReopeningEvolution oldVisit sourceIndex sourceEvent
      occurrence).origin entry).1 =
        contributionCapacityReopeningBackwardEntry oldVisit current entry := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  cases current with
  | zero =>
      rcases contributionCapacityReopeningEntry_cases oldVisit true entry with
          entry_eq | entry_eq | entry_eq <;> subst entry <;> rfl
  | succ current =>
      rcases contributionCapacityReopeningEntry_cases oldVisit true entry with
          entry_eq | entry_eq | entry_eq <;> subst entry <;> rfl

def contributionCapacityReopeningLedgerCompiler
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex) :
    SourceNativeLedgerCompiler
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := ContributionCapacityReopeningExactTransitionAt oldVisit
    sourceIndex sourceEvent
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
  writeRowSource := contributionCapacityReopeningWriteRowSource oldVisit
    sourceIndex sourceEvent
  terminalRowSource := LedgerTerminalRowSourceAt.empty
    (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event.supportExact.down
    exact .nativeWrite (PLift.up event.periodicExitGenerated) rfl
      (contributionCapacityReopeningEmitted oldVisit sourceIndex sourceEvent
        ((show Nat from current) + 1))
      (contributionCapacityReopeningEvolution oldVisit sourceIndex sourceEvent
        ⟨contributionCapacityReopeningSupportAt oldVisit current, event⟩)
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event.supportExact.down
    exact ⟨contributionCapacityReopeningPatch oldVisit sourceIndex sourceEvent
      ⟨contributionCapacityReopeningSupportAt oldVisit current, event⟩, rfl⟩

def contributionCapacityReopeningRestructuringVocabulary
    (oldVisit : OldVisit) : RestructuringVocabulary where
  base := ContributionCapacityU8LifecycleV oldVisit
  DescendantAt := fun _ parentIncidence parentContent childIncidence childContent =>
    PLift (parentIncidence = childIncidence) ×
      PLift (parentContent = childContent)
  SplitCoverageAt := fun _ _ _ => PEmpty
  MergeCoverageAt := fun _ _ _ => PEmpty
  LocalDischargePreservedAt := fun _ parentContent childContent =>
    PLift (parentContent = childContent)
  RenameAt := fun _ oldContent newContent => PLift (oldContent = newContent)

def contributionCapacityReopeningRestructuringLaw
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex) :
    SourceNativeLedgerRestructuringLaw
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent) where
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
    have oldEquality := contributionCapacityU8ObligationAt_injective oldVisit
      occurrence.2.materialWitness equality
    rcases left with ⟨leftResponsibility, leftOpen⟩
    rcases right with ⟨rightResponsibility, rightOpen⟩
    exact oldEquality

def contributionCapacityReopeningRestructuringCertification
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (contributionCapacityReopeningRestructuringLaw oldVisit sourceIndex
        sourceEvent)
      ((contributionCapacityReopeningLedgerCompiler oldVisit sourceIndex
        sourceEvent).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right equality => by
      apply contributionCapacityReopeningBackwardEntry_injective oldVisit
        current
      exact (contributionCapacityReopeningEvolution_origin oldVisit
        sourceIndex sourceEvent
        ⟨contributionCapacityReopeningSupportAt oldVisit current, event⟩
        left).symm.trans
          (equality.trans
            (contributionCapacityReopeningEvolution_origin oldVisit
              sourceIndex sourceEvent
              ⟨contributionCapacityReopeningSupportAt oldVisit current, event⟩
              right)))
    (fun left right equality => by
      apply contributionCapacityReopeningForwardEntry_injective oldVisit
        current
      exact (contributionCapacityReopeningEvolution_destination oldVisit
        sourceIndex sourceEvent
        ⟨contributionCapacityReopeningSupportAt oldVisit current, event⟩
        left).symm.trans
          (equality.trans
            (contributionCapacityReopeningEvolution_destination oldVisit
              sourceIndex sourceEvent
              ⟨contributionCapacityReopeningSupportAt oldVisit current, event⟩
              right)))

def contributionCapacityReopeningRestructuringCompiler
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex) :
    SourceNativeRestructuringLedgerCompiler
      (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent) where
  ledgerCompiler := contributionCapacityReopeningLedgerCompiler oldVisit
    sourceIndex sourceEvent
  restructuringLaw := contributionCapacityReopeningRestructuringLaw oldVisit
    sourceIndex sourceEvent
  certifyRestructuring := contributionCapacityReopeningRestructuringCertification
    oldVisit sourceIndex sourceEvent

def contributionCapacityReopeningRestructuringSource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex) :
    SourceNativeRestructuringLedgerSource
      (ReopeningNAt oldVisit) (ReopeningVAt oldVisit sourceIndex) where
  source := contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent
  compiler := contributionCapacityReopeningRestructuringCompiler oldVisit
    sourceIndex sourceEvent

end
end M14SourceGeneratedContributionCapacityReopeningCompiler
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningCompiler.contributionCapacityReopeningLedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningCompiler.contributionCapacityReopeningRestructuringSource
