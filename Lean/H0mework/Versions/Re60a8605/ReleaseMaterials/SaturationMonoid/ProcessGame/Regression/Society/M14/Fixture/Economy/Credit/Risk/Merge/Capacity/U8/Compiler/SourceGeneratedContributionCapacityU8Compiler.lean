import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Lifecycle.SourceGeneratedContributionCapacityU8Lifecycle
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIPeriodicActualServiceCapacity

/-!
# Source-generated contribution-capacity U8 compiler

The canonical minimal coface has exactly three live rows at its emitted
support: inherited contribution, inherited obstruction, and the generated
addressable residual.  Every root write enumerates this whole ledger and
carries all three rows without refilling any budget.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityU8Compiler

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14UBIPeriodicActualServiceCapacity

/-- U8 local current `n` is the exact payment occurrence at global depth
`n + 2`.  In particular current two is runtime depth four and current three
is the reopening-action source at depth five. -/
def contributionCapacityU8PaymentDepthAtCurrent (current : Nat) : Nat :=
  current + 2

@[simp] theorem contributionCapacityU8PaymentDepthAtCurrent_two :
    contributionCapacityU8PaymentDepthAtCurrent 2 = 4 :=
  rfl

@[simp] theorem contributionCapacityU8PaymentDepthAtCurrent_three :
    contributionCapacityU8PaymentDepthAtCurrent 3 = 5 :=
  rfl

abbrev ContributionCapacityU8ExactWholeLedgerPaymentAt (current : Nat) :=
  PLift (Nonempty (PeriodicActualServiceExitAt
    (contributionCapacityU8PaymentDepthAtCurrent current)))

def contributionCapacityU8NextPaidBy
    {current : Nat}
    (_payment : ContributionCapacityU8ExactWholeLedgerPaymentAt current) :
    Nat :=
  current + 1

def contributionCapacityU8Vocabulary
    (oldVisit : OldVisit) : ConstructiveRoot.Vocabulary where
  Current := Nat
  Anchor := (CapacityU8NAt oldVisit).Anchor
  Incidence := (CapacityU8NAt oldVisit).Incidence
  Lineage := (CapacityU8NAt oldVisit).Lineage
  anchorAt := fun _ =>
    (CapacityU8NAt oldVisit).anchorAt (CapacityCofaceAt oldVisit).cofaceSupport
  incidenceAt := fun _ =>
    (CapacityU8NAt oldVisit).incidenceAt
      (CapacityCofaceAt oldVisit).cofaceSupport
  lineageAt := fun _ =>
    (CapacityU8NAt oldVisit).lineageAt
      (CapacityCofaceAt oldVisit).cofaceSupport
  NativeWriteAt := ContributionCapacityU8ExactWholeLedgerPaymentAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := contributionCapacityU8NextPaidBy
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev CapacityU8VAt (oldVisit : OldVisit) :=
  contributionCapacityU8Vocabulary oldVisit

structure SourceGeneratedContributionCapacityU8EventAt
    (oldVisit : OldVisit) (current : Nat)
    (indexedSupport : (CapacityU8NAt oldVisit).Support) : Type where
  private mk ::
  supportExact :
    PLift (indexedSupport = (CapacityCofaceAt oldVisit).cofaceSupport)
  materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness
  materialExact : materialWitness =
    exactSourceGeneratedLossAllocationMaterialWitness
  periodicExitGenerated : Nonempty (PeriodicActualServiceExitAt
    (contributionCapacityU8PaymentDepthAtCurrent current))

def contributionCapacityU8EventLaw
    (oldVisit : OldVisit) :
    SourceNativeEventAlgebra (CapacityU8NAt oldVisit)
      (CapacityU8VAt oldVisit) where
  EventAt := SourceGeneratedContributionCapacityU8EventAt oldVisit
  compile := fun event =>
    .nativeWrite (PLift.up event.periodicExitGenerated)
  AffectedInventoryAt := fun {_} {indexedSupport} _ =>
    OpenResponsibilityAt (CapacityU8NAt oldVisit) indexedSupport
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by
    intro current indexedSupport event
    cases event.supportExact.down
    rfl
  incidence_commutes := by
    intro current indexedSupport event
    cases event.supportExact.down
    rfl
  lineage_commutes := by
    intro current indexedSupport event
    cases event.supportExact.down
    rfl

def contributionCapacityU8Source
    (oldVisit : OldVisit) :
    SourceNativeSource (CapacityU8NAt oldVisit) (CapacityU8VAt oldVisit) where
  initial := (0 : Nat)
  law := contributionCapacityU8EventLaw oldVisit

def contributionCapacityU8Emitted
    (oldVisit : OldVisit) (current : (CapacityU8VAt oldVisit).Current) :
    (contributionCapacityU8Source oldVisit).toRootSource.actual.OccurrenceAt
      current :=
  ⟨(CapacityCofaceAt oldVisit).cofaceSupport,
    { supportExact := PLift.up rfl
      materialWitness := exactSourceGeneratedLossAllocationMaterialWitness
      materialExact := rfl
      periodicExitGenerated :=
        ⟨periodicActualServiceExitAt
          (contributionCapacityU8PaymentDepthAtCurrent current)⟩ }⟩

theorem contributionCapacityU8Occurrence_eq_emitted
    (oldVisit : OldVisit)
    {current : (CapacityU8VAt oldVisit).Current}
    (occurrence :
      (contributionCapacityU8Source oldVisit).toRootSource.actual.OccurrenceAt
        current) :
    occurrence = contributionCapacityU8Emitted oldVisit current := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  cases event.materialExact
  cases event
  rfl

/-! ## Exact three-row ledger -/

def contributionCapacityU8Ledger
    (oldVisit : OldVisit) : CompleteLiveLedgerAt (CapacityU8NAt oldVisit) :=
  ⟨(CapacityCofaceAt oldVisit).cofaceSupport⟩

def contributionCapacityU8InheritedContribution
    (oldVisit : OldVisit) :
    (contributionCapacityU8Ledger oldVisit).Entry :=
  (CapacityCofaceAt oldVisit).cofaceLedgerRetract.forward
    (contributionCapacityCutTargetContribution
      (capacityActionRootedAt oldVisit))

def contributionCapacityU8InheritedObstruction
    (oldVisit : OldVisit) :
    (contributionCapacityU8Ledger oldVisit).Entry :=
  (CapacityCofaceAt oldVisit).cofaceLedgerRetract.forward
    (contributionCapacityCutTargetObstruction
      (capacityActionRootedAt oldVisit))

def contributionCapacityU8GeneratedResidual
    (oldVisit : OldVisit) :
    (contributionCapacityU8Ledger oldVisit).Entry :=
  (CapacityCofaceAt oldVisit).obstructionEntry

def contributionCapacityU8EntryAt
    (oldVisit : OldVisit) :
    Fin 3 → (contributionCapacityU8Ledger oldVisit).Entry :=
  Fin.cases (contributionCapacityU8InheritedContribution oldVisit)
    (fun tail => Fin.cases
      (contributionCapacityU8InheritedObstruction oldVisit)
      (fun _ => contributionCapacityU8GeneratedResidual oldVisit) tail)

def contributionCapacityU8EntryIndex
    (oldVisit : OldVisit) :
    (contributionCapacityU8Ledger oldVisit).Entry → Fin 3
  | ⟨.inl _oldResponsibility, .inl _contribution⟩ => ⟨0, by decide⟩
  | ⟨.inl _oldResponsibility, .inr _obstruction⟩ => ⟨1, by decide⟩
  | ⟨.inr _direction, _aligned⟩ => ⟨2, by decide⟩

theorem contributionCapacityU8EntryAt_index
    (oldVisit : OldVisit)
    (entry : (contributionCapacityU8Ledger oldVisit).Entry) :
    contributionCapacityU8EntryAt oldVisit
        (contributionCapacityU8EntryIndex oldVisit entry) = entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      rcases isOpen with contribution | obstruction
      · rcases contribution.down with ⟨support_eq, responsibility_eq⟩
        cases support_eq
        cases responsibility_eq
        rfl
      · rcases obstruction.down with ⟨support_eq, responsibility_eq⟩
        cases support_eq
        cases responsibility_eq
        rfl
  | inr direction =>
      cases direction
      cases isOpen
      rfl

theorem contributionCapacityU8Entry_cases
    (oldVisit : OldVisit)
    (entry : (contributionCapacityU8Ledger oldVisit).Entry) :
    entry = contributionCapacityU8InheritedContribution oldVisit ∨
      entry = contributionCapacityU8InheritedObstruction oldVisit ∨
      entry = contributionCapacityU8GeneratedResidual oldVisit := by
  have indexed := contributionCapacityU8EntryAt_index oldVisit entry
  generalize index_eq : contributionCapacityU8EntryIndex oldVisit entry = index at indexed
  revert indexed
  refine Fin.cases ?_ (fun tail => ?_) index
  · intro indexed
    exact .inl indexed.symm
  · change Fin 2 at tail
    refine Fin.cases ?_ (fun last => ?_) tail
    · intro indexed
      exact .inr (.inl indexed.symm)
    · change Fin 1 at last
      have last_eq : last = (0 : Fin 1) := Subsingleton.elim _ _
      subst last
      intro indexed
      exact .inr (.inr indexed.symm)

/-! ## Whole-ledger carried write -/

def ContributionCapacityU8ExactTransitionAt
    (oldVisit : OldVisit) :
    {current : (CapacityU8VAt oldVisit).Current} →
    (occurrence :
      (contributionCapacityU8Source oldVisit).toRootSource.actual.OccurrenceAt
        current) →
    {targetSupport : (CapacityU8NAt oldVisit).Support} →
    OpenResponsibilityAt (CapacityU8NAt oldVisit)
      ((contributionCapacityU8Source oldVisit).toRootSource.account.supportOf
        occurrence) →
    OpenResponsibilityAt (CapacityU8NAt oldVisit) targetSupport → Type :=
  fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (CapacityU8NAt oldVisit) sourceEntry targetEntry

def contributionCapacityU8WriteRowSource
    (oldVisit : OldVisit) :
    LedgerWriteRowSourceAt (contributionCapacityU8Source oldVisit)
      (ContributionCapacityU8ExactTransitionAt oldVisit) where
  IncidenceOccurrenceAt := fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (CapacityU8NAt oldVisit) sourceEntry targetEntry
  compileEvolution := fun evolution => evolution
  compileExact := fun evolution => evolution

def contributionCapacityU8Rows
    (oldVisit : OldVisit)
    {current : (CapacityU8VAt oldVisit).Current}
    (occurrence :
      (contributionCapacityU8Source oldVisit).toRootSource.actual.OccurrenceAt
        current) :
    FiniteGeneratedLedgerWriteRowsAt
      (contributionCapacityU8WriteRowSource oldVisit) occurrence
      (contributionCapacityU8Ledger oldVisit) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact
    { size := 3
      sourceEntryAt := contributionCapacityU8EntryAt oldVisit
      targetEntryAt := contributionCapacityU8EntryAt oldVisit
      rowAt := fun index =>
        (contributionCapacityU8WriteRowSource oldVisit).generate
          (LedgerEntryEvolutionAt.carried rfl HEq.rfl) }

def contributionCapacityU8Patch
    (oldVisit : OldVisit)
    {current : (CapacityU8VAt oldVisit).Current}
    (occurrence :
      (contributionCapacityU8Source oldVisit).toRootSource.actual.OccurrenceAt
        current) :
    FiniteGeneratedLedgerWritePatchAt
      (contributionCapacityU8WriteRowSource oldVisit) occurrence
      (contributionCapacityU8Ledger oldVisit) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact .complete
    (contributionCapacityU8Rows oldVisit
      ⟨(CapacityCofaceAt oldVisit).cofaceSupport, event⟩)
    { destinationIndex := contributionCapacityU8EntryIndex oldVisit
      originIndex := contributionCapacityU8EntryIndex oldVisit
      destination_sound := contributionCapacityU8EntryAt_index oldVisit
      origin_sound := contributionCapacityU8EntryAt_index oldVisit }

def contributionCapacityU8Evolution
    (oldVisit : OldVisit)
    {current : (CapacityU8VAt oldVisit).Current}
    (occurrence :
      (contributionCapacityU8Source oldVisit).toRootSource.actual.OccurrenceAt
        current) :
    LedgerWriteEvolutionAt (CapacityU8NAt oldVisit)
      (contributionCapacityU8Ledger oldVisit)
      (contributionCapacityU8Ledger oldVisit) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact (contributionCapacityU8Patch oldVisit
    ⟨(CapacityCofaceAt oldVisit).cofaceSupport, event⟩
    ).toLedgerWriteEvolution

@[simp] theorem contributionCapacityU8Evolution_destination
    (oldVisit : OldVisit)
    {current : (CapacityU8VAt oldVisit).Current}
    (occurrence :
      (contributionCapacityU8Source oldVisit).toRootSource.actual.OccurrenceAt
        current)
    (entry : (contributionCapacityU8Ledger oldVisit).Entry) :
    ((contributionCapacityU8Evolution oldVisit occurrence).destination entry).1 =
      entry := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rcases contributionCapacityU8Entry_cases oldVisit entry with
      entry_eq | entry_eq | entry_eq <;> subst entry <;> rfl

@[simp] theorem contributionCapacityU8Evolution_origin
    (oldVisit : OldVisit)
    {current : (CapacityU8VAt oldVisit).Current}
    (occurrence :
      (contributionCapacityU8Source oldVisit).toRootSource.actual.OccurrenceAt
        current)
    (entry : (contributionCapacityU8Ledger oldVisit).Entry) :
    ((contributionCapacityU8Evolution oldVisit occurrence).origin entry).1 =
      entry := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rcases contributionCapacityU8Entry_cases oldVisit entry with
      entry_eq | entry_eq | entry_eq <;> subst entry <;> rfl

def contributionCapacityU8LedgerCompiler
    (oldVisit : OldVisit) :
    SourceNativeLedgerCompiler (contributionCapacityU8Source oldVisit) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := ContributionCapacityU8ExactTransitionAt oldVisit
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
  writeRowSource := contributionCapacityU8WriteRowSource oldVisit
  terminalRowSource := LedgerTerminalRowSourceAt.empty
    (contributionCapacityU8Source oldVisit)
  compile := by
    intro current occurrence
    rcases occurrence with ⟨indexedSupport, event⟩
    cases event.supportExact.down
    exact .nativeWrite (PLift.up event.periodicExitGenerated) rfl
      (contributionCapacityU8Emitted oldVisit
        (Nat.succ (show Nat from current)))
      (contributionCapacityU8Evolution oldVisit
        ⟨(CapacityCofaceAt oldVisit).cofaceSupport, event⟩)
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨indexedSupport, event⟩
    cases event.supportExact.down
    exact ⟨contributionCapacityU8Patch oldVisit
      ⟨(CapacityCofaceAt oldVisit).cofaceSupport, event⟩, rfl⟩

/-! ## Identity restructuring certification -/

def contributionCapacityU8RestructuringVocabulary
    (oldVisit : OldVisit) : RestructuringVocabulary where
  base := ContributionCapacityU8LifecycleV oldVisit
  DescendantAt := fun _ parentIncidence parentContent
      childIncidence childContent =>
    PLift (parentIncidence = childIncidence) ×
      PLift (parentContent = childContent)
  SplitCoverageAt := fun _ _ _ => PEmpty
  MergeCoverageAt := fun _ _ _ => PEmpty
  LocalDischargePreservedAt := fun _ parentContent childContent =>
    PLift (parentContent = childContent)
  RenameAt := fun _ oldContent newContent =>
    PLift (oldContent = newContent)

def contributionCapacityU8RestructuringLaw
    (oldVisit : OldVisit) :
    SourceNativeLedgerRestructuringLaw
      (contributionCapacityU8Source oldVisit) where
  vocabulary := contributionCapacityU8RestructuringVocabulary oldVisit
  sourceEventAt := fun occurrence =>
    ((contributionCapacityU8Source oldVisit).toRootSource.account.supportOf
        occurrence,
      occurrence.2.materialWitness)
  obligationAt := by
    intro current occurrence indexedSupport entry
    exact contributionCapacityU8ObligationAt oldVisit
      occurrence.2.materialWitness entry
  responsibilityKey := AdmittedObligation.content
  anchorKey := fun _ => ()
  incidenceKey := id
  lineageKey := id
  responsibility_commutes := by intros; rfl
  anchor_commutes := by intros; rfl
  incidence_commutes := by intros; rfl
  lineage_commutes := by intros; rfl
  obligationAt_injective := by
    intro current occurrence indexedSupport left right obligation_eq
    exact contributionCapacityU8ObligationAt_injective oldVisit
      occurrence.2.materialWitness obligation_eq

def contributionCapacityU8RestructuringCertification
    (oldVisit : OldVisit)
    {current : (CapacityU8VAt oldVisit).Current}
    (occurrence :
      (contributionCapacityU8Source oldVisit).toRootSource.actual.OccurrenceAt
        current) :
    SourceNativeLedgerRestructuringCertificationAt
      (contributionCapacityU8RestructuringLaw oldVisit)
      ((contributionCapacityU8LedgerCompiler oldVisit).compile occurrence) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right origin_eq =>
      (contributionCapacityU8Evolution_origin oldVisit
        ⟨(CapacityCofaceAt oldVisit).cofaceSupport, event⟩ left).symm.trans
        (origin_eq.trans
          (contributionCapacityU8Evolution_origin oldVisit
            ⟨(CapacityCofaceAt oldVisit).cofaceSupport, event⟩ right)))
    (fun left right destination_eq =>
      (contributionCapacityU8Evolution_destination oldVisit
        ⟨(CapacityCofaceAt oldVisit).cofaceSupport, event⟩ left).symm.trans
        (destination_eq.trans
          (contributionCapacityU8Evolution_destination oldVisit
            ⟨(CapacityCofaceAt oldVisit).cofaceSupport, event⟩ right)))

def contributionCapacityU8RestructuringCompiler
    (oldVisit : OldVisit) :
    SourceNativeRestructuringLedgerCompiler
      (contributionCapacityU8Source oldVisit) where
  ledgerCompiler := contributionCapacityU8LedgerCompiler oldVisit
  restructuringLaw := contributionCapacityU8RestructuringLaw oldVisit
  certifyRestructuring :=
    contributionCapacityU8RestructuringCertification oldVisit

def contributionCapacityU8RestructuringSource
    (oldVisit : OldVisit) :
    SourceNativeRestructuringLedgerSource
      (CapacityU8NAt oldVisit) (CapacityU8VAt oldVisit) where
  source := contributionCapacityU8Source oldVisit
  compiler := contributionCapacityU8RestructuringCompiler oldVisit

end
end M14SourceGeneratedContributionCapacityU8Compiler
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8Compiler.contributionCapacityU8LedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8Compiler.contributionCapacityU8RestructuringSource
