import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.SourceGeneratedContributionMergeWorld

/-!
# Source-generated contribution-merge compiler

For any exact loss-allocation rooted failure, current `0` reads the complete
translated split ledger and generates one exact three-row write into the
two-row merged ledger.  The existing A/B children have the same generated
destination; the existing obstruction remains a separate `0 → 0`
continuation.  Every later current is an identity continuation on that merged
target.

This file defines only the event source, finite ledger patch, evolution and
ledger compiler.  Merge restructuring authority, roots and runtimes remain
downstream.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionMergeCompiler

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld

variable
    {OldV : ConstructiveRoot.Vocabulary}
    {oldWorld : SourceNativeAuthoritativeRootClosure
      M14SourceGeneratedLossAllocationWorld.OldN OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus M14SourceGeneratedLossAllocationWorld.OldN}
    {oldTheory : TheoryState M14SourceGeneratedLossAllocationWorld.OldN}
    {support : M14SourceGeneratedLossAllocationWorld.OldN.Support}
    {obstruction :
      M14SourceGeneratedLossAllocationWorld.OldN.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}

local notation "RootedFailure" => RootedActualExpressibilityFailureAt
  oldWorld oldVisit U7 failure

/-! ## Exact occurrence source -/

def contributionMergeSupportAt
    (rooted : RootedFailure) : Nat → (TargetN rooted).Support
  | 0 => contributionMergeInitialSupport rooted
  | _ + 1 => contributionMergeTargetSupport rooted

structure SourceGeneratedContributionMergeEventAt
    (rooted : RootedFailure) (current : Nat)
    (indexedSupport : (TargetN rooted).Support) : Type where
  private mk ::
  supportExact :
    PLift (indexedSupport = contributionMergeSupportAt rooted current)
  materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness
  materialExact : materialWitness =
    exactSourceGeneratedLossAllocationMaterialWitness

abbrev contributionMergeRootVocabulary
    (rooted : RootedFailure) : ConstructiveRoot.Vocabulary where
  Current := Nat
  Anchor := (TargetN rooted).Anchor
  Incidence := (TargetN rooted).Incidence
  Lineage := (TargetN rooted).Lineage
  anchorAt := fun current =>
    (TargetN rooted).anchorAt (contributionMergeSupportAt rooted current)
  incidenceAt := fun current =>
    (TargetN rooted).incidenceAt (contributionMergeSupportAt rooted current)
  lineageAt := fun current =>
    (TargetN rooted).lineageAt (contributionMergeSupportAt rooted current)
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => current + 1
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev TargetV (rooted : RootedFailure) :=
  contributionMergeRootVocabulary rooted

def contributionMergeEventLaw (rooted : RootedFailure) :
    SourceNativeEventAlgebra (TargetN rooted) (TargetV rooted) where
  EventAt := SourceGeneratedContributionMergeEventAt rooted
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun {_} {indexedSupport} _ =>
    OpenResponsibilityAt (TargetN rooted) indexedSupport
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

def contributionMergeSource (rooted : RootedFailure) :
    SourceNativeSource (TargetN rooted) (TargetV rooted) where
  initial := 0
  law := contributionMergeEventLaw rooted

def contributionMergeEmitted
    (rooted : RootedFailure) (current : (TargetV rooted).Current) :
    (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt current :=
  ⟨contributionMergeSupportAt rooted current,
    ⟨PLift.up rfl, exactSourceGeneratedLossAllocationMaterialWitness, rfl⟩⟩

theorem contributionMergeOccurrence_eq_emitted
    (rooted : RootedFailure)
    {current : (TargetV rooted).Current}
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt
        current) :
    occurrence = contributionMergeEmitted rooted current := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  cases event.materialExact
  cases event
  rfl

/-! ## Exact first-write rows -/

def ContributionMergeExactTransitionAt (rooted : RootedFailure) :
    {current : (TargetV rooted).Current} →
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt
        current) →
    {targetSupport : (TargetN rooted).Support} →
    OpenResponsibilityAt (TargetN rooted)
      ((contributionMergeSource rooted).toRootSource.account.supportOf
        occurrence) →
    OpenResponsibilityAt (TargetN rooted) targetSupport → Type :=
  fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (TargetN rooted) sourceEntry targetEntry

def contributionMergeWriteRowSource (rooted : RootedFailure) :
    LedgerWriteRowSourceAt (contributionMergeSource rooted)
      (ContributionMergeExactTransitionAt rooted) where
  IncidenceOccurrenceAt := fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (TargetN rooted) sourceEntry targetEntry
  compileEvolution := fun evolution => evolution
  compileExact := fun evolution => evolution

abbrev initialChildA (rooted : RootedFailure) :=
  contributionMergeInitialEntry rooted (lossAllocationTargetChildA rooted)

abbrev initialChildB (rooted : RootedFailure) :=
  contributionMergeInitialEntry rooted (lossAllocationTargetChildB rooted)

abbrev initialObstruction (rooted : RootedFailure) :=
  contributionMergeInitialEntry rooted
    (lossAllocationTargetObstruction rooted)

def contributionChildAToMerged (rooted : RootedFailure) :
    LedgerEntryEvolutionAt (TargetN rooted)
      (initialChildA rooted) (mergedContributionEntry rooted) :=
  .transferred
    (GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ())
    rfl rfl (Nat.le_refl 1)

def contributionChildBToMerged (rooted : RootedFailure) :
    LedgerEntryEvolutionAt (TargetN rooted)
      (initialChildB rooted) (mergedContributionEntry rooted) :=
  .transferred
    (GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ())
    rfl rfl (Nat.le_refl 1)

def contributionMergeObstructionContinuity (rooted : RootedFailure) :
    LedgerEntryEvolutionAt (TargetN rooted)
      (initialObstruction rooted) (mergedObstructionEntry rooted) :=
  .transferred
    (GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ())
    rfl rfl (Nat.le_refl 0)

def contributionMergeFirstSourceEntryAt (rooted : RootedFailure) :
    Fin 3 → (contributionMergeInitialLedger rooted).Entry :=
  Fin.cases (initialChildA rooted)
    (Fin.cases (initialChildB rooted)
      (fun _ => initialObstruction rooted))

def contributionMergeFirstTargetEntryAt (rooted : RootedFailure) :
    Fin 3 → (contributionMergeTargetLedger rooted).Entry :=
  Fin.cases (mergedContributionEntry rooted)
    (Fin.cases (mergedContributionEntry rooted)
      (fun _ => mergedObstructionEntry rooted))

def contributionMergeFirstRows
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    FiniteGeneratedLedgerWriteRowsAt
      (contributionMergeWriteRowSource rooted) occurrence
      (contributionMergeTargetLedger rooted) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact
    { size := 3
      sourceEntryAt := contributionMergeFirstSourceEntryAt rooted
      targetEntryAt := contributionMergeFirstTargetEntryAt rooted
      rowAt := Fin.cases
        ((contributionMergeWriteRowSource rooted).generate
          (contributionChildAToMerged rooted))
        (Fin.cases
          ((contributionMergeWriteRowSource rooted).generate
            (contributionChildBToMerged rooted))
          (fun _ => (contributionMergeWriteRowSource rooted).generate
            (contributionMergeObstructionContinuity rooted))) }

/-! ## Complete source and target coverage -/

theorem contributionMergeInitialEntry_cases
    (rooted : RootedFailure)
    (entry : (contributionMergeInitialLedger rooted).Entry) :
    entry = initialChildA rooted ∨
      entry = initialChildB rooted ∨
      entry = initialObstruction rooted := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      cases oldResponsibility
      rcases isOpen with ⟨leg, admitted⟩
      rcases admitted with admitted | admitted
      · cases admitted
        exact .inl rfl
      · cases admitted
        exact .inr (.inl rfl)
  | inr responsibilityDirection =>
      cases isOpen
      exact .inr (.inr rfl)

def contributionMergeInitialEntryIndex
    (rooted : RootedFailure) :
    (contributionMergeInitialLedger rooted).Entry → Fin 3
  | ⟨.inl _, ⟨.a, _⟩⟩ => ⟨0, by decide⟩
  | ⟨.inl _, ⟨.b, _⟩⟩ => ⟨1, by decide⟩
  | ⟨.inl _, ⟨.c, impossible⟩⟩ =>
      False.elim (by rcases impossible with h | h <;> cases h)
  | ⟨.inl _, ⟨.d, impossible⟩⟩ =>
      False.elim (by rcases impossible with h | h <;> cases h)
  | ⟨.inr _, _⟩ => ⟨2, by decide⟩

def contributionMergeTargetEntryIndex
    (rooted : RootedFailure) :
    (contributionMergeTargetLedger rooted).Entry → Fin 3
  | ⟨_, .inl _⟩ => ⟨0, by decide⟩
  | ⟨_, .inr _⟩ => ⟨2, by decide⟩

theorem contributionMergeFirstSourceEntryAt_index
    (rooted : RootedFailure)
    (entry : (contributionMergeInitialLedger rooted).Entry) :
    contributionMergeFirstSourceEntryAt rooted
        (contributionMergeInitialEntryIndex rooted entry) = entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      cases oldResponsibility
      rcases isOpen with ⟨leg, admitted⟩
      cases leg with
      | a => rfl
      | b => rfl
      | c => rcases admitted with h | h <;> cases h
      | d => rcases admitted with h | h <;> cases h
  | inr direction =>
      cases isOpen
      rfl

theorem contributionMergeFirstTargetEntryAt_index
    (rooted : RootedFailure)
    (entry : (contributionMergeTargetLedger rooted).Entry) :
    contributionMergeFirstTargetEntryAt rooted
        (contributionMergeTargetEntryIndex rooted entry) = entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  rcases isOpen with contribution | obstruction
  · rcases contribution.down with ⟨support_eq, responsibility_eq⟩
    cases support_eq
    cases responsibility_eq
    rfl
  · rcases obstruction.down with ⟨support_eq, responsibility_eq⟩
    cases support_eq
    cases responsibility_eq
    rfl

def contributionMergeFirstPatch
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    FiniteGeneratedLedgerWritePatchAt
      (contributionMergeWriteRowSource rooted) occurrence
      (contributionMergeTargetLedger rooted) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact .complete
    (contributionMergeFirstRows rooted
      ⟨contributionMergeInitialSupport rooted, event⟩)
    { destinationIndex := contributionMergeInitialEntryIndex rooted
      originIndex := contributionMergeTargetEntryIndex rooted
      destination_sound := contributionMergeFirstSourceEntryAt_index rooted
      origin_sound := contributionMergeFirstTargetEntryAt_index rooted }

def contributionMergeFirstEvolution
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    LedgerWriteEvolutionAt (TargetN rooted)
      (contributionMergeInitialLedger rooted)
      (contributionMergeTargetLedger rooted) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact (contributionMergeFirstPatch rooted
    ⟨contributionMergeInitialSupport rooted, event⟩).toLedgerWriteEvolution

@[simp] theorem contributionMergeFirst_destination_childA
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    ((contributionMergeFirstEvolution rooted occurrence).destination
      (initialChildA rooted)).1 = mergedContributionEntry rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

@[simp] theorem contributionMergeFirst_destination_childB
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    ((contributionMergeFirstEvolution rooted occurrence).destination
      (initialChildB rooted)).1 = mergedContributionEntry rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

theorem contributionMergeFirst_children_repeatedDestination
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    ((contributionMergeFirstEvolution rooted occurrence).destination
      (initialChildA rooted)).1 =
      ((contributionMergeFirstEvolution rooted occurrence).destination
        (initialChildB rooted)).1 := by
  rw [contributionMergeFirst_destination_childA,
    contributionMergeFirst_destination_childB]

@[simp] theorem contributionMergeFirst_destination_obstruction
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    ((contributionMergeFirstEvolution rooted occurrence).destination
      (initialObstruction rooted)).1 = mergedObstructionEntry rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

@[simp] theorem contributionMergeFirst_origin_contribution
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    ((contributionMergeFirstEvolution rooted occurrence).origin
      (mergedContributionEntry rooted)).1 = initialChildA rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

@[simp] theorem contributionMergeFirst_origin_obstruction
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    ((contributionMergeFirstEvolution rooted occurrence).origin
      (mergedObstructionEntry rooted)).1 = initialObstruction rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

theorem contributionMergeFirst_origin_cases
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0)
    (targetEntry : (contributionMergeTargetLedger rooted).Entry) :
    ((contributionMergeFirstEvolution rooted occurrence).origin
        targetEntry).1 = initialChildA rooted ∨
      ((contributionMergeFirstEvolution rooted occurrence).origin
        targetEntry).1 = initialObstruction rooted := by
  rcases contributionMergeTargetEntry_cases rooted targetEntry with
      target_eq | target_eq
  · subst targetEntry
    exact .inl (contributionMergeFirst_origin_contribution rooted occurrence)
  · subst targetEntry
    exact .inr (contributionMergeFirst_origin_obstruction rooted occurrence)

theorem contributionMergeFirst_target_cases
    (rooted : RootedFailure)
    (targetEntry : (contributionMergeTargetLedger rooted).Entry) :
    targetEntry = mergedContributionEntry rooted ∨
      targetEntry = mergedObstructionEntry rooted :=
  contributionMergeTargetEntry_cases rooted targetEntry

/-! ## Whole-ledger compiler -/

def contributionMergeLedgerCompiler (rooted : RootedFailure) :
    SourceNativeLedgerCompiler (contributionMergeSource rooted) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := ContributionMergeExactTransitionAt rooted
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
  writeRowSource := contributionMergeWriteRowSource rooted
  terminalRowSource := LedgerTerminalRowSourceAt.empty
    (contributionMergeSource rooted)
  compile := by
    intro current occurrence
    cases current with
    | zero =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact .nativeWrite () rfl (contributionMergeEmitted rooted 1)
          (contributionMergeFirstEvolution rooted
            ⟨contributionMergeInitialSupport rooted, event⟩)
    | succ current =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact .nativeWrite () rfl
          (contributionMergeEmitted rooted (Nat.succ current + 1))
          ((FiniteGeneratedLedgerWritePatchAt.identity
            (contributionMergeWriteRowSource rooted)
              ⟨contributionMergeTargetSupport rooted, event⟩
            ).toLedgerWriteEvolution)
  compilePatch := by
    intro current occurrence
    cases current with
    | zero =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact ⟨contributionMergeFirstPatch rooted
          ⟨contributionMergeInitialSupport rooted, event⟩, rfl⟩
    | succ current =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact ⟨FiniteGeneratedLedgerWritePatchAt.identity
          (contributionMergeWriteRowSource rooted)
            ⟨contributionMergeTargetSupport rooted, event⟩, rfl⟩

theorem contributionMergeCompiler_firstWrite_exact
    (rooted : RootedFailure) :
    (contributionMergeLedgerCompiler rooted).compile
        (contributionMergeEmitted rooted 0) =
      .nativeWrite () rfl (contributionMergeEmitted rooted 1)
        (contributionMergeFirstEvolution rooted
          (contributionMergeEmitted rooted 0)) :=
  rfl

def contributionMergeFirstSuccessor
    (rooted : RootedFailure) :
    SourceNativeLedgerGeneratedSuccessorAt
      (contributionMergeEmitted rooted 0)
      ((contributionMergeLedgerCompiler rooted).compile
        (contributionMergeEmitted rooted 0)) :=
  PUnit.unit

theorem contributionMergeCompiler_commutes
    (rooted : RootedFailure)
    (current : (TargetV rooted).Current) :
    SourceNativeLedgerEvolutionAt.CommutesWith
      (contributionMergeEmitted rooted)
      ((contributionMergeLedgerCompiler rooted).compile
        (contributionMergeEmitted rooted current)) := by
  cases current with
  | zero => rfl
  | succ current => rfl

end
end M14SourceGeneratedContributionMergeCompiler
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeCompiler.contributionMergeFirstEvolution
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeCompiler.contributionMergeLedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeCompiler.contributionMergeOccurrence_eq_emitted
