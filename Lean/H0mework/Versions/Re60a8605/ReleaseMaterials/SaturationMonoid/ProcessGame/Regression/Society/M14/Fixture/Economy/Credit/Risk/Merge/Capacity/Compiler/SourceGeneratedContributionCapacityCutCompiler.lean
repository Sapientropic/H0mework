import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.World.SourceGeneratedContributionCapacityCutWorld

/-!
# Source-generated contribution-capacity cut compiler

Current `0` reads the complete two-row merge target and writes the complete
two-row capacity target.  The contribution is maintained with a strict
`1 -> 0` debit; the obstruction is transferred with `0 -> 0` continuity.
Every later current is an identity continuation on the cut target.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCutCompiler

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionCapacityCutWorld

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

def contributionCapacityCutSupportAt
    (rooted : RootedFailure) : Nat → (CutN rooted).Support
  | 0 => contributionCapacityCutInitialSupport rooted
  | _ + 1 => contributionCapacityCutTargetSupport rooted

structure SourceGeneratedContributionCapacityCutEventAt
    (rooted : RootedFailure) (current : Nat)
    (indexedSupport : (CutN rooted).Support) : Type where
  private mk ::
  supportExact :
    PLift (indexedSupport = contributionCapacityCutSupportAt rooted current)
  materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness
  materialExact : materialWitness =
    exactSourceGeneratedLossAllocationMaterialWitness

abbrev contributionCapacityCutRootVocabulary
    (rooted : RootedFailure) : ConstructiveRoot.Vocabulary where
  Current := Nat
  Anchor := (CutN rooted).Anchor
  Incidence := (CutN rooted).Incidence
  Lineage := (CutN rooted).Lineage
  anchorAt := fun current =>
    (CutN rooted).anchorAt (contributionCapacityCutSupportAt rooted current)
  incidenceAt := fun current =>
    (CutN rooted).incidenceAt (contributionCapacityCutSupportAt rooted current)
  lineageAt := fun current =>
    (CutN rooted).lineageAt (contributionCapacityCutSupportAt rooted current)
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
  contributionCapacityCutRootVocabulary rooted

def contributionCapacityCutEventLaw (rooted : RootedFailure) :
    SourceNativeEventAlgebra (CutN rooted) (TargetV rooted) where
  EventAt := SourceGeneratedContributionCapacityCutEventAt rooted
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun {_} {indexedSupport} _ =>
    OpenResponsibilityAt (CutN rooted) indexedSupport
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

def contributionCapacityCutSource (rooted : RootedFailure) :
    SourceNativeSource (CutN rooted) (TargetV rooted) where
  initial := 0
  law := contributionCapacityCutEventLaw rooted

def contributionCapacityCutEmitted
    (rooted : RootedFailure) (current : (TargetV rooted).Current) :
    (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
      current :=
  ⟨contributionCapacityCutSupportAt rooted current,
    ⟨PLift.up rfl, exactSourceGeneratedLossAllocationMaterialWitness, rfl⟩⟩

theorem contributionCapacityCutOccurrence_eq_emitted
    (rooted : RootedFailure)
    {current : (TargetV rooted).Current}
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        current) :
    occurrence = contributionCapacityCutEmitted rooted current := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  cases event.materialExact
  cases event
  rfl

/-! ## Exact first-write rows -/

def ContributionCapacityCutExactTransitionAt
    (rooted : RootedFailure) :
    {current : (TargetV rooted).Current} →
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        current) →
    {targetSupport : (CutN rooted).Support} →
    OpenResponsibilityAt (CutN rooted)
      ((contributionCapacityCutSource rooted).toRootSource.account.supportOf
        occurrence) →
    OpenResponsibilityAt (CutN rooted) targetSupport → Type :=
  fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (CutN rooted) sourceEntry targetEntry

def contributionCapacityCutWriteRowSource (rooted : RootedFailure) :
    LedgerWriteRowSourceAt (contributionCapacityCutSource rooted)
      (ContributionCapacityCutExactTransitionAt rooted) where
  IncidenceOccurrenceAt := fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (CutN rooted) sourceEntry targetEntry
  compileEvolution := fun evolution => evolution
  compileExact := fun evolution => evolution

abbrev initialContribution (rooted : RootedFailure) :=
  contributionCapacityCutInitialEntry rooted (mergedContributionEntry rooted)

abbrev initialObstruction (rooted : RootedFailure) :=
  contributionCapacityCutInitialEntry rooted (mergedObstructionEntry rooted)

def contributionCapacityStrictDebit (rooted : RootedFailure) :
    LedgerEntryEvolutionAt (CutN rooted)
      (initialContribution rooted)
      (contributionCapacityCutTargetContribution rooted) :=
  .maintained rfl rfl rfl rfl rfl (by
    change 0 < 1
    decide)

def contributionCapacityObstructionContinuity
    (rooted : RootedFailure) :
    LedgerEntryEvolutionAt (CutN rooted)
      (initialObstruction rooted)
      (contributionCapacityCutTargetObstruction rooted) :=
  .transferred
    (GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ())
    rfl rfl (Nat.le_refl 0)

def contributionCapacityFirstSourceEntryAt
    (rooted : RootedFailure) :
    Fin 2 → (contributionCapacityCutInitialLedger rooted).Entry :=
  Fin.cases (initialContribution rooted) (fun _ => initialObstruction rooted)

def contributionCapacityFirstTargetEntryAt
    (rooted : RootedFailure) :
    Fin 2 → (contributionCapacityCutTargetLedger rooted).Entry :=
  Fin.cases (contributionCapacityCutTargetContribution rooted)
    (fun _ => contributionCapacityCutTargetObstruction rooted)

def contributionCapacityFirstRows
    (rooted : RootedFailure)
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        0) :
    FiniteGeneratedLedgerWriteRowsAt
      (contributionCapacityCutWriteRowSource rooted) occurrence
      (contributionCapacityCutTargetLedger rooted) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact
    { size := 2
      sourceEntryAt := contributionCapacityFirstSourceEntryAt rooted
      targetEntryAt := contributionCapacityFirstTargetEntryAt rooted
      rowAt := Fin.cases
        ((contributionCapacityCutWriteRowSource rooted).generate
          (contributionCapacityStrictDebit rooted))
        (fun _ => (contributionCapacityCutWriteRowSource rooted).generate
          (contributionCapacityObstructionContinuity rooted)) }

/-! ## Complete source and target coverage -/

theorem contributionCapacityCutInitialEntry_cases
    (rooted : RootedFailure)
    (entry : (contributionCapacityCutInitialLedger rooted).Entry) :
    entry = initialContribution rooted ∨
      entry = initialObstruction rooted := by
  rcases entry with ⟨responsibility, isOpen⟩
  rcases isOpen with contribution | obstruction
  · rcases contribution.down with ⟨support_eq, responsibility_eq⟩
    cases support_eq
    cases responsibility_eq
    exact .inl (by congr)
  · rcases obstruction.down with ⟨support_eq, responsibility_eq⟩
    cases support_eq
    cases responsibility_eq
    exact .inr (by congr)

def contributionCapacityFirstSourceEntryIndex
    (rooted : RootedFailure) :
    (contributionCapacityCutInitialLedger rooted).Entry → Fin 2
  | ⟨_, .inl _⟩ => ⟨0, by decide⟩
  | ⟨_, .inr _⟩ => ⟨1, by decide⟩

def contributionCapacityFirstTargetEntryIndex
    (rooted : RootedFailure) :
    (contributionCapacityCutTargetLedger rooted).Entry → Fin 2
  | ⟨_, .inl _⟩ => ⟨0, by decide⟩
  | ⟨_, .inr _⟩ => ⟨1, by decide⟩

theorem contributionCapacityFirstSourceEntryAt_index
    (rooted : RootedFailure)
    (entry : (contributionCapacityCutInitialLedger rooted).Entry) :
    contributionCapacityFirstSourceEntryAt rooted
        (contributionCapacityFirstSourceEntryIndex rooted entry) = entry := by
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

theorem contributionCapacityFirstTargetEntryAt_index
    (rooted : RootedFailure)
    (entry : (contributionCapacityCutTargetLedger rooted).Entry) :
    contributionCapacityFirstTargetEntryAt rooted
        (contributionCapacityFirstTargetEntryIndex rooted entry) = entry := by
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

def contributionCapacityFirstPatch
    (rooted : RootedFailure)
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        0) :
    FiniteGeneratedLedgerWritePatchAt
      (contributionCapacityCutWriteRowSource rooted) occurrence
      (contributionCapacityCutTargetLedger rooted) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact .complete
    (contributionCapacityFirstRows rooted
      ⟨contributionCapacityCutInitialSupport rooted, event⟩)
    { destinationIndex := contributionCapacityFirstSourceEntryIndex rooted
      originIndex := contributionCapacityFirstTargetEntryIndex rooted
      destination_sound := contributionCapacityFirstSourceEntryAt_index rooted
      origin_sound := contributionCapacityFirstTargetEntryAt_index rooted }

def contributionCapacityFirstEvolution
    (rooted : RootedFailure)
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        0) :
    LedgerWriteEvolutionAt (CutN rooted)
      (contributionCapacityCutInitialLedger rooted)
      (contributionCapacityCutTargetLedger rooted) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact (contributionCapacityFirstPatch rooted
    ⟨contributionCapacityCutInitialSupport rooted, event⟩
    ).toLedgerWriteEvolution

@[simp] theorem contributionCapacityFirst_destination_contribution
    (rooted : RootedFailure)
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        0) :
    ((contributionCapacityFirstEvolution rooted occurrence).destination
      (initialContribution rooted)).1 =
        contributionCapacityCutTargetContribution rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

@[simp] theorem contributionCapacityFirst_destination_obstruction
    (rooted : RootedFailure)
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        0) :
    ((contributionCapacityFirstEvolution rooted occurrence).destination
      (initialObstruction rooted)).1 =
        contributionCapacityCutTargetObstruction rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

@[simp] theorem contributionCapacityFirst_origin_contribution
    (rooted : RootedFailure)
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        0) :
    ((contributionCapacityFirstEvolution rooted occurrence).origin
      (contributionCapacityCutTargetContribution rooted)).1 =
        initialContribution rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

@[simp] theorem contributionCapacityFirst_origin_obstruction
    (rooted : RootedFailure)
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        0) :
    ((contributionCapacityFirstEvolution rooted occurrence).origin
      (contributionCapacityCutTargetObstruction rooted)).1 =
        initialObstruction rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

/-! ## Whole-ledger compiler -/

def contributionCapacityCutLedgerCompiler (rooted : RootedFailure) :
    SourceNativeLedgerCompiler (contributionCapacityCutSource rooted) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := ContributionCapacityCutExactTransitionAt rooted
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
  writeRowSource := contributionCapacityCutWriteRowSource rooted
  terminalRowSource := LedgerTerminalRowSourceAt.empty
    (contributionCapacityCutSource rooted)
  compile := by
    intro current occurrence
    cases current with
    | zero =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact .nativeWrite () rfl (contributionCapacityCutEmitted rooted 1)
          (contributionCapacityFirstEvolution rooted
            ⟨contributionCapacityCutInitialSupport rooted, event⟩)
    | succ current =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact .nativeWrite () rfl
          (contributionCapacityCutEmitted rooted (Nat.succ current + 1))
          ((FiniteGeneratedLedgerWritePatchAt.identity
            (contributionCapacityCutWriteRowSource rooted)
              ⟨contributionCapacityCutTargetSupport rooted, event⟩
            ).toLedgerWriteEvolution)
  compilePatch := by
    intro current occurrence
    cases current with
    | zero =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact ⟨contributionCapacityFirstPatch rooted
          ⟨contributionCapacityCutInitialSupport rooted, event⟩, rfl⟩
    | succ current =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact ⟨FiniteGeneratedLedgerWritePatchAt.identity
          (contributionCapacityCutWriteRowSource rooted)
            ⟨contributionCapacityCutTargetSupport rooted, event⟩, rfl⟩

theorem contributionCapacityCutCompiler_firstWrite_exact
    (rooted : RootedFailure) :
    (contributionCapacityCutLedgerCompiler rooted).compile
        (contributionCapacityCutEmitted rooted 0) =
      .nativeWrite () rfl (contributionCapacityCutEmitted rooted 1)
        (contributionCapacityFirstEvolution rooted
          (contributionCapacityCutEmitted rooted 0)) :=
  rfl

def contributionCapacityCutFirstSuccessor
    (rooted : RootedFailure) :
    SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityCutEmitted rooted 0)
      ((contributionCapacityCutLedgerCompiler rooted).compile
        (contributionCapacityCutEmitted rooted 0)) :=
  PUnit.unit

theorem contributionCapacityCutCompiler_commutes
    (rooted : RootedFailure)
    (current : (TargetV rooted).Current) :
    SourceNativeLedgerEvolutionAt.CommutesWith
      (contributionCapacityCutEmitted rooted)
      ((contributionCapacityCutLedgerCompiler rooted).compile
        (contributionCapacityCutEmitted rooted current)) := by
  cases current with
  | zero => rfl
  | succ current => rfl

end
end M14SourceGeneratedContributionCapacityCutCompiler
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutCompiler.contributionCapacityStrictDebit
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutCompiler.contributionCapacityFirstEvolution
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutCompiler.contributionCapacityCutLedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutCompiler.contributionCapacityCutCompiler_commutes
