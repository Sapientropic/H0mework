import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.World.SourceGeneratedContributionCapacityJointSettlementWorld
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Handoff.Compiler.SourceGeneratedContributionCapacitySettlementSurvivorCompiler

/-!
# Post-settlement renewal compiler

The unique empty support has no live debt, but it is not a terminal world.
Every current generates a fresh canonical actual-service exit occurrence and a
native successor.  Its whole-ledger write is the canonical identity patch on
the empty complete ledger, so no row, receipt, registry, or completed schedule
is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14UBIPeriodicActualServiceCapacity

def contributionCapacityPostSettlementRenewalInitialCurrentAt
    (sourceIndex : Nat) : Nat :=
  contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex + 5

@[simp] theorem contributionCapacityPostSettlementRenewalInitialCurrentAt_one :
    contributionCapacityPostSettlementRenewalInitialCurrentAt 1 = 15 :=
  rfl

/-- The actual-service witness is the source write that pays this whole-ledger
transition.  It remains a proposition and stores no completed service. -/
abbrev ContributionCapacityPostSettlementExactWholeLedgerPaymentAt
    (current : Nat) :=
  PLift (Nonempty (PeriodicActualServiceExitAt current))

/-- The next current is computed only from the indexed payment write. -/
def contributionCapacityPostSettlementNextPaidBy
    {current : Nat}
    (_payment :
      ContributionCapacityPostSettlementExactWholeLedgerPaymentAt current) :
    Nat :=
  current + 1

def contributionCapacityPostSettlementRenewalVocabulary
    (oldVisit : OldVisit) : ConstructiveRoot.Vocabulary where
  Current := Nat
  Anchor := (JointSettlementNAt oldVisit).Anchor
  Incidence := (JointSettlementNAt oldVisit).Incidence
  Lineage := (JointSettlementNAt oldVisit).Lineage
  anchorAt := fun _ => (JointSettlementNAt oldVisit).anchorAt
    (contributionCapacityJointSettlementEmptySupport oldVisit)
  incidenceAt := fun _ => (JointSettlementNAt oldVisit).incidenceAt
    (contributionCapacityJointSettlementEmptySupport oldVisit)
  lineageAt := fun _ => (JointSettlementNAt oldVisit).lineageAt
    (contributionCapacityJointSettlementEmptySupport oldVisit)
  NativeWriteAt :=
    ContributionCapacityPostSettlementExactWholeLedgerPaymentAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := contributionCapacityPostSettlementNextPaidBy
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev PostSettlementRenewalVAt (oldVisit : OldVisit) :=
  contributionCapacityPostSettlementRenewalVocabulary oldVisit

structure SourceGeneratedContributionCapacityPostSettlementRenewalEventAt
    (oldVisit : OldVisit) (current : Nat)
    (support : (JointSettlementNAt oldVisit).Support) : Type where
  private mk ::
  supportExact : PLift
    (support = contributionCapacityJointSettlementEmptySupport oldVisit)
  periodicExitGenerated : Nonempty (PeriodicActualServiceExitAt current)

def contributionCapacityPostSettlementEmptyInventoryPresentation
    (oldVisit : OldVisit) :
    ConstructivePresentation PEmpty
      (OpenResponsibilityAt (JointSettlementNAt oldVisit)
        (contributionCapacityJointSettlementEmptySupport oldVisit)) where
  forward := PEmpty.elim
  backward := fun entry => nomatch entry.2
  backward_forward := fun value => nomatch value
  forward_backward := fun entry => nomatch entry.2

def contributionCapacityPostSettlementRenewalEventLaw
    (oldVisit : OldVisit) :
    SourceNativeEventAlgebra (JointSettlementNAt oldVisit)
      (PostSettlementRenewalVAt oldVisit) where
  EventAt := SourceGeneratedContributionCapacityPostSettlementRenewalEventAt
    oldVisit
  compile := fun event =>
    .nativeWrite (PLift.up event.periodicExitGenerated)
  AffectedInventoryAt := fun _ => PEmpty
  affectedInventoryPresentation := by
    intro current support event
    cases event.supportExact.down
    exact contributionCapacityPostSettlementEmptyInventoryPresentation oldVisit
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

def contributionCapacityPostSettlementRenewalSource
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeSource (JointSettlementNAt oldVisit)
      (PostSettlementRenewalVAt oldVisit) where
  initial := contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex
  law := contributionCapacityPostSettlementRenewalEventLaw oldVisit

def contributionCapacityPostSettlementRenewalEmitted
    (oldVisit : OldVisit) (sourceIndex current : Nat) :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
      |>.toRootSource.actual.OccurrenceAt current :=
  ⟨contributionCapacityJointSettlementEmptySupport oldVisit,
    { supportExact := PLift.up rfl
      periodicExitGenerated := ⟨periodicActualServiceExitAt current⟩ }⟩

theorem contributionCapacityPostSettlementRenewalOccurrence_eq_emitted
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : Nat}
    (occurrence :
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
        |>.toRootSource.actual.OccurrenceAt current) :
    occurrence = contributionCapacityPostSettlementRenewalEmitted oldVisit
      sourceIndex current := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  cases event
  rfl

def ContributionCapacityPostSettlementRenewalExactTransitionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    {current : Nat} →
    (occurrence :
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
        |>.toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (JointSettlementNAt oldVisit).Support} →
    OpenResponsibilityAt (JointSettlementNAt oldVisit) occurrence.1 →
    OpenResponsibilityAt (JointSettlementNAt oldVisit) targetSupport → Type :=
  fun {_} _ {_} _ _ => PEmpty

def contributionCapacityPostSettlementRenewalWriteRowSource
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    LedgerWriteRowSourceAt
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
      (ContributionCapacityPostSettlementRenewalExactTransitionAt oldVisit
        sourceIndex) :=
  LedgerWriteRowSourceAt.empty
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
    (ContributionCapacityPostSettlementRenewalExactTransitionAt oldVisit
      sourceIndex)

def contributionCapacityPostSettlementRenewalPatch
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : Nat}
    (occurrence :
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
        |>.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt
      (contributionCapacityPostSettlementRenewalWriteRowSource oldVisit
        sourceIndex) occurrence
      (contributionCapacityJointSettlementEmptyLedger oldVisit) := by
  rw [contributionCapacityPostSettlementRenewalOccurrence_eq_emitted oldVisit
    sourceIndex occurrence]
  exact FiniteGeneratedLedgerWritePatchAt.identity
    (contributionCapacityPostSettlementRenewalWriteRowSource oldVisit sourceIndex)
    (contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex current)

def contributionCapacityPostSettlementRenewalEvolution
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : Nat}
    (occurrence :
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
        |>.toRootSource.actual.OccurrenceAt current) :
    LedgerWriteEvolutionAt (JointSettlementNAt oldVisit)
      (contributionCapacityJointSettlementEmptyLedger oldVisit)
      (contributionCapacityJointSettlementEmptyLedger oldVisit) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact (contributionCapacityPostSettlementRenewalPatch oldVisit sourceIndex
    (contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
      current)).toLedgerWriteEvolution

def contributionCapacityPostSettlementRenewalLedgerCompiler
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeLedgerCompiler
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex) where
  IncidenceTransitionAt := fun _ _ _ => PEmpty
  ExactTransitionAt :=
    ContributionCapacityPostSettlementRenewalExactTransitionAt oldVisit
      sourceIndex
  exact_incidence := fun exact => nomatch exact
  exact_lineage := fun exact => nomatch exact
  writeRowSource := contributionCapacityPostSettlementRenewalWriteRowSource
    oldVisit sourceIndex
  terminalRowSource := LedgerTerminalRowSourceAt.empty
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
  compile := by
    intro current occurrence
    rw [contributionCapacityPostSettlementRenewalOccurrence_eq_emitted oldVisit
      sourceIndex occurrence]
    exact .nativeWrite
      (PLift.up
        (contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (show Nat from current)).2.periodicExitGenerated) rfl
      (contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        ((show Nat from current) + 1))
      (contributionCapacityPostSettlementRenewalEvolution oldVisit sourceIndex
        (contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (show Nat from current)))
  compilePatch := by
    intro current occurrence
    rw [contributionCapacityPostSettlementRenewalOccurrence_eq_emitted oldVisit
      sourceIndex occurrence]
    exact ⟨contributionCapacityPostSettlementRenewalPatch oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (show Nat from current)), rfl⟩

def contributionCapacityPostSettlementRenewalRestructuringLaw
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeLedgerRestructuringLaw
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex) where
  vocabulary := contributionCapacityReopeningRestructuringVocabulary oldVisit
  sourceEventAt := fun _ =>
    ((contributionCapacitySettlementSurvivorSupport oldVisit).1,
      exactSourceGeneratedLossAllocationMaterialWitness)
  obligationAt := by
    intro current occurrence support entry
    cases support with
    | inl oldSupport =>
        exact contributionCapacityU8ObligationAt oldVisit
          exactSourceGeneratedLossAllocationMaterialWitness
          (⟨entry.1, entry.2⟩ : OpenResponsibilityAt
            (CapacityU8NAt oldVisit) oldSupport.1)
    | inr emptyUnit => cases emptyUnit; exact nomatch entry.2
  responsibilityKey := AdmittedObligation.content
  anchorKey := fun _ => ()
  incidenceKey := id
  lineageKey := id
  responsibility_commutes := by
    intro current occurrence support entry
    cases support with
    | inl oldSupport => rfl
    | inr emptyUnit => cases emptyUnit; exact nomatch entry.2
  anchor_commutes := by
    intro current occurrence support entry
    cases support with
    | inl oldSupport => rfl
    | inr emptyUnit => cases emptyUnit; exact nomatch entry.2
  incidence_commutes := by
    intro current occurrence support entry
    cases support with
    | inl oldSupport => rfl
    | inr emptyUnit => cases emptyUnit; exact nomatch entry.2
  lineage_commutes := by
    intro current occurrence support entry
    cases support with
    | inl oldSupport => rfl
    | inr emptyUnit => cases emptyUnit; exact nomatch entry.2
  obligationAt_injective := by
    intro current occurrence support left right equality
    cases support with
    | inl oldSupport =>
        exact contributionCapacityU8ObligationAt_injective oldVisit
          exactSourceGeneratedLossAllocationMaterialWitness equality
    | inr emptyUnit => cases emptyUnit; exact nomatch left.2

def contributionCapacityPostSettlementRenewalRestructuringCertification
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : Nat}
    (occurrence :
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
        |>.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (contributionCapacityPostSettlementRenewalRestructuringLaw oldVisit
        sourceIndex)
      ((contributionCapacityPostSettlementRenewalLedgerCompiler oldVisit
        sourceIndex).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left _right _equality => nomatch left.2)
    (fun left _right _equality => nomatch left.2)

def contributionCapacityPostSettlementRenewalRestructuringCompiler
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeRestructuringLedgerCompiler
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex) where
  ledgerCompiler := contributionCapacityPostSettlementRenewalLedgerCompiler
    oldVisit sourceIndex
  restructuringLaw := contributionCapacityPostSettlementRenewalRestructuringLaw
    oldVisit sourceIndex
  certifyRestructuring :=
    contributionCapacityPostSettlementRenewalRestructuringCertification oldVisit
      sourceIndex

def contributionCapacityPostSettlementRenewalRestructuringSource
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeRestructuringLedgerSource (JointSettlementNAt oldVisit)
      (PostSettlementRenewalVAt oldVisit) where
  source := contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
  compiler := contributionCapacityPostSettlementRenewalRestructuringCompiler
    oldVisit sourceIndex

end
end M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler.contributionCapacityPostSettlementRenewalLedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler.contributionCapacityPostSettlementRenewalRestructuringSource
