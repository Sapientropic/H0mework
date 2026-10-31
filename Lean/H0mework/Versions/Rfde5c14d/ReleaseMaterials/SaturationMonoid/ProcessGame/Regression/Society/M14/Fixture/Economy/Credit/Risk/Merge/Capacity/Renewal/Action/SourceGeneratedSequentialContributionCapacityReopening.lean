import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Action.SourceGeneratedContributionCapacityReopeningActionSource

/-!
# Source-generated sequential capacity reopening

The zero-field action seal consumes the exact generated residual occurrence.
Its fixed program derives a periodic actual-service UBI occurrence from the
source index, transports the unchanged three-row ledger, and exposes positive
actionable-exit capacity in the receipt while every progress-budget row stays
zero.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialContributionCapacityReopening

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open RootInquiryCompletion.NoFreeCapacityRestoration
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityFailure
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityNoFreeRestoration
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningActionSource
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity

structure ExactContributionCapacityReopeningReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (_answer : PUnit) : Type 3 where
  sourceEventExact : sourceEvent =
    contributionCapacityReopeningActionExactSourceEventAt oldVisit sourceIndex
  sourceResidualExact :
    contributionCapacityReopeningActionSourceEntryAt oldVisit sourceIndex =
      contributionCapacityU8GeneratedResidual oldVisit
  periodicActualExitGenerated : Nonempty (PeriodicActualServiceExitAt
    (contributionCapacityReopeningDepthAt sourceIndex))
  actionableRenewalGenerated : Nonempty
    (geometryCompilerAt
      (contributionCapacityReopeningDepthAt sourceIndex)).SourceGeneratedActionableExitRenewalAt
  actionableExitCapacityOne :
    (geometryCompilerAt
      (contributionCapacityReopeningDepthAt sourceIndex)).actionableExitCapacity = 1
  capturedExitCapacityZero :
    (capturedGeometryCompilerAt
      (contributionCapacityReopeningDepthAt sourceIndex)).actionableExitCapacity = 0
  targetLedgerAllZero :
    (entry : (contributionCapacityReopeningTargetLedger oldVisit).Entry) →
      entry.progressBudget = 0
  targetLedgerHasNoPositiveProgress :
    IsEmpty (PositiveProgressEntryAt
      (contributionCapacityReopeningTargetLedger oldVisit))
  exhaustedRootCannotSelfRefill :
    NoEndogenousPositiveRestorationAt oldVisit
  generatedResidualUsesExistingBearer :
    contributionCapacityU8BearerAt oldVisit
        exactSourceGeneratedLossAllocationMaterialWitness
        (contributionCapacityU8GeneratedResidual oldVisit) =
      sourceGeneratedLossAllocationMaterial.parentBearer

/-- Payment existence is a projection of the receipt's one actual-service
authority; it is not an independently stored existential. -/
theorem ExactContributionCapacityReopeningReceiptAt.periodicPaymentGenerated
    {oldVisit : OldVisit} {sourceIndex : Nat}
    {sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex}
    {answer : PUnit}
    (receipt : ExactContributionCapacityReopeningReceiptAt oldVisit sourceIndex
      sourceEvent answer) :
    Nonempty (PeriodicSourceBackedPaymentAt
      (contributionCapacityReopeningDepthAt sourceIndex)) := by
  rcases receipt.periodicActualExitGenerated with ⟨actualExit⟩
  exact ⟨actualExit.paymentOccurrence⟩

def exactContributionCapacityReopeningReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (answer : PUnit) :
    ExactContributionCapacityReopeningReceiptAt oldVisit sourceIndex
      sourceEvent answer := by
  rw [sourceEvent.eq_generated]
  exact
    { sourceEventExact := rfl
      sourceResidualExact := rfl
      periodicActualExitGenerated :=
        ⟨contributionCapacityReopeningPeriodicExitAt sourceIndex 0⟩
      actionableRenewalGenerated :=
        ⟨actionableExitRenewalAt
          (contributionCapacityReopeningDepthAt sourceIndex)⟩
      actionableExitCapacityOne := actionableExitCapacity_eq_one_at
        (contributionCapacityReopeningDepthAt sourceIndex)
      capturedExitCapacityZero := captured_nominal_capacity_eq_zero_at
        (contributionCapacityReopeningDepthAt sourceIndex)
      targetLedgerAllZero :=
        contributionCapacityReopeningTargetEntry_budget_zero oldVisit
      targetLedgerHasNoPositiveProgress :=
        positiveProgressEntry_isEmpty_of_all_zero _
          (contributionCapacityReopeningTargetEntry_budget_zero oldVisit)
      exhaustedRootCannotSelfRefill :=
        contributionCapacityU8_noEndogenousPositiveRestoration oldVisit
      generatedResidualUsesExistingBearer :=
        contributionCapacityU8_generatedBearer_is_existingParent oldVisit }

def contributionCapacityReopeningActionTargetAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (exactSource : ReopeningSourceEventAt oldVisit sourceIndex) :
    SourceNativeSequentialActualActionTargetAt
      (contributionCapacityReopeningActionSourceRootAt oldVisit)
      (contributionCapacityReopeningActionSourceVisitAt oldVisit sourceIndex)
      exactSource
      (contributionCapacityReopeningActionSourceEntryAt oldVisit sourceIndex)
      (contributionCapacityReopeningActionSourceAuthorityAt oldVisit
        sourceIndex) := by
  rw [exactSource.eq_generated]
  exact
    { TargetN := ReopeningNAt oldVisit
      translation := contributionCapacityReopeningTranslation oldVisit
      TargetV := ReopeningVAt oldVisit sourceIndex
      targetRoot := contributionCapacityReopeningLivingRoot oldVisit sourceIndex
        (contributionCapacityReopeningActionExactSourceEventAt oldVisit
          sourceIndex)
      targetTheory := contributionCapacityReopeningTheory oldVisit
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic :=
        { compile := id
          commuting := fun _ => rfl }
      occurrencePresentation :=
        contributionCapacityReopeningActionOccurrencePresentationAt oldVisit
          sourceIndex
      occurrence_commutes :=
        contributionCapacityReopeningActionOccurrence_commutes oldVisit
          sourceIndex
      initialSupport_heq := HEq.rfl
      initialOpenLedger :=
        (contributionCapacityReopeningTranslation oldVisit).oldOpenLedger
          (CapacityCofaceAt oldVisit).cofaceSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := by
        intro targetEntry
        exact ⟨⟨⟨targetEntry.1, targetEntry.2⟩, PLift.up rfl⟩⟩
      translatedSourceEntryRow :=
        contributionCapacityReopeningInitialResidualRow oldVisit sourceIndex
          (contributionCapacityReopeningActionExactSourceEventAt oldVisit
            sourceIndex)
      firstSuccessor :=
        contributionCapacityReopeningFirstSuccessor oldVisit sourceIndex
          (contributionCapacityReopeningActionExactSourceEventAt oldVisit
            sourceIndex)
      canonical_targetNextVisit_eq := rfl
      Answer := PUnit
      answer := PUnit.unit
      Receipt := fun answer => ExactContributionCapacityReopeningReceiptAt
        oldVisit sourceIndex
          (contributionCapacityReopeningActionExactSourceEventAt oldVisit
            sourceIndex) answer
      receipt := exactContributionCapacityReopeningReceiptAt oldVisit
        sourceIndex
        (contributionCapacityReopeningActionExactSourceEventAt oldVisit
          sourceIndex) PUnit.unit }

def contributionCapacityReopeningActionProgramAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeSequentialActualActionProgramAt
      (contributionCapacityReopeningActionSourceRootAt oldVisit)
      (contributionCapacityReopeningActionSourceVisitAt oldVisit sourceIndex)
      (contributionCapacityReopeningActionSourceEntryAt oldVisit sourceIndex)
      (contributionCapacityReopeningActionSourceAuthorityAt oldVisit
        sourceIndex) where
  targetAt := contributionCapacityReopeningActionTargetAt oldVisit sourceIndex

def generatedContributionCapacityReopeningActionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedSequentialActualActionAt
      (contributionCapacityReopeningActionProgramAt oldVisit sourceIndex)
      (contributionCapacityReopeningActionExactSourceEventAt oldVisit
        sourceIndex) :=
  (contributionCapacityReopeningActionProgramAt oldVisit sourceIndex).generate
    (contributionCapacityReopeningActionExactSourceEventAt oldVisit sourceIndex)

def contributionCapacityReopeningActionCompilationAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (exactSource : ReopeningSourceEventAt oldVisit sourceIndex) :
    SourceNativeInquiryCompilationAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8RuntimeVisitAt oldVisit sourceIndex)
      (contributionCapacityRevisedU7 oldVisit)
      (contributionCapacityRevisedCalculus oldVisit)
      (contributionCapacityRevisedTheory oldVisit) ()
      (contributionCapacityU8InquiryEventAt oldVisit sourceIndex)
      (contributionCapacityU8GeneratedResidual oldVisit)
      (contributionCapacityU8RuntimeAuthorityAt oldVisit sourceIndex) :=
  .actualAction
    ((contributionCapacityReopeningActionProgramAt oldVisit sourceIndex).generate
      exactSource)

def contributionCapacityReopeningActionCompilationProgramAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeInquiryCompilationProgramAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8RuntimeVisitAt oldVisit sourceIndex)
      (contributionCapacityRevisedU7 oldVisit)
      (contributionCapacityRevisedCalculus oldVisit)
      (contributionCapacityRevisedTheory oldVisit) ()
      (contributionCapacityU8InquiryEventAt oldVisit sourceIndex)
      (contributionCapacityU8GeneratedResidual oldVisit)
      (contributionCapacityU8RuntimeAuthorityAt oldVisit sourceIndex) where
  compile := contributionCapacityReopeningActionCompilationAt oldVisit
    sourceIndex

@[simp] theorem generatedContributionCapacityReopening_targetRoot_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (generatedContributionCapacityReopeningActionAt oldVisit sourceIndex).target.targetRoot =
      contributionCapacityReopeningLivingRoot oldVisit sourceIndex
        (contributionCapacityReopeningActionExactSourceEventAt oldVisit
          sourceIndex) :=
  rfl

theorem generatedContributionCapacityReopening_macroNext_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (generatedContributionCapacityReopeningActionAt oldVisit sourceIndex).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedContributionCapacityReopeningActionAt oldVisit sourceIndex).target.TargetV,
        (generatedContributionCapacityReopeningActionAt oldVisit sourceIndex).target.targetRoot.toAuthoritativeRoot,
        (generatedContributionCapacityReopeningActionAt oldVisit sourceIndex).target.targetVisit⟩ :=
  SourceNativeSequentialActualActionTargetAt.targetAnswerAndNext_next_eq
    (generatedContributionCapacityReopeningActionAt oldVisit sourceIndex).target

end
end M14SourceGeneratedSequentialContributionCapacityReopening
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacityReopening.generatedContributionCapacityReopeningActionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacityReopening.generatedContributionCapacityReopening_macroNext_exact
