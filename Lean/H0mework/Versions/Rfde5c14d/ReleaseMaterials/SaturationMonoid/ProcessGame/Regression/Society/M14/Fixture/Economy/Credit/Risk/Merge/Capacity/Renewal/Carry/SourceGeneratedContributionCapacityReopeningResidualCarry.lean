import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Compiler.SourceGeneratedContributionCapacityReopeningCompiler

/-!
# Source-generated reopening residual carry

Each positive reopening current consumes the authoritative compiler row of
the already live generated residual.  The root's complete three-row patch
selects an exact `.carried` evolution while the same emitted occurrence
generates a fresh periodic actual-service exit.  This is a dependent readout
of the one root ledger: no lifecycle vocabulary, admission, process, state,
receipt registry or parallel ledger is constructed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityReopeningResidualCarry

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14UBIPeriodicActualServiceCapacity

abbrev ReopeningResidualCarryOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (index : Nat) :=
  (contributionCapacityReopeningSource oldVisit sourceIndex sourceEvent)
    |>.toRootSource.actual.OccurrenceAt (index + 1)

def reopeningResidualCarryOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (index : Nat) :
    ReopeningResidualCarryOccurrenceAt oldVisit sourceIndex sourceEvent index :=
  contributionCapacityReopeningEmitted oldVisit sourceIndex sourceEvent
    (index + 1)

def reopeningResidualCarrySourceEntryAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (index : Nat) :
    OpenResponsibilityAt (ReopeningNAt oldVisit)
      (reopeningResidualCarryOccurrenceAt oldVisit sourceIndex sourceEvent
        index).1 :=
  contributionCapacityReopeningResidualEntryAt oldVisit true

def reopeningResidualCarryTargetEntryAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (index : Nat) :
    OpenResponsibilityAt (ReopeningNAt oldVisit)
      (contributionCapacityReopeningEmitted oldVisit sourceIndex sourceEvent
        (index + 2)).1 :=
  contributionCapacityReopeningResidualEntryAt oldVisit true

def reopeningResidualCarryEvolutionAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (index : Nat) :
    LedgerEntryEvolutionAt (ReopeningNAt oldVisit)
      (reopeningResidualCarrySourceEntryAt oldVisit sourceIndex sourceEvent
        index)
      (reopeningResidualCarryTargetEntryAt oldVisit sourceIndex sourceEvent
        index) :=
  .carried rfl HEq.rfl

def reopeningResidualCarryWholeEvolutionAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (index : Nat) :=
  contributionCapacityReopeningEvolution oldVisit sourceIndex sourceEvent
    (reopeningResidualCarryOccurrenceAt oldVisit sourceIndex sourceEvent index)

theorem reopeningResidualCarry_foldDestination_exact
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (index : Nat) :
    (reopeningResidualCarryWholeEvolutionAt oldVisit sourceIndex sourceEvent
      index).destination
        (reopeningResidualCarrySourceEntryAt oldVisit sourceIndex sourceEvent
          index) =
      ⟨reopeningResidualCarryTargetEntryAt oldVisit sourceIndex sourceEvent
          index,
        reopeningResidualCarryEvolutionAt oldVisit sourceIndex sourceEvent
          index⟩ := by
  rfl

theorem reopeningResidualCarry_compilerDisposition_exact
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (index : Nat) :
    ((contributionCapacityReopeningLedgerCompiler oldVisit sourceIndex
        sourceEvent).compile
      (reopeningResidualCarryOccurrenceAt oldVisit sourceIndex sourceEvent
        index)).entryDisposition
      (reopeningResidualCarrySourceEntryAt oldVisit sourceIndex sourceEvent
        index) =
      .evolved (reopeningResidualCarryEvolutionAt oldVisit sourceIndex
        sourceEvent index) := by
  rfl

/-- Zero-field authority token.  All data are recomputed from the fixed root
compiler and its exact emitted occurrence. -/
inductive SourceGeneratedReopeningResidualCarryAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (index : Nat) : Type where
  | private generated

namespace SourceGeneratedReopeningResidualCarryAt

def generate
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex)
    (index : Nat) :
    SourceGeneratedReopeningResidualCarryAt oldVisit sourceIndex sourceEvent
      index :=
  .generated

variable
    {oldVisit : OldVisit} {sourceIndex : Nat}
    {sourceEvent : ReopeningSourceEventAt oldVisit sourceIndex}
    {index : Nat}
    (carry : SourceGeneratedReopeningResidualCarryAt oldVisit sourceIndex
      sourceEvent index)

theorem eq_generate :
    carry = generate oldVisit sourceIndex sourceEvent index := by
  cases carry
  rfl

def sourceOccurrence :
    ReopeningResidualCarryOccurrenceAt oldVisit sourceIndex sourceEvent
      index := by
  cases carry
  exact reopeningResidualCarryOccurrenceAt oldVisit sourceIndex sourceEvent
    index

def sourceEntry : OpenResponsibilityAt (ReopeningNAt oldVisit)
    carry.sourceOccurrence.1 := by
  cases carry
  exact reopeningResidualCarrySourceEntryAt oldVisit sourceIndex sourceEvent
    index

def targetEntry : OpenResponsibilityAt (ReopeningNAt oldVisit)
    (contributionCapacityReopeningEmitted oldVisit sourceIndex sourceEvent
      (index + 2)).1 := by
  cases carry
  exact reopeningResidualCarryTargetEntryAt oldVisit sourceIndex sourceEvent
    index

def evolution : LedgerEntryEvolutionAt (ReopeningNAt oldVisit)
    carry.sourceEntry carry.targetEntry := by
  cases carry
  exact reopeningResidualCarryEvolutionAt oldVisit sourceIndex sourceEvent
    index

theorem compilerDisposition_exact :
    ((contributionCapacityReopeningLedgerCompiler oldVisit sourceIndex
        sourceEvent).compile carry.sourceOccurrence).entryDisposition
      carry.sourceEntry = .evolved carry.evolution := by
  cases carry
  exact reopeningResidualCarry_compilerDisposition_exact oldVisit sourceIndex
    sourceEvent index

theorem foldDestination_exact :
    (reopeningResidualCarryWholeEvolutionAt oldVisit sourceIndex sourceEvent
      index).destination carry.sourceEntry =
      ⟨carry.targetEntry, carry.evolution⟩ := by
  cases carry
  exact reopeningResidualCarry_foldDestination_exact oldVisit sourceIndex
    sourceEvent index

theorem sourceEntry_budget_zero : carry.sourceEntry.progressBudget = 0 := by
  cases carry
  exact contributionCapacityReopeningTargetEntry_budget_zero oldVisit
    (reopeningResidualCarrySourceEntryAt oldVisit sourceIndex sourceEvent index)

theorem targetEntry_budget_zero : carry.targetEntry.progressBudget = 0 := by
  cases carry
  exact contributionCapacityReopeningTargetEntry_budget_zero oldVisit
    (reopeningResidualCarryTargetEntryAt oldVisit sourceIndex sourceEvent index)

theorem lineage_preserved :
    (ReopeningNAt oldVisit).lineageAt carry.sourceOccurrence.1 =
      (ReopeningNAt oldVisit).lineageAt
        (contributionCapacityReopeningEmitted oldVisit sourceIndex sourceEvent
          (index + 2)).1 := by
  cases carry
  rfl

theorem claim_preserved : carry.sourceEntry.claim = carry.targetEntry.claim := by
  cases carry
  rfl

theorem residual_bearer_is_existing_parent :
    contributionCapacityU8BearerAt oldVisit
        exactSourceGeneratedLossAllocationMaterialWitness
        (contributionCapacityU8GeneratedResidual oldVisit) =
      sourceGeneratedLossAllocationMaterial.parentBearer :=
  contributionCapacityU8_generatedBearer_is_existingParent oldVisit

theorem actualRenewal
    (_carry : SourceGeneratedReopeningResidualCarryAt oldVisit sourceIndex
      sourceEvent index) :
    Nonempty (PeriodicActualServiceExitAt
      (contributionCapacityReopeningDepthAtCurrent sourceIndex (index + 1))) :=
  (reopeningResidualCarryOccurrenceAt oldVisit sourceIndex sourceEvent
    index).2.periodicExitGenerated

end SourceGeneratedReopeningResidualCarryAt

end
end M14SourceGeneratedContributionCapacityReopeningResidualCarry
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningResidualCarry.SourceGeneratedReopeningResidualCarryAt.compilerDisposition_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningResidualCarry.SourceGeneratedReopeningResidualCarryAt.foldDestination_exact
