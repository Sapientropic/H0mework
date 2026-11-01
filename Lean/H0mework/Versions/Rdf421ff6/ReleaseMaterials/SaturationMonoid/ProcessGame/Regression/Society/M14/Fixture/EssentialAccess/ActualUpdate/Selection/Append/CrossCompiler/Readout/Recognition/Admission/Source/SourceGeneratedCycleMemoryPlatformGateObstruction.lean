import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Source.SourceGeneratedActualRelationCycleMemoryWitnessPublication
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Recurrence.SourceGeneratedCrossCompilerRelationAppendUBI
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Channel.Carrier.Producer.SourceGeneratedContributionCapacityEssentialAccessChannel

/-!
# Cycle-memory obstruction to the existing paid channel representation

The unique cross runtime cofinally regenerates the platform relation.  The
existing paid essential-access carrier has only the previously generated
tenure and health channels, so no value of that carrier can represent the
platform seed.  The obstruction is source-positive: at every requested finite
boundary it produces a later same-runtime cycle-memory witness, preserves UBI,
and derives the empty old representation fibre.

`platformCycleBaseAfter` is a proof-side index calculated from the already
proved period-three recurrence.  It is not stored in a current, used to choose
an event, or installed as a future schedule.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCycleMemoryPlatformGateObstruction

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14EssentialAccessRelationFixture
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedLineageFoldRelationRecurrenceStage
open M14SourceGeneratedLineageFoldRelationRecurrenceStage.RelationLineageRecurrenceStage
open M14SourceGeneratedPlatformRetainedRelationAction
open M14SourceGeneratedEssentialAccessCriticalActionCarrier
open M14SourceGeneratedEssentialAccessRelationRenewal
open M14SourceGeneratedCrossCompilerRelationCurrentRecurrence
open M14SourceGeneratedCrossCompilerRelationAppendUBI
open M14SourceGeneratedActualRelationThreeCycle
open M14SourceGeneratedActualRelationCycleMemoryWitnessPublication
open M14ProofCarryingActualRelationCycleReflexiveMemory
open M14SourceGeneratedContributionCapacityEssentialAccessChannel

/-! ## Exact first period and recurrence -/

theorem homogeneousStageOne_actionRoot_platform :
    (stageAt 1).actionCurrent.root = exactEssentialAccessSeed .platform := by
  rw [show (1 : Nat) = 0 + 1 by rfl, stageAt_succ,
    next_actionCurrent_exact]
  change (criticalActionCarrierOfSelected
    (stageAt 0).selected).action.criticalBearer.bearerLineage.seed = _
  rw [(criticalActionCarrierOfSelected_foldProvenance
      (stageAt 0).selected).2.1,
    selectedCriticalSeed_eq_root]
  change platformRetainedRelationPrior.root = _
  rw [platformRetainedRelationPrior_exact]
  rfl

theorem crossCompilerTargetSeed_zero_tenure :
    (crossCompilerCurrentStageAt 0).targetSeed =
      exactEssentialAccessSeed .tenure := by
  let candidate :
      RootedAccountedUnfolding (CrossCompilerAtomAt 0) → ExactRelationSeed :=
    fun current => sourceGeneratedEssentialAccessRenewalSeed
      (crossCompilerAtomSeedAt 0 current.root)
  have generated :=
    crossCompilerCurrentStageAt_seed_fold_unique 0 candidate (by
      intro origin branches
      rfl)
  change (crossCompilerCurrentStageAt 0).targetSeed =
    sourceGeneratedEssentialAccessRenewalSeed
      (crossCompilerCurrentStageAt 0).actionCurrent.root at generated
  have currentRoot :
      (crossCompilerCurrentStageAt 0).actionCurrent.root =
        exactEssentialAccessSeed .platform :=
    (congrArg RootedAccountedUnfolding.root
      crossCompilerCurrentStageAt_zero_actionCurrent).trans
        homogeneousStageOne_actionRoot_platform
  rw [generated, currentRoot]
  exact renewalSeed_platform

theorem crossCompilerTargetSeed_one_health :
    (crossCompilerCurrentStageAt 1).targetSeed =
      exactEssentialAccessSeed .health := by
  rw [show (1 : Nat) = 0 + 1 by rfl,
    crossCompilerCurrentStageAt_targetSeed_succ,
    crossCompilerTargetSeed_zero_tenure]
  exact renewalSeed_tenure

theorem crossCompilerTargetSeed_two_platform :
    (crossCompilerCurrentStageAt 2).targetSeed =
      exactEssentialAccessSeed .platform := by
  rw [show (2 : Nat) = 1 + 1 by rfl,
    crossCompilerCurrentStageAt_targetSeed_succ,
    crossCompilerTargetSeed_one_health]
  exact renewalSeed_health

/-- Readout index of the `cycle`th platform-rooted renewal cycle. -/
def platformCycleBaseAt (cycle : Nat) : Nat :=
  2 + 3 * cycle

theorem platformCycleBaseAt_seed_platform (cycle : Nat) :
    actualRelationSeedAt (platformCycleBaseAt cycle) =
      exactEssentialAccessSeed .platform := by
  induction cycle with
  | zero =>
      simpa [platformCycleBaseAt, actualRelationSeedAt] using
        crossCompilerTargetSeed_two_platform
  | succ cycle ih =>
      have depthExact :
          platformCycleBaseAt (cycle + 1) =
            platformCycleBaseAt cycle + 3 := by
        simp [platformCycleBaseAt]
        omega
      rw [depthExact]
      exact (crossCompilerCurrentStageAt_targetSeed_add_three
        (platformCycleBaseAt cycle)).trans ih

/-- A later platform cycle for every finite observation boundary. -/
def platformCycleBaseAfter (boundary : Nat) : Nat :=
  platformCycleBaseAt (boundary + 1)

theorem platformCycleBaseAfter_later (boundary : Nat) :
    boundary < platformCycleBaseAfter boundary := by
  simp [platformCycleBaseAfter, platformCycleBaseAt]
  omega

theorem platformCycleBaseAfter_seed_platform (boundary : Nat) :
    actualRelationSeedAt (platformCycleBaseAfter boundary) =
      exactEssentialAccessSeed .platform :=
  platformCycleBaseAt_seed_platform (boundary + 1)

/-! ## Exact old-representation obstruction -/

/-- Fibre claiming that the existing paid channel carrier represents an exact
relation seed.  It is a diagnostic restriction, not a new channel registry. -/
abbrev ExistingPaidEssentialAccessChannelRepresentationAt
    (seed : essentialAccessRelationCompiler.ExactRelationSeed) :=
  { channel : EssentialAccessChannel // channelSeed channel = seed }

theorem existingPaidChannel_platformRepresentation_isEmpty :
    IsEmpty (ExistingPaidEssentialAccessChannelRepresentationAt
      (exactEssentialAccessSeed .platform)) :=
  ⟨fun represented => by
    rcases represented with ⟨channel, exactSeed⟩
    cases channel <;>
      have values := congrArg Subtype.val exactSeed <;>
      cases values⟩

/-- Source-positive obstruction at every finite boundary.  It carries the
actual later cycle, canonical memory/recollection witness, exact platform
identity, empty old paid-channel fibre and the inherited UBI outcome. -/
structure SourceGeneratedCycleMemoryPlatformGateObstructionAt
    (boundary : Nat) : Type where
  private mk ::
  cycleBaseLater : boundary < platformCycleBaseAfter boundary
  cycleWitness : SourceGeneratedActualRelationCycleMemoryWitnessAt
    (platformCycleBaseAfter boundary)
    (platformCycleBaseAfter boundary + 3)
  platformSeedExact :
    actualRelationSeedAt (platformCycleBaseAfter boundary) =
      exactEssentialAccessSeed .platform
  oldPaidChannelEmpty :
    IsEmpty (ExistingPaidEssentialAccessChannelRepresentationAt
      (actualRelationSeedAt (platformCycleBaseAfter boundary)))
  inheritedUBI : type_of%
    (crossCompilerUBI_directConsumer
      (platformCycleBaseAfter boundary + 3))

/-- Sole producer.  Its mouth receives only the already observed finite
boundary; the cycle base, event, witness, old-carrier no-go and UBI receipt are
generated internally. -/
def sourceGeneratedCycleMemoryPlatformGateObstructionAt
    (boundary : Nat) :
    SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary where
  cycleBaseLater := platformCycleBaseAfter_later boundary
  cycleWitness := sourceGeneratedActualRelationCycleMemoryWitnessAt
    (platformCycleBaseAfter boundary)
  platformSeedExact := platformCycleBaseAfter_seed_platform boundary
  oldPaidChannelEmpty := by
    rw [platformCycleBaseAfter_seed_platform]
    exact existingPaidChannel_platformRepresentation_isEmpty
  inheritedUBI := crossCompilerUBI_directConsumer _

theorem cycleMemoryPlatformGateObstruction_directConsumer
    (boundary : Nat) :
    Nonempty (SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary) ∧
      boundary < platformCycleBaseAfter boundary ∧
      type_of% (actualRelationThreeCycle_directConsumer
        (platformCycleBaseAfter boundary)) ∧
      type_of% (actualRelationRoleRing_p130_reflexiveMemory
        (platformCycleBaseAfter boundary)) ∧
      actualRelationSeedAt (platformCycleBaseAfter boundary) =
        exactEssentialAccessSeed .platform ∧
      IsEmpty (ExistingPaidEssentialAccessChannelRepresentationAt
        (actualRelationSeedAt (platformCycleBaseAfter boundary))) ∧
      type_of% (crossCompilerUBI_directConsumer
        (platformCycleBaseAfter boundary + 3)) := by
  let generated :=
    sourceGeneratedCycleMemoryPlatformGateObstructionAt boundary
  exact ⟨⟨generated⟩, generated.cycleBaseLater,
    generated.cycleWitness.actualCycle,
    generated.cycleWitness.cycleMemory,
    generated.platformSeedExact,
    generated.oldPaidChannelEmpty,
    generated.inheritedUBI⟩

end
end M14SourceGeneratedCycleMemoryPlatformGateObstruction
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateObstruction.platformCycleBaseAt_seed_platform
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateObstruction.existingPaidChannel_platformRepresentation_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateObstruction.sourceGeneratedCycleMemoryPlatformGateObstructionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateObstruction.cycleMemoryPlatformGateObstruction_directConsumer
