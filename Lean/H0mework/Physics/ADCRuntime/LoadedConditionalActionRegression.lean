import H0mework.Computation.LoadedADCInformation.ConditionalActionMaterial

/-! Actual feedback preserves a nontrivial conditional material fibre even while it changes the command. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.ConditionalAction

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

open SourceOwnedObservationHistory SourceGeneratedRuntimeHistoryProbability

theorem next_image_supported (bound : Nat) (value : Carrier FiniteBinaryDrive)
    (supported : value ∈ (SourceConditionalHistory.observed
      (sourceLaw downstreamTechnology downstreamGraph seed bound) materialRead).support)
    (point : Fin (bound + 1))
    (same : sourcePoint (driveAt downstreamTechnology downstreamGraph seed point.val) = value) :
    loadedExposure downstreamTechnology downstreamGraph seed (point.val + 1) ∈
      ((SourceConditionalHistory.conditional
        (sourceLaw downstreamTechnology downstreamGraph seed bound) materialRead value supported).map
          (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph))).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨materialQuery downstreamTechnology downstreamGraph seed bound point, ?_, rfl⟩
  rw [SourceConditionalHistory.conditional_support]
  refine ⟨?_, sample_supported downstreamTechnology downstreamGraph seed bound point⟩
  exact (material_read_history downstreamTechnology downstreamGraph seed point.val).trans same

theorem conditional_next_not_pure (bound : Nat) (enough : 2 ≤ bound)
    (supported : sourcePoint (driveAt downstreamTechnology downstreamGraph seed 0) ∈
      (SourceConditionalHistory.observed
        (sourceLaw downstreamTechnology downstreamGraph seed bound) materialRead).support) :
    ∀ material, (SourceConditionalHistory.conditional
      (sourceLaw downstreamTechnology downstreamGraph seed bound) materialRead
        (sourcePoint (driveAt downstreamTechnology downstreamGraph seed 0)) supported).map
          (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph)) ≠ PMF.pure material := by
  intro material pure
  let first : Fin (bound + 1) := ⟨0, by omega⟩
  let third : Fin (bound + 1) := ⟨2, by omega⟩
  have one := next_image_supported downstreamTechnology downstreamGraph seed bound _ supported first rfl
  have three := next_image_supported downstreamTechnology downstreamGraph seed bound _ supported third
    (congrArg sourcePoint (driveAt_two downstreamTechnology downstreamGraph seed 0))
  rw [pure, PMF.mem_support_pure_iff] at one three
  have distinct : loadedExposure downstreamTechnology downstreamGraph seed 1 ≠
      loadedExposure downstreamTechnology downstreamGraph seed 3 :=
    fun same => (by decide : (1 : Nat) ≠ 3)
      (exposure_injective downstreamTechnology downstreamGraph seed same)
  exact distinct (one.trans three.symm)

end
end FiniteADCWholeJointCurrent.Information.ConditionalAction
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
