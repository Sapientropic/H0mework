import H0mework.Computation.LoadedADCInformation.ConditionalActionHistory

/-! Every conditional image is an original owned material stage's actual next. -/

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

theorem next_support_owned (bound : Nat) (value : Carrier FiniteBinaryDrive)
    (supported : value ∈ (SourceConditionalHistory.observed
      (sourceLaw downstreamTechnology downstreamGraph seed bound) materialRead).support)
    (nextMaterial : RootedAccountedUnfolding (FiniteADCWholeJointCurrent hardware
      (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology))
    (member : nextMaterial ∈ ((SourceConditionalHistory.conditional
      (sourceLaw downstreamTechnology downstreamGraph seed bound) materialRead value supported).map
        (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph))).support) :
    ∃ point : Fin (bound + 1),
      nextMaterial = loadedExposure downstreamTechnology downstreamGraph seed (point.val + 1) ∧
      sourcePoint (driveAt downstreamTechnology downstreamGraph seed point.val) = value ∧
      type_of% (material_stage_owned downstreamTechnology downstreamGraph seed point.val) := by
  obtain ⟨original, member, nextExact⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  rw [SourceConditionalHistory.conditional_support] at member
  rcases member with ⟨readMatches, inSource⟩
  rw [sourceLaw_sampled, PMF.mem_support_map_iff] at inSource
  obtain ⟨point, _, sourceExact⟩ := inSource
  refine ⟨point, ?_, ?_, material_stage_owned downstreamTechnology downstreamGraph seed point.val⟩
  · rw [← nextExact, ← sourceExact]
    rfl
  · rw [← sourceExact] at readMatches
    exact (material_read_history downstreamTechnology downstreamGraph seed point.val).symm.trans readMatches

theorem conditional_recombines_next (bound : Nat) :
    (SourceConditionalHistory.observed (sourceLaw downstreamTechnology downstreamGraph seed bound) materialRead).bindOnSupport
      (fun value supported => (SourceConditionalHistory.conditional
        (sourceLaw downstreamTechnology downstreamGraph seed bound) materialRead value supported).map
          (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph))) =
      (historyPMF bound).map (fun point => loadedExposure downstreamTechnology downstreamGraph seed (point.val + 1)) := by
  rw [SourceConditionalHistory.recombine_map, next_sampled]

end
end FiniteADCWholeJointCurrent.Information.ConditionalAction
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
