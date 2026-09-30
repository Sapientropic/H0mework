import H0mework.Computation.LoadedADCInformation.Error

/-! Drive recovery is exact for its own task; omitted physical history is a different obligation. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

theorem drive_task_recovery (bound : Nat) (read : FiniteBinaryDrive → ℂ) :
    error (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (read ∘ query downstreamTechnology downstreamGraph seed bound) read = 0 := by
  simp [error]

theorem two_actor_query_injective :
    Function.Injective (query downstreamTechnology downstreamGraph seed 1) := by
  intro left right same
  fin_cases left <;> fin_cases right
  · rfl
  · exact False.elim (driveAt_distinct downstreamTechnology downstreamGraph seed 0 same.symm)
  · exact False.elim (driveAt_distinct downstreamTechnology downstreamGraph seed 0 same)
  · rfl

theorem two_actor_recovery (task : Fin 2 → ℂ) :
    error (historyPMF 1) (query downstreamTechnology downstreamGraph seed 1) task
      (optimalDecoder (historyPMF 1) (query downstreamTechnology downstreamGraph seed 1) task) = 0 := by
  have recovers := ObservationRefinement.optimum_injective (historyPMF 1)
    (query downstreamTechnology downstreamGraph seed 1)
    (two_actor_query_injective downstreamTechnology downstreamGraph seed) task
  unfold error
  apply Finset.sum_eq_zero
  intro point _
  rw [recovers point (history_weight_positive 1 point)]
  simp

theorem no_drive_material_decoder :
    ¬ ∃ decoder : FiniteBinaryDrive → RootedAccountedUnfolding
      (FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology),
      ∀ frame, decoder (driveAt downstreamTechnology downstreamGraph seed frame) =
        loadedExposure downstreamTechnology downstreamGraph seed frame := by
  rintro ⟨decoder, recovers⟩
  apply no_drive_time_decoder downstreamTechnology downstreamGraph seed
  refine ⟨timeRead downstreamTechnology downstreamGraph ∘ decoder, fun frame => ?_⟩
  simp only [Function.comp_apply, recovers, timeRead_exposure]

end
end FiniteADCWholeJointCurrent.Information
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
