import H0mework.Probability.Information.Entropy
import H0mework.Computation.LoadedADCInformation.DistortionPhysical

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Distortion

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open scoped Classical
noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def historyInformation (bound : Nat) : ℝ :=
  SourceUniformFibreInformation.conditionalEntropy bound (query downstreamTechnology downstreamGraph seed bound)

private theorem source_fibre_statistic (bound : Nat) (read : ℝ → ℝ) (empty : read 0 = 0) :
    (∑ value ∈ SourceUniformFibreVariance.outputs bound (query downstreamTechnology downstreamGraph seed bound),
      read (SourceUniformFibreVariance.fibre bound (query downstreamTechnology downstreamGraph seed bound) value).card) =
    ∑ side : Fin 2, read (phaseCount bound side) := by
  rw [SourceUniformFibreVariance.outputs, sum_query_image]
  apply Finset.sum_congr rfl
  intro side _
  have same : SourceUniformFibreVariance.fibre bound
      (query downstreamTechnology downstreamGraph seed bound)
      (driveAt downstreamTechnology downstreamGraph seed side.val) = fibre bound side :=
    (fibre_is_original_side downstreamTechnology downstreamGraph seed bound side).symm
  by_cases positive : 0 < phaseCount bound side
  · rw [if_pos positive, same, fibre_card]
  · have zero : phaseCount bound side = 0 := Nat.eq_zero_of_not_pos positive
    rw [if_neg positive, zero, Nat.cast_zero, empty]

theorem historyInformation_formula (bound : Nat) :
    historyInformation downstreamTechnology downstreamGraph seed bound =
      ∑ side : Fin 2, (phaseCount bound side : ℝ) / (bound + 1) * Real.log (phaseCount bound side) := by
  rw [historyInformation, SourceUniformFibreInformation.conditional_entropy_formula]
  exact source_fibre_statistic downstreamTechnology downstreamGraph seed bound
    (fun count => count / (bound + 1) * Real.log count) (by simp)

theorem information_grid_bound (bound : Nat) :
    tick (hardware := hardware) ^ 2 / 3 *
      (Real.exp (2 * historyInformation downstreamTechnology downstreamGraph seed bound) - 1) ≤
        gridBase (hardware := hardware) bound := by
  have generated := SourceUniformFibreInformation.entropy_spread_lower bound
    (query downstreamTechnology downstreamGraph seed bound) (tick (hardware := hardware))
  rw [source_fibre_statistic downstreamTechnology downstreamGraph seed bound
    (fun count => count * (count ^ 2 - 1)) (by simp)] at generated
  exact generated

theorem information_residual_bound (bound : Nat) :
    tick (hardware := hardware) ^ 2 / 3 *
      (Real.exp (2 * historyInformation downstreamTechnology downstreamGraph seed bound) - 1) ≤
      ‖residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
        (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound))‖ ^ 2 :=
  (information_grid_bound downstreamTechnology downstreamGraph seed bound).trans
    (residual_grid_lower downstreamTechnology downstreamGraph seed bound)

theorem information_decoder_bound (bound : Nat) (decoder : FiniteBinaryDrive → ℂ) :
    tick (hardware := hardware) ^ 2 / 3 *
      (Real.exp (2 * historyInformation downstreamTechnology downstreamGraph seed bound) - 1) ≤
      error (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
        (timeTask downstreamTechnology downstreamGraph seed bound) decoder :=
  (information_grid_bound downstreamTechnology downstreamGraph seed bound).trans
    (decoder_grid_lower downstreamTechnology downstreamGraph seed bound decoder)

theorem model_information_zero (bound : Nat) :
    SourceUniformFibreInformation.conditionalEntropy bound
      (AccountAction.modelQuery downstreamTechnology downstreamGraph seed bound) = 0 :=
  SourceUniformFibreInformation.conditional_entropy_zero_of_injective bound _
    (AccountAction.model_query_injective downstreamTechnology downstreamGraph seed bound)

end
end FiniteADCWholeJointCurrent.Information.Distortion
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
