import H0mework.Probability.Information.Pairwise
import H0mework.Computation.LoadedADCInformation.DistortionTiming
import H0mework.Computation.LoadedADCInformation.DistortionGrowth

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Distortion

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def actualExcess (bound : Nat) : ℝ :=
  (1 / (2 * (bound + 1 : ℝ))) *
    ∑ side : Fin 2, (phaseCount bound side : ℝ)⁻¹ *
      fibreTimingExcess downstreamTechnology downstreamGraph seed bound side

theorem actualExcess_nonnegative (bound : Nat) :
    0 ≤ actualExcess downstreamTechnology downstreamGraph seed bound := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun side _ =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (fibreTimingExcess_nonnegative downstreamTechnology downstreamGraph seed bound side)

private theorem original_time_task (bound : Nat) :
    timeTask downstreamTechnology downstreamGraph seed bound =
      fun index => (loadedElapsed downstreamTechnology downstreamGraph seed index.val : ℂ) := by
  funext index
  exact congrArg Complex.ofReal (timeQuery_generated downstreamTechnology downstreamGraph seed bound index)

private theorem residual_phase_pairs (bound : Nat) :
    ‖residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound))‖ ^ 2 =
      (1 / (2 * (bound + 1 : ℝ))) *
        ∑ side : Fin 2, (phaseCount bound side : ℝ)⁻¹ *
          ∑ left ∈ fibre bound side, ∑ right ∈ fibre bound side,
            (loadedElapsed downstreamTechnology downstreamGraph seed right.val -
              loadedElapsed downstreamTechnology downstreamGraph seed left.val) ^ 2 := by
  rw [original_time_task]
  rw [SourceUniformFibreVariance.residual_pairwise]
  apply congrArg (fun total : ℝ => (1 / (2 * (bound + 1 : ℝ))) * total)
  rw [SourceUniformFibreVariance.outputs, sum_query_image]
  apply Finset.sum_congr rfl
  intro side _
  have same : SourceUniformFibreVariance.fibre bound
      (query downstreamTechnology downstreamGraph seed bound)
      (driveAt downstreamTechnology downstreamGraph seed side.val) = fibre bound side :=
    (fibre_is_original_side downstreamTechnology downstreamGraph seed bound side).symm
  by_cases positive : 0 < phaseCount bound side
  · simp only [positive, if_true, same, fibre_card]
  · have zero : phaseCount bound side = 0 := Nat.eq_zero_of_not_pos positive
    rw [if_neg positive]
    simp only [zero, Nat.cast_zero, inv_zero, zero_mul]

theorem residual_physical (bound : Nat) :
    ‖residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound))‖ ^ 2 =
      gridBase (hardware := hardware) bound + actualExcess downstreamTechnology downstreamGraph seed bound := by
  rw [residual_phase_pairs]
  rw [Finset.mul_sum]
  simp only [← mul_assoc, normalised_fibre_time_pairs]
  rw [Finset.sum_add_distrib]
  simp only [gridBase, actualExcess, Finset.mul_sum, mul_assoc]

theorem residual_grid_lower (bound : Nat) :
    gridBase (hardware := hardware) bound ≤
      ‖residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
        (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound))‖ ^ 2 := by
  rw [residual_physical]
  exact le_add_of_nonneg_right (actualExcess_nonnegative downstreamTechnology downstreamGraph seed bound)

theorem decoder_grid_lower (bound : Nat) (decoder : FiniteBinaryDrive → ℂ) :
    gridBase (hardware := hardware) bound ≤
      error (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
        (timeTask downstreamTechnology downstreamGraph seed bound) decoder :=
  (residual_grid_lower downstreamTechnology downstreamGraph seed bound).trans
    (SourceUniformFibreVariance.decoder_lower bound (query downstreamTechnology downstreamGraph seed bound)
      (timeQuery downstreamTechnology downstreamGraph seed bound) decoder)

end
end FiniteADCWholeJointCurrent.Information.Distortion
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
