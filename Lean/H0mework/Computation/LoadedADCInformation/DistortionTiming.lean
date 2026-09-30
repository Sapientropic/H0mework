import H0mework.Computation.LoadedADCInformation.DistortionSourceLattice

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Distortion

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem elapsed_gap (first steps : Nat) :
    tick (hardware := hardware) * (steps : ℝ) ≤
      loadedElapsed downstreamTechnology downstreamGraph seed (first + steps) -
        loadedElapsed downstreamTechnology downstreamGraph seed first := by
  induction steps with
  | zero => simp
  | succ steps previous =>
      rw [← Nat.add_assoc, loadedElapsed_succ]
      have paid := charge_ge_tick downstreamTechnology downstreamGraph seed (first + steps)
      change tick (hardware := hardware) ≤
        (loadedStepDuration downstreamTechnology downstreamGraph
          (loadedAfter downstreamTechnology downstreamGraph seed (first + steps))).value at paid
      push_cast
      nlinarith

theorem time_gap (left right : Nat) (ordered : left ≤ right) :
    tick (hardware := hardware) * ((right : ℝ) - (left : ℝ)) ≤
      loadedElapsed downstreamTechnology downstreamGraph seed right -
        loadedElapsed downstreamTechnology downstreamGraph seed left := by
  have generated := elapsed_gap downstreamTechnology downstreamGraph seed left (right - left)
  rw [Nat.add_sub_of_le ordered, Nat.cast_sub ordered] at generated
  exact generated

private theorem ordered_time_pair (left right : Nat) (ordered : left ≤ right) :
    tick (hardware := hardware) ^ 2 * ((right : ℝ) - (left : ℝ)) ^ 2 ≤
      (loadedElapsed downstreamTechnology downstreamGraph seed right -
        loadedElapsed downstreamTechnology downstreamGraph seed left) ^ 2 := by
  have generated := time_gap downstreamTechnology downstreamGraph seed left right ordered
  have nonnegative : 0 ≤ tick (hardware := hardware) * ((right : ℝ) - (left : ℝ)) :=
    mul_nonneg (tick_pos (hardware := hardware)).le (sub_nonneg.mpr (by exact_mod_cast ordered))
  simpa only [mul_pow] using (sq_le_sq₀ nonnegative (nonnegative.trans generated)).mpr generated

theorem time_pair_lower_bound (left right : Nat) :
    tick (hardware := hardware) ^ 2 * ((right : ℝ) - (left : ℝ)) ^ 2 ≤
      (loadedElapsed downstreamTechnology downstreamGraph seed right -
        loadedElapsed downstreamTechnology downstreamGraph seed left) ^ 2 := by
  rcases le_total left right with ordered | reversed
  · exact ordered_time_pair downstreamTechnology downstreamGraph seed left right ordered
  · convert ordered_time_pair downstreamTechnology downstreamGraph seed right left reversed using 1 <;> ring

def timingPairExcess (left right : Nat) : ℝ :=
  (loadedElapsed downstreamTechnology downstreamGraph seed right -
    loadedElapsed downstreamTechnology downstreamGraph seed left) ^ 2 -
      tick (hardware := hardware) ^ 2 * ((right : ℝ) - (left : ℝ)) ^ 2

theorem timingPairExcess_nonnegative (left right : Nat) :
    0 ≤ timingPairExcess downstreamTechnology downstreamGraph seed left right :=
  sub_nonneg.mpr (time_pair_lower_bound downstreamTechnology downstreamGraph seed left right)

def fibreTimingExcess (bound : Nat) (side : Fin 2) : ℝ :=
  ∑ left ∈ fibre bound side, ∑ right ∈ fibre bound side,
    timingPairExcess downstreamTechnology downstreamGraph seed left.val right.val

theorem fibreTimingExcess_nonnegative (bound : Nat) (side : Fin 2) :
    0 ≤ fibreTimingExcess downstreamTechnology downstreamGraph seed bound side :=
  Finset.sum_nonneg (fun left _ => Finset.sum_nonneg (fun right _ =>
    timingPairExcess_nonnegative downstreamTechnology downstreamGraph seed left.val right.val))

theorem fibre_time_pairs (bound : Nat) (side : Fin 2) :
    (∑ left ∈ fibre bound side, ∑ right ∈ fibre bound side,
      (loadedElapsed downstreamTechnology downstreamGraph seed right.val -
        loadedElapsed downstreamTechnology downstreamGraph seed left.val) ^ 2) =
      tick (hardware := hardware) ^ 2 * ((2 / 3 : ℝ) * (phaseCount bound side : ℝ) ^ 2 *
        ((phaseCount bound side : ℝ) ^ 2 - 1)) +
      fibreTimingExcess downstreamTechnology downstreamGraph seed bound side := by
  have generated (left right : Fin (bound + 1)) :
      (loadedElapsed downstreamTechnology downstreamGraph seed right.val -
        loadedElapsed downstreamTechnology downstreamGraph seed left.val) ^ 2 =
      tick (hardware := hardware) ^ 2 * ((right.val : ℝ) - (left.val : ℝ)) ^ 2 +
        timingPairExcess downstreamTechnology downstreamGraph seed left.val right.val := by
    unfold timingPairExcess
    ring
  simp only [generated, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [fibre_index_pair_square_sum]
  rfl

theorem normalised_fibre_time_pairs (bound : Nat) (side : Fin 2) :
    (1 / (2 * (bound + 1 : ℝ))) * (phaseCount bound side : ℝ)⁻¹ *
      (∑ left ∈ fibre bound side, ∑ right ∈ fibre bound side,
        (loadedElapsed downstreamTechnology downstreamGraph seed right.val -
          loadedElapsed downstreamTechnology downstreamGraph seed left.val) ^ 2) =
      tick (hardware := hardware) ^ 2 / (3 * (bound + 1 : ℝ)) *
        (phaseCount bound side : ℝ) * ((phaseCount bound side : ℝ) ^ 2 - 1) +
      (1 / (2 * (bound + 1 : ℝ))) * (phaseCount bound side : ℝ)⁻¹ *
        fibreTimingExcess downstreamTechnology downstreamGraph seed bound side := by
  by_cases zero : phaseCount bound side = 0
  · simp [zero]
  · have nonzero : (phaseCount bound side : ℝ) ≠ 0 := by exact_mod_cast zero
    have totalNonzero : (bound + 1 : ℝ) ≠ 0 := by positivity
    rw [fibre_time_pairs]
    field_simp

end
end FiniteADCWholeJointCurrent.Information.Distortion
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
