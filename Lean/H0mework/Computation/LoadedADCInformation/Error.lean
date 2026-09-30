import H0mework.Computation.LoadedADCInformation.Conditional
import H0mework.Probability.Recovery.Collision

/-! Every sufficiently long original actor history pays a positive physical-time loss under drive compression. -/

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

def timeGap : ℝ :=
  timeRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed 2)

theorem timeGap_generated :
    timeGap downstreamTechnology downstreamGraph seed =
      charge downstreamTechnology downstreamGraph seed +
        charge downstreamTechnology downstreamGraph (loadedStep downstreamTechnology downstreamGraph seed) := by
  rw [timeGap, timeRead_exposure, loadedElapsed_succ, loadedElapsed_succ]
  simp [loadedElapsed, loadedAfter, charge]

theorem timeGap_pos : 0 < timeGap downstreamTechnology downstreamGraph seed := by
  rw [timeGap_generated]
  exact add_pos (charge_pos downstreamTechnology downstreamGraph seed)
    (charge_pos downstreamTechnology downstreamGraph _)

theorem timeGap_lower_bound :
    2 * (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource hardware.clockCode).value ≤
      timeGap downstreamTechnology downstreamGraph seed := by
  rw [timeGap, timeRead_exposure]
  exact loadedElapsed_lower_bound downstreamTechnology downstreamGraph seed 2

theorem compressed_time_lower_bound (bound : Nat) (enough : 2 ≤ bound) (decoder : FiniteBinaryDrive → ℂ) :
    timeGap downstreamTechnology downstreamGraph seed ^ 2 / (2 * (bound + 1 : ℝ)) ≤
      error (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
        (timeTask downstreamTechnology downstreamGraph seed bound) decoder := by
  let left : Fin (bound + 1) := ⟨0, by omega⟩
  let right : Fin (bound + 1) := ⟨2, by omega⟩
  have different : left ≠ right := by intro same; have := congrArg Fin.val same; simp [left, right] at this
  have same : query downstreamTechnology downstreamGraph seed bound left =
      query downstreamTechnology downstreamGraph seed bound right :=
    (driveAt_two downstreamTechnology downstreamGraph seed 0).symm
  have weight : (historyPMF bound left).toReal = (historyPMF bound right).toReal := by
    rw [history_weight, history_weight]
  have paid := equal_weight_pair_lower_bound (historyPMF bound)
    (query downstreamTechnology downstreamGraph seed bound) (timeTask downstreamTechnology downstreamGraph seed bound)
    decoder left right different same weight
  have delta : ‖timeTask downstreamTechnology downstreamGraph seed bound left -
      timeTask downstreamTechnology downstreamGraph seed bound right‖ ^ 2 =
        timeGap downstreamTechnology downstreamGraph seed ^ 2 := by
    change ‖((timeRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed 0) : ℝ) : ℂ) -
      ((timeGap downstreamTechnology downstreamGraph seed : ℝ) : ℂ)‖ ^ 2 = _
    rw [timeRead_exposure]
    simp [loadedElapsed, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [history_weight, delta] at paid
  convert paid using 1
  field_simp

theorem compressed_time_positive (bound : Nat) (enough : 2 ≤ bound) (decoder : FiniteBinaryDrive → ℂ) :
    0 < error (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (timeTask downstreamTechnology downstreamGraph seed bound) decoder :=
  lt_of_lt_of_le (div_pos (sq_pos_of_pos (timeGap_pos downstreamTechnology downstreamGraph seed))
    (by positivity)) (compressed_time_lower_bound downstreamTechnology downstreamGraph seed bound enough decoder)

theorem compressed_residual_lower_bound (bound : Nat) (enough : 2 ≤ bound) :
    timeGap downstreamTechnology downstreamGraph seed ^ 2 / (2 * (bound + 1 : ℝ)) ≤
      ‖residual (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
        (taskValue (historyPMF bound) (timeTask downstreamTechnology downstreamGraph seed bound))‖ ^ 2 := by
  rw [← optimal_attains]
  exact compressed_time_lower_bound downstreamTechnology downstreamGraph seed bound enough _

end
end FiniteADCWholeJointCurrent.Information
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
