import H0mework.Physics.ADCRuntime.LoadedReceiverContinuation

/-! # Full physical snapshot time of the generated loaded continuation -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Cells.Conductance
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {technology : AIGCellTechnology} {actualBoot : FiniteDimensionedSeriesRLCPortState}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem loadedStepDuration_four_phases :
    (loadedStepDuration downstreamTechnology downstreamGraph seed).value =
      (readDelay (hardware := hardware)
        (clockMax := loadedReceiverInstalledMaxTick hardware technology actualBoot) (technology := technology)
        downstreamTechnology downstreamGraph).value +
      (commonOutputLoadDuration (hardware := hardware)
        (clockMax := loadedReceiverInstalledMaxTick hardware technology actualBoot)
        (technology := technology) downstreamTechnology downstreamGraph).value +
      (commonRecoverySampleTime downstreamTechnology downstreamGraph seed).value +
      (loadedReceiverFreshSample downstreamTechnology downstreamGraph seed).val.executedDuration.value := rfl

/-- The trace ends at the current ADC snapshot. Its edge times include read,
load, recovery and the next actual sample, rather than only plant-start gaps. -/
def loadedElapsed (frames : Nat) : ℝ :=
  ∑ frame ∈ Finset.range frames,
    (loadedStepDuration downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed frame)).value

@[simp] theorem loadedElapsed_zero :
    loadedElapsed downstreamTechnology downstreamGraph seed 0 = 0 := by
  simp [loadedElapsed]

theorem loadedElapsed_succ (frames : Nat) :
    loadedElapsed downstreamTechnology downstreamGraph seed (frames + 1) =
      loadedElapsed downstreamTechnology downstreamGraph seed frames +
        (loadedStepDuration downstreamTechnology downstreamGraph
          (loadedAfter downstreamTechnology downstreamGraph seed frames)).value :=
  Finset.sum_range_succ _ _

theorem loadedElapsed_lower_bound (frames : Nat) :
    (frames : ℝ) *
        (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource hardware.clockCode).value ≤
      loadedElapsed downstreamTechnology downstreamGraph seed frames := by
  calc
    _ = ∑ _frame ∈ Finset.range frames,
        (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource hardware.clockCode).value := by simp
    _ ≤ _ := Finset.sum_le_sum (fun frame _ =>
      loadedStepDuration_ge_tick downstreamTechnology downstreamGraph
        (loadedAfter downstreamTechnology downstreamGraph seed frame))

theorem loadedElapsed_strictMono :
    StrictMono (loadedElapsed downstreamTechnology downstreamGraph seed) := by
  apply strictMono_nat_of_lt_succ
  intro frames
  rw [loadedElapsed_succ]
  have tick := finiteSamplingClockTickPeriod_pos hardware.meteredSource.fixture.coreSource hardware.clockCode
  have duration := loadedStepDuration_ge_tick downstreamTechnology downstreamGraph
    (loadedAfter downstreamTechnology downstreamGraph seed frames)
  linarith

theorem loadedContinuation_no_zeno (timeBound : ℝ) :
    ∃ frames : Nat, timeBound < loadedElapsed downstreamTechnology downstreamGraph seed frames := by
  let tick := (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource hardware.clockCode).value
  have positive : 0 < tick :=
    finiteSamplingClockTickPeriod_pos hardware.meteredSource.fixture.coreSource hardware.clockCode
  obtain ⟨frames, enough⟩ := exists_nat_gt (timeBound / tick)
  have scaled := mul_lt_mul_of_pos_right enough positive
  rw [div_mul_cancel₀ _ (ne_of_gt positive)] at scaled
  exact ⟨frames, lt_of_lt_of_le scaled (loadedElapsed_lower_bound _ _ _ frames)⟩

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
