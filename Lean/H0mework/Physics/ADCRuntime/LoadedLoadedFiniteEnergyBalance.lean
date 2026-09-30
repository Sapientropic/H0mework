import H0mework.Physics.ADCRuntime.LoadedLoadedStepEnergyBalance
import H0mework.Physics.ADCRuntime.LoadedReceiverTiming

/-! # Finite generated continuation consumes the same actual whole-step energy law -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
  {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {technology : AIGCellTechnology} {actualBoot : FiniteDimensionedSeriesRLCPortState}
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (seed : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def loadedFiniteWork (frames : Nat) : SIJoule :=
  ⟨∑ frame ∈ Finset.range frames,
    (loadedStepWork downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed frame)).value⟩

def loadedFiniteHeat (frames : Nat) : SIJoule :=
  ⟨∑ frame ∈ Finset.range frames,
    (loadedStepHeat downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed frame)).value⟩

@[simp] theorem loadedFiniteWork_zero :
    loadedFiniteWork downstreamTechnology downstreamGraph seed 0 = ⟨0⟩ := by
  simp only [loadedFiniteWork, Finset.range_zero, Finset.sum_empty]

@[simp] theorem loadedFiniteHeat_zero :
    loadedFiniteHeat downstreamTechnology downstreamGraph seed 0 = ⟨0⟩ := by
  simp only [loadedFiniteHeat, Finset.range_zero, Finset.sum_empty]

theorem loadedFiniteHeat_nonneg (frames : Nat) :
    0 ≤ (loadedFiniteHeat downstreamTechnology downstreamGraph seed frames).value :=
  Finset.sum_nonneg (s := Finset.range frames) fun frame _ =>
    loadedStepHeat_nonneg downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed frame)

/-- Existing finite telescoping, not another domain induction, consumes each generated step. -/
theorem loadedFinite_energy_balance (frames : Nat) :
    (jointStoredEnergy (loadedAfter downstreamTechnology downstreamGraph seed frames)).value -
        (jointStoredEnergy seed).value =
      (loadedFiniteWork downstreamTechnology downstreamGraph seed frames).value -
        (loadedFiniteHeat downstreamTechnology downstreamGraph seed frames).value := by
  calc
    _ = ∑ frame ∈ Finset.range frames,
        ((jointStoredEnergy (loadedAfter downstreamTechnology downstreamGraph seed (frame + 1))).value -
          (jointStoredEnergy (loadedAfter downstreamTechnology downstreamGraph seed frame)).value) := by
      simpa only [loadedAfter_zero] using
        (Finset.sum_range_sub (fun frame =>
          (jointStoredEnergy (loadedAfter downstreamTechnology downstreamGraph seed frame)).value) frames).symm
    _ = ∑ frame ∈ Finset.range frames,
        ((loadedStepWork downstreamTechnology downstreamGraph
            (loadedAfter downstreamTechnology downstreamGraph seed frame)).value -
          (loadedStepHeat downstreamTechnology downstreamGraph
            (loadedAfter downstreamTechnology downstreamGraph seed frame)).value) := by
      apply Finset.sum_congr rfl
      intro frame _
      rw [loadedAfter_succ, loadedStep_energy_balance]
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      rfl

/-- Heat cannot be spent outside the actual initial store and signed external work. -/
theorem loadedFinite_heat_budget (frames : Nat) :
    (loadedFiniteHeat downstreamTechnology downstreamGraph seed frames).value ≤
      (jointStoredEnergy seed).value + (loadedFiniteWork downstreamTechnology downstreamGraph seed frames).value := by
  have paid := loadedFinite_energy_balance downstreamTechnology downstreamGraph seed frames
  have stored := jointStoredEnergy_nonneg (loadedAfter downstreamTechnology downstreamGraph seed frames)
  linarith

theorem loadedFinite_no_unpaid_storage_increase (frames : Nat) :
    (jointStoredEnergy (loadedAfter downstreamTechnology downstreamGraph seed frames)).value -
        (jointStoredEnergy seed).value ≤
      (loadedFiniteWork downstreamTechnology downstreamGraph seed frames).value := by
  rw [loadedFinite_energy_balance]
  exact sub_le_self _ (loadedFiniteHeat_nonneg downstreamTechnology downstreamGraph seed frames)

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
