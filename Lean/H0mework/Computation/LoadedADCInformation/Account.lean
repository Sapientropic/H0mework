import H0mework.Computation.LoadedADCInformation.Source
import H0mework.Physics.ADCRuntime.LoadedLoadedFiniteEnergyBalance

/-! The identical original material fold retains signed work and heat through all four actual phases. -/

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

private theorem charge_exposure (value : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology → ℝ) (frames : Nat) :
    RootedAccountedUnfolding.SourceCharge.tally value (loadedExposure downstreamTechnology downstreamGraph seed frames) =
      ∑ frame ∈ Finset.range frames, value (loadedAfter downstreamTechnology downstreamGraph seed frame) := by
  induction frames with
  | zero => simp [loadedExposure, RootedAccountedUnfolding.observe_zero,
      RootedAccountedUnfolding.SourceCharge.tally, RootedAccountedUnfolding.zero,
      RootedAccountedUnfolding.fold, RootedAccountedUnfolding.foldBranches,
      RootedAccountedUnfolding.SourceCharge.atSource]
  | succ frames induction =>
      change RootedAccountedUnfolding.SourceCharge.tally value
        ((loadedExposure downstreamTechnology downstreamGraph seed frames).advance _) = _
      rw [RootedAccountedUnfolding.SourceCharge.advance, loadedExposure_frontier, induction, Finset.sum_range_succ]
      simp

def workRead (material : RootedAccountedUnfolding
    (FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)) : ℝ :=
  RootedAccountedUnfolding.SourceCharge.tally
    (fun current => (loadedStepWork downstreamTechnology downstreamGraph current).value) material

def heatRead (material : RootedAccountedUnfolding
    (FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)) : ℝ :=
  RootedAccountedUnfolding.SourceCharge.tally
    (fun current => (loadedStepHeat downstreamTechnology downstreamGraph current).value) material

theorem workRead_exposure (frames : Nat) :
    workRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) =
      (loadedFiniteWork downstreamTechnology downstreamGraph seed frames).value :=
  charge_exposure downstreamTechnology downstreamGraph seed _ frames

theorem heatRead_exposure (frames : Nat) :
    heatRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) =
      (loadedFiniteHeat downstreamTechnology downstreamGraph seed frames).value :=
  charge_exposure downstreamTechnology downstreamGraph seed _ frames

theorem whole_material_account (frames : Nat) :
    (jointStoredEnergy (loadedAfter downstreamTechnology downstreamGraph seed frames)).value -
      (jointStoredEnergy seed).value =
        workRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) -
          heatRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) := by
  rw [workRead_exposure, heatRead_exposure]
  exact loadedFinite_energy_balance downstreamTechnology downstreamGraph seed frames

theorem material_heat_budget (frames : Nat) :
    heatRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) ≤
      (jointStoredEnergy seed).value +
        workRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) := by
  rw [heatRead_exposure, workRead_exposure]
  exact loadedFinite_heat_budget downstreamTechnology downstreamGraph seed frames

end
end FiniteADCWholeJointCurrent.Information
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
