import H0mework.Computation.LoadedADCPacket.IntervalConditional

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Interval

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

theorem step_work_interval (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    ((loadedStep downstreamTechnology downstreamGraph current).memory.storedEnergy +
        energyLower (loadedStep downstreamTechnology downstreamGraph current).packet).value -
      (current.memory.storedEnergy + energyUpper current.packet).value +
        (loadedStepHeat downstreamTechnology downstreamGraph current).value ≤
      (loadedStepWork downstreamTechnology downstreamGraph current).value ∧
    (loadedStepWork downstreamTechnology downstreamGraph current).value ≤
      ((loadedStep downstreamTechnology downstreamGraph current).memory.storedEnergy +
        energyUpper (loadedStep downstreamTechnology downstreamGraph current).packet).value -
      (current.memory.storedEnergy + energyLower current.packet).value +
        (loadedStepHeat downstreamTechnology downstreamGraph current).value := by
  have currentBounds := joint_interval current
  have nextBounds := joint_interval (loadedStep downstreamTechnology downstreamGraph current)
  have paid := loadedStep_energy_balance downstreamTechnology downstreamGraph current
  constructor <;> linarith only [currentBounds.1, currentBounds.2, nextBounds.1, nextBounds.2, paid]

variable (seed : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem whole_work_interval (frames : Nat) :
    ((loadedAfter downstreamTechnology downstreamGraph seed frames).memory.storedEnergy +
        energyLower (loadedAfter downstreamTechnology downstreamGraph seed frames).packet).value -
      (seed.memory.storedEnergy + energyUpper seed.packet).value +
        heatRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) ≤
      workRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) ∧
    workRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) ≤
      ((loadedAfter downstreamTechnology downstreamGraph seed frames).memory.storedEnergy +
        energyUpper (loadedAfter downstreamTechnology downstreamGraph seed frames).packet).value -
      (seed.memory.storedEnergy + energyLower seed.packet).value +
        heatRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) := by
  have initialBounds := joint_interval seed
  have finalBounds := joint_interval (loadedAfter downstreamTechnology downstreamGraph seed frames)
  have paid := whole_material_account downstreamTechnology downstreamGraph seed frames
  constructor <;> linarith only [initialBounds.1, initialBounds.2, finalBounds.1, finalBounds.2, paid]

theorem packet_heat_budget (frames : Nat) :
    heatRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) ≤
      (seed.memory.storedEnergy + energyUpper seed.packet).value +
        workRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed frames) := by
  have bounds := joint_interval seed
  have paid := material_heat_budget downstreamTechnology downstreamGraph seed frames
  linarith only [bounds.2, paid]

end
end FiniteADCWholeJointCurrent.Information.Packet.Interval
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
