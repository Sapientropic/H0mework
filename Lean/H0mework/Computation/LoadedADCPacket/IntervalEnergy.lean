import H0mework.Computation.LoadedADCPacket.IntervalState
import H0mework.Probability.Recovery.IntervalSquare

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Interval

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

def energyLower (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) : SIJoule :=
  let run := compileFiniteDimensionedSeriesRLCNetlistRun (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
  ⟨∑ channel, ((run.capacitanceAt channel).value / 2 *
      SourceIntervalSquare.lower (voltageLower packet channel).value (voltageUpper packet channel).value +
    (run.inductanceAt channel).value / 2 *
      SourceIntervalSquare.lower (currentLower packet channel).value (currentUpper packet channel).value)⟩

def energyUpper (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) : SIJoule :=
  let run := compileFiniteDimensionedSeriesRLCNetlistRun (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
  ⟨∑ channel, ((run.capacitanceAt channel).value / 2 *
      SourceIntervalSquare.upper (voltageLower packet channel).value (voltageUpper packet channel).value +
    (run.inductanceAt channel).value / 2 *
      SourceIntervalSquare.upper (currentLower packet channel).value (currentUpper packet channel).value)⟩

theorem energy_interval (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    (energyLower current.packet).value ≤ (finiteADCRecipientStoredEnergyAt current.plant current.plant.val.executedDuration).value ∧
      (finiteADCRecipientStoredEnergyAt current.plant current.plant.val.executedDuration).value ≤ (energyUpper current.packet).value := by
  have voltageBounds := fun channel =>
    SourceIntervalSquare.bounds (voltage_interval current channel).1.le (voltage_interval current channel).2
  have currentBounds := fun channel =>
    SourceIntervalSquare.bounds (current_interval current channel).1 (current_interval current channel).2.le
  dsimp only [energyLower, energyUpper, finiteADCRecipientStoredEnergyAt,
    drivenRLCBankStoredEnergy, drivenRLCStoredEnergy]
  constructor
  · apply Finset.sum_le_sum
    intro channel _
    have cap := div_nonneg (compiledFiniteDimensionedSeriesRLC_capacitance_pos
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel).le (by norm_num : (0 : ℝ) ≤ 2)
    have ind := div_nonneg (compiledFiniteDimensionedSeriesRLC_inductance_pos
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel).le (by norm_num : (0 : ℝ) ≤ 2)
    exact add_le_add (mul_le_mul_of_nonneg_left (voltageBounds channel).1 cap)
      (mul_le_mul_of_nonneg_left (currentBounds channel).1 ind)
  · apply Finset.sum_le_sum
    intro channel _
    have cap := div_nonneg (compiledFiniteDimensionedSeriesRLC_capacitance_pos
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel).le (by norm_num : (0 : ℝ) ≤ 2)
    have ind := div_nonneg (compiledFiniteDimensionedSeriesRLC_inductance_pos
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel).le (by norm_num : (0 : ℝ) ≤ 2)
    exact add_le_add (mul_le_mul_of_nonneg_left (voltageBounds channel).2 cap)
      (mul_le_mul_of_nonneg_left (currentBounds channel).2 ind)

theorem joint_interval (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    (current.memory.storedEnergy + energyLower current.packet).value ≤ (jointStoredEnergy current).value ∧
      (jointStoredEnergy current).value ≤ (current.memory.storedEnergy + energyUpper current.packet).value := by
  have bounds := energy_interval current
  unfold jointStoredEnergy
  simp only [SIQuantity.add_value]
  constructor <;> linarith only [bounds.1, bounds.2]

end
end FiniteADCWholeJointCurrent.Information.Packet.Interval
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
