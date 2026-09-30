import H0mework.Physics.ReceiverActuation.CapacitorRLCWork
import H0mework.Physics.ReceiverActuation.CommonLoad

/-! # The actual ten addressed receiver loads settle their complete passive energy loss -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Producer
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

def outputLoadHeatAt (channel : FiniteEmbodimentChannel) (time : ℝ) : SIJoule :=
  let cell := outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel
  let hold := compileHoldLeaseForGraph cell downstreamTechnology downstreamGraph
    hardware.meteredSource.fixture.coreSource hardware.clockCode
  let recipient := current.outputLoadInitialRecipient downstreamTechnology downstreamGraph
  capacitorRLCLeakHeatAt cell hold (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    channel (current.outputLoadInitialVoltage downstreamTechnology downstreamGraph channel)
    (recipient.voltageAt channel) (recipient.currentAt channel) time +
  capacitorRLCResistiveHeatAt cell hold (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    channel (current.outputLoadInitialVoltage downstreamTechnology downstreamGraph channel)
    (recipient.voltageAt channel) (recipient.currentAt channel) time

theorem outputLoadHeatAt_nonneg (channel : FiniteEmbodimentChannel) (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (outputLoadHeatAt downstreamTechnology downstreamGraph current channel time).value := by
  obtain ⟨leak, resistor⟩ := capacitorRLCHeatAt_nonneg
    (outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel)
    (compileHoldLeaseForGraph _ downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode)
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel
    (current.outputLoadInitialVoltage downstreamTechnology downstreamGraph channel)
    ((current.outputLoadInitialRecipient downstreamTechnology downstreamGraph).voltageAt channel)
    ((current.outputLoadInitialRecipient downstreamTechnology downstreamGraph).currentAt channel) time nonnegative
  exact add_nonneg leak resistor

theorem outputLoadEnergyAt_integrated_balance (channel : FiniteEmbodimentChannel) (time : ℝ) :
    (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel time).value -
        (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel 0).value =
      -(outputLoadHeatAt downstreamTechnology downstreamGraph current channel time).value := by
  have paid := capacitorRLCEnergyAt_integrated_balance
    (outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel)
    (compileHoldLeaseForGraph _ downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode)
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel
    (current.outputLoadInitialVoltage downstreamTechnology downstreamGraph channel)
    ((current.outputLoadInitialRecipient downstreamTechnology downstreamGraph).voltageAt channel)
    ((current.outputLoadInitialRecipient downstreamTechnology downstreamGraph).currentAt channel) time
  convert paid using 1 <;> first | rfl | (
    dsimp only [outputLoadHeatAt, SIQuantity.add_value]
    ring)

def wholeOutputLoadHeatAt (time : ℝ) : SIJoule :=
  ⟨∑ channel, (outputLoadHeatAt downstreamTechnology downstreamGraph current channel time).value⟩

theorem wholeOutputLoadHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (wholeOutputLoadHeatAt downstreamTechnology downstreamGraph current time).value :=
  Finset.sum_nonneg (s := Finset.univ) fun channel _ =>
    outputLoadHeatAt_nonneg downstreamTechnology downstreamGraph current channel time nonnegative

/-- All channels use the same elapsed time; signed transfer is internal to each load. -/
theorem wholeOutputLoadEnergyAt_integrated_balance (time : ℝ) :
    (∑ channel, (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel time).value) -
      (∑ channel, (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel 0).value) =
        -(wholeOutputLoadHeatAt downstreamTechnology downstreamGraph current time).value := by
  have rows := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun channel (_ : channel ∈ (Finset.univ : Finset FiniteEmbodimentChannel)) =>
      outputLoadEnergyAt_integrated_balance downstreamTechnology downstreamGraph current channel time)
  simpa only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, wholeOutputLoadHeatAt] using rows

theorem commonOutputLoadEnergy_paid :
    let time := (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value
    (∑ channel, (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel time).value) -
      (∑ channel, (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel 0).value) =
        -(wholeOutputLoadHeatAt downstreamTechnology downstreamGraph current time).value :=
  wholeOutputLoadEnergyAt_integrated_balance _ _ _ _

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
