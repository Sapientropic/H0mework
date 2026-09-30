import H0mework.Physics.ReceiverActuation.EndpointEnergyEnvelope
import H0mework.Physics.ReceiverActuation.OutputLoad
import H0mework.Computation.AIGHold.AIGBankOutputLoad

/-! # The actual output-load energy has no receiver-width dependency

The restored output has one read pin. Its actual in-rail charge and the core's
generated endpoint bounds pay a source-only energy envelope before connection.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

def wholeReceiverOutputEnergyEnvelopeAt (core : ResonantDrivenCoreSource)
    (technology : AIGCellTechnology) (channel : FiniteEmbodimentChannel) : SIJoule :=
  ⟨(technology.intrinsicCapacitance.value + technology.pinCapacitance.value) / 2 *
      technology.supply.value ^ 2 + (finiteADCCoreRecipientEnergyEnvelopeAt core channel).value⟩

theorem wholeReceiverOutputEnergyEnvelopeAt_nonneg (core : ResonantDrivenCoreSource)
    (technology : AIGCellTechnology) (channel : FiniteEmbodimentChannel) :
    0 ≤ (wholeReceiverOutputEnergyEnvelopeAt core technology channel).value :=
  add_nonneg (mul_nonneg (div_nonneg
    (add_nonneg technology.intrinsic_pos.le technology.pin_nonnegative) (by norm_num)) (sq_nonneg _))
    (finiteADCCoreRecipientEnergyEnvelopeAt_nonneg core channel)

private theorem memory_voltage_bounds {α β : Type} [DecidableEq α] [Hashable α]
    [DecidableEq β] [Hashable β] {width : Nat}
    (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (aigMemoryStateAt technology entry memory assignment downstreamTechnology downstreamGraph
      clock code node polarity time).value ∧
    (aigMemoryStateAt technology entry memory assignment downstreamTechnology downstreamGraph
      clock code node polarity time).value ≤ technology.supply.value :=
  aigMemoryStateAt_mem_rail technology entry memory assignment downstreamTechnology downstreamGraph
    clock code node polarity time nonnegative

namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

theorem outputLoadInitialVoltage_bounds (channel : FiniteEmbodimentChannel) :
    0 ≤ (current.outputLoadInitialVoltage downstreamTechnology downstreamGraph channel).value ∧
    (current.outputLoadInitialVoltage downstreamTechnology downstreamGraph channel).value ≤
      technology.supply.value := by
  unfold outputLoadInitialVoltage receiverStateAt
  apply memory_voltage_bounds
  exact readDelay_nonneg downstreamTechnology downstreamGraph

theorem outputLoadInitialRecipient_absolute_bounds (channel : FiniteEmbodimentChannel) :
    |((current.outputLoadInitialRecipient downstreamTechnology downstreamGraph).voltageAt channel).value| <
      (finiteADCCoreVoltageEnvelopeAt hardware.meteredSource.fixture.coreSource channel).value ∧
    |((current.outputLoadInitialRecipient downstreamTechnology downstreamGraph).currentAt channel).value| <
      (finiteADCCoreCurrentEnvelopeAt hardware.meteredSource.fixture.coreSource channel).value :=
  finiteADCPhysicalDelayedEndpoint_absolute_bounds current.plant _ channel

theorem outputLoadEnergyAt_initial_le_source_envelope (channel : FiniteEmbodimentChannel) :
    (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel 0).value ≤
      (wholeReceiverOutputEnergyEnvelopeAt hardware.meteredSource.fixture.coreSource technology channel).value := by
  have holdBound := current.outputLoadInitialVoltage_bounds downstreamTechnology downstreamGraph channel
  have recipientBound := current.outputLoadInitialRecipient_absolute_bounds downstreamTechnology downstreamGraph channel
  have holdSquare := (sq_le_sq₀ holdBound.1 technology.supply_pos.le).mpr holdBound.2
  have voltageSquare := sq_le_sq.mpr (recipientBound.1.le.trans (le_abs_self _))
  have currentSquare := sq_le_sq.mpr (recipientBound.2.le.trans (le_abs_self _))
  have capacitorBound := mul_le_mul_of_nonneg_left voltageSquare
    (div_nonneg (compiledFiniteDimensionedSeriesRLC_capacitance_pos
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel).le (by norm_num : (0 : ℝ) ≤ 2))
  have inductorBound := mul_le_mul_of_nonneg_left currentSquare
    (div_nonneg (compiledFiniteDimensionedSeriesRLC_inductance_pos
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel).le (by norm_num : (0 : ℝ) ≤ 2))
  have holdEnergyBound := mul_le_mul_of_nonneg_left holdSquare
    (div_nonneg (add_nonneg technology.intrinsic_pos.le technology.pin_nonnegative) (by norm_num : (0 : ℝ) ≤ 2))
  dsimp only [outputLoadEnergyAt, capacitorRLCEnergyAt, capacitorRLCHoldEnergyAt,
    capacitorRLCRecipientEnergyAt, SIQuantity.add_value]
  rw [capacitorRLCStateAt_initial]
  simp only [capacitorRLCInitial, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (outputLoadCell (hardware := hardware) (clockMax := clockMax)
      (technology := technology) channel).capacitance.value =
      technology.intrinsicCapacitance.value + technology.pinCapacitance.value from
    aigBankCell_capacitance_eq _ _ technology]
  exact add_le_add holdEnergyBound (add_le_add capacitorBound inductorBound)

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
