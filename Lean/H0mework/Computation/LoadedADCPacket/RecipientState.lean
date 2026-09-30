import H0mework.Computation.LoadedADCPacket.RecipientLegs
import H0mework.Physics.DrivenEnergy.StateCorrection

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Recipient

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Physical.Interface
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

private theorem current_of_calibrated_resistor
    (actual resistance scale reading error : ℝ) (resistance_ne : resistance ≠ 0)
    (generated : reading * scale = resistance * actual + scale * error) :
    actual = scale * reading / resistance + -(scale / resistance) * error := by
  calc
    actual = (scale * reading - scale * error) / resistance := by
      apply (eq_div_iff resistance_ne).2
      nlinarith [generated]
    _ = _ := by ring

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (current : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem endpoint_current (channel : FiniteEmbodimentChannel) :
    (finiteADCPhysicalEndpoint current.plant).currentAt channel =
      (decodedRecipient current.packet).currentAt channel + currentError current channel := by
  have leg := correctedLeg_original current .resistor channel
  simp only [resonantActualNormalizedResistorAt, resonantActualResistorVoltageAt,
    resistanceTimesCurrent_value] at leg
  field_simp [hardware.meteredSource.fixture.coreSource.2.voltageScale_ne] at leg
  apply SIQuantity.ext
  simp only [finiteADCPhysicalEndpoint, finiteADCPhysicalStateAt_commutes,
    drivenTotalPortStateAt, decodedRecipient, currentError, SIQuantity.add_value]
  exact current_of_calibrated_resistor _ _ _ _ _
    (ne_of_gt (compiledFiniteDimensionedSeriesRLC_resistance_pos
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel)) leg

theorem endpoint_voltage (channel : FiniteEmbodimentChannel) :
    (finiteADCPhysicalEndpoint current.plant).voltageAt channel =
      (decodedRecipient current.packet).voltageAt channel + voltageError current channel := by
  have resistor := correctedLeg_original current .resistor channel
  have inductor := correctedLeg_original current .inductor channel
  simp only [resonantActualNormalizedResistorAt, resonantActualResistorVoltageAt,
    resistanceTimesCurrent_value] at resistor
  simp only [resonantActualNormalizedInductorAt, resonantActualInductorVoltageAt,
    inductanceTimesCurrentRate_value] at inductor
  field_simp [hardware.meteredSource.fixture.coreSource.2.voltageScale_ne] at resistor
  field_simp [ne_of_gt (resonantInductorOutputScale_pos
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel)] at inductor
  have kvl := congrArg SIQuantity.value (drivenTotal_forcedKirchhoffVoltageLaw
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (sourceOwnedResonantDrivenFrequencyAt hardware.meteredSource.fixture.coreSource)
    (sourceOwnedResonantDrivenFrequencyAt_positive hardware.meteredSource.fixture.coreSource)
    (sourceOwnedResonantDrivenDriveAt hardware.meteredSource.fixture.coreSource
      (binaryDriveState current.plant.val.drive)) current.plant.val.initial channel
    current.plant.val.executedDuration)
  simp only [SIQuantity.add_value, inductanceTimesCurrentRate_value, resistanceTimesCurrent_value] at kvl
  have time : (⟨headerSeconds current.packet⟩ : SISecond) = current.plant.val.executedDuration := by
    apply SIQuantity.ext
    exact (packet_duration current).symm
  apply SIQuantity.ext
  simp only [finiteADCPhysicalEndpoint, finiteADCPhysicalStateAt_commutes,
    drivenTotalPortStateAt, decodedRecipient, voltageError, SIQuantity.add_value,
    decodedDrive_original, time]
  nlinarith [resistor, inductor, kvl]

theorem endpoint_eq_shift : finiteADCPhysicalEndpoint current.plant =
    RLCStateError.shift (decodedRecipient current.packet) (voltageError current) (currentError current) := by
  apply FiniteDimensionedSeriesRLCPortState.ext
  · funext channel
    exact endpoint_voltage current channel
  · funext channel
    exact endpoint_current current channel

theorem currentError_bound (channel : FiniteEmbodimentChannel) :
    |(currentError current channel).value| <
      (hardware.meteredSource.fixture.coreSource.2.voltageScale.value /
        ((compileFiniteDimensionedSeriesRLCNetlistRun
          (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)).seriesResistanceAt channel).value) *
        ((1 : ℝ) / 249750) := by
  have ratioPositive := div_pos hardware.meteredSource.fixture.coreSource.2.voltageScalePositive
    (compiledFiniteDimensionedSeriesRLC_resistance_pos
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel)
  simpa only [currentError, abs_mul, abs_neg, abs_of_pos ratioPositive] using
    mul_lt_mul_of_pos_left (quantizationError_bound current .resistor channel) ratioPositive

theorem voltageError_bound (channel : FiniteEmbodimentChannel) :
    |(voltageError current channel).value| <
      (hardware.meteredSource.fixture.coreSource.2.voltageScale.value +
        (resonantInductorOutputScaleAt
          (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel).value) *
        ((1 : ℝ) / 249750) := by
  have resistor := mul_lt_mul_of_pos_left (quantizationError_bound current .resistor channel)
    hardware.meteredSource.fixture.coreSource.2.voltageScalePositive
  have inductor := mul_lt_mul_of_pos_left (quantizationError_bound current .inductor channel)
    (resonantInductorOutputScale_pos
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel)
  dsimp only [voltageError]
  refine lt_of_le_of_lt (abs_add_le _ _) ?_
  rw [abs_mul, abs_of_pos hardware.meteredSource.fixture.coreSource.2.voltageScalePositive,
    abs_mul, abs_of_pos (resonantInductorOutputScale_pos
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel)]
  nlinarith [resistor, inductor]

end
end FiniteADCWholeJointCurrent.Information.Packet.Recipient
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
