import H0mework.Computation.LoadedADCPacket.RecipientSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Recipient

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Physical.Interface
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (current : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem decodedDrive_original : decodedDrive current.packet = current.plant.val.drive := by
  change decodeFiniteADC128EnergySample
    (unpackADCWirePacket (finiteADCPhysicalCurrentSource current.plant)
      (recordedADCWirePacket (finiteADCPhysicalCurrentSource current.plant) current.plant.val
        (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode current.plant.property)
        current.fits)) = _
  rw [unpack_recordedADCWirePacket_current]
  exact decodeFiniteADC128EnergySample_compiled _ _

theorem decodedLeg_original (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) :
    decodedLeg current.packet leg channel =
      finiteADCClockedDecodedLegAt (finiteADCPhysicalCurrentSource current.plant)
        current.plant.val leg channel := by
  change ((finiteADCDigitalLegRatio
    (unpackADCWirePacket (finiteADCPhysicalCurrentSource current.plant)
      (recordedADCWirePacket (finiteADCPhysicalCurrentSource current.plant) current.plant.val
        (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode current.plant.property)
        current.fits)) leg channel : ℚ) : ℝ) = _
  rw [unpack_recordedADCWirePacket_current]
  rw [finiteADCDigitalLegRatio_cast_eq _ _ _ _
    (ne_of_gt (finiteADCDigitalWordDifference_span_pos _ _ leg channel))]
  exact congrArg (fun run => finiteADCClockedDecodedLegAt
    (finiteADCPhysicalCurrentSource current.plant) run leg channel) current.plant.property.symm

theorem quantizationError_original (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) :
    quantizationError current leg channel =
      finiteADCClockedDecodedLegAt (finiteADCPhysicalCurrentSource current.plant)
          current.plant.val leg channel -
        finiteADCClockedAnalogLegAt (finiteADCPhysicalCurrentSource current.plant)
          current.plant.val.drive leg channel := by
  have generated := compiledFiniteADCClockedDecodedLeg_sub_analog_eq
    (finiteADCPhysicalCurrentSource current.plant) current.plant.val.drive leg channel
  have same : current.plant.val = compileFiniteADCClockedNoisyMeteredSynchronousSample
    (finiteADCPhysicalCurrentSource current.plant) current.plant.val.drive := current.plant.property
  rw [← same] at generated
  have raw := congrArg (fun run => run.rawVoltageAt .operational leg channel) current.plant.property
  change current.plant.val.rawVoltageAt .operational leg channel =
    finiteADCClockedRawVoltageAt (finiteADCPhysicalCurrentSource current.plant)
      current.plant.val.drive .operational leg channel at raw
  rw [← raw] at generated
  exact generated.symm

theorem quantizationError_bound (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) :
    |quantizationError current leg channel| < (1 : ℝ) / 249750 := by
  rw [quantizationError_original]
  have generated := compiledFiniteADCClockedDecodedLeg_error_lt
    (finiteADCPhysicalCurrentSource current.plant) current.plant.val.drive leg channel
  have same : current.plant.val = compileFiniteADCClockedNoisyMeteredSynchronousSample
    (finiteADCPhysicalCurrentSource current.plant) current.plant.val.drive := current.plant.property
  rw [← same] at generated
  exact generated

theorem correctedLeg_original (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) :
    correctedLeg current.packet leg channel =
      (match leg with
      | .resistor => resonantActualNormalizedResistorAt hardware.meteredSource.fixture.coreSource
          (binaryDriveState current.plant.val.drive) current.plant.val.initial channel
          current.plant.val.executedDuration
      | .inductor => resonantActualNormalizedInductorAt hardware.meteredSource.fixture.coreSource
          (binaryDriveState current.plant.val.drive) current.plant.val.initial channel
          current.plant.val.executedDuration) + quantizationError current leg channel := by
  have generated := finiteADCClockedAnalogLeg_eq_actual_add_noise
    (finiteADCPhysicalCurrentSource current.plant) current.plant.val.drive leg channel
  have duration := congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.executedDuration
    current.plant.property
  change current.plant.val.executedDuration =
    finiteADCClockedSampleTime (finiteADCPhysicalCurrentSource current.plant) current.plant.val.drive at duration
  rw [← duration] at generated
  have time : (⟨headerSeconds current.packet⟩ : SISecond) = current.plant.val.executedDuration := by
    apply SIQuantity.ext
    exact (packet_duration current).symm
  unfold correctedLeg
  rw [decodedLeg_original, time, quantizationError_original]
  dsimp only [finiteADCPhysicalCurrentSource, finiteADCFixtureWithInitial] at generated
  change finiteADCClockedAnalogLegAt (finiteADCPhysicalCurrentSource current.plant)
    current.plant.val.drive leg channel = _ at generated
  rw [generated]
  cases leg <;> ring

end
end FiniteADCWholeJointCurrent.Information.Packet.Recipient
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
