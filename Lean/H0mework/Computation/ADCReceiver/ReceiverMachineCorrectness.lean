import H0mework.Computation.ADCReceiver.ReceiverMachine

/-!
# Correctness of the clocked finite-ADC receiver machine

The generated eight-step register trace agrees with the existing executable
packet receiver for every packet, including malformed packets and invalid
calibration.  No correctness premise or desired output enters the machine.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

@[simp] theorem finiteADCReceiverMachineTicks_eq :
    finiteADCReceiverMachineTicks = 8 := rfl

theorem finiteADCReceiverMachineTicks_pos :
    0 < finiteADCReceiverMachineTicks := by
  rw [finiteADCReceiverMachineTicks_eq]
  decide

private theorem finiteADCReceiverScaledDecision_eq_decode
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (sample : FiniteADCDigitalSample source) :
    finiteADCReceiverScaledDecision
        (finiteADCReceiverScaledRegisters
          (finiteADCReceiverSumRegisters
            (finiteADCReceiverProductRegisters
              (finiteADCReceiverSquareRegisters
                (finiteADCReceiverDifferenceRegisters sample))))) =
      decodeFiniteADC128EnergySample sample := by
  funext channel
  rfl

private theorem finiteADCReceiverMachine_after_eight
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCReceiverMachineOutput
        (finiteADCReceiverMachineAfter source lastTick packet 8) =
      some (receiveADC128WirePacket source lastTick packet) := by
  cases parsed : parseADCWirePacket source lastTick packet with
  | none =>
      simp [finiteADCReceiverMachineAfter, finiteADCReceiverMachineStart,
        finiteADCReceiverMachineStep, finiteADCReceiverMachineOutput,
        Function.iterate_succ_apply', receiveADC128WirePacket, parsed]
  | some sample =>
      by_cases calibrated : validADCEnergyCalibration sample
      · simp [finiteADCReceiverMachineAfter, finiteADCReceiverMachineStart,
          finiteADCReceiverMachineStep, finiteADCReceiverMachineOutput,
          Function.iterate_succ_apply', receiveADC128WirePacket, parsed, calibrated,
          finiteADCReceiverScaledDecision_eq_decode]
      · simp [finiteADCReceiverMachineAfter, finiteADCReceiverMachineStart,
          finiteADCReceiverMachineStep, finiteADCReceiverMachineOutput,
          Function.iterate_succ_apply', receiveADC128WirePacket, parsed, calibrated]

/-- After the phase-generated latency, the machine's registered result equals
the old executable receiver on every packet, including both rejection paths. -/
theorem finiteADCReceiverMachine_completed
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCReceiverMachineOutput
        (finiteADCReceiverMachineAfter source lastTick packet
          finiteADCReceiverMachineTicks) =
      some (receiveADC128WirePacket source lastTick packet) := by
  rw [finiteADCReceiverMachineTicks_eq]
  exact finiteADCReceiverMachine_after_eight source lastTick packet

/-- No packet, valid or invalid, can expose an output before the generated
terminal phase.  This rejects a caller-selected shorter processing delay. -/
theorem finiteADCReceiverMachine_not_completed_early
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (ticks : Nat)
    (early : ticks < finiteADCReceiverMachineTicks) :
    finiteADCReceiverMachineOutput
        (finiteADCReceiverMachineAfter source lastTick packet ticks) = none := by
  rw [finiteADCReceiverMachineTicks_eq] at early
  cases parsed : parseADCWirePacket source lastTick packet with
  | none =>
      interval_cases ticks <;>
        simp [finiteADCReceiverMachineAfter, finiteADCReceiverMachineStart,
          finiteADCReceiverMachineStep, finiteADCReceiverMachineOutput,
          Function.iterate_succ_apply', parsed]
  | some sample =>
      by_cases calibrated : validADCEnergyCalibration sample
      · interval_cases ticks <;>
          simp [finiteADCReceiverMachineAfter, finiteADCReceiverMachineStart,
            finiteADCReceiverMachineStep, finiteADCReceiverMachineOutput,
            Function.iterate_succ_apply', parsed, calibrated]
      · interval_cases ticks <;>
          simp [finiteADCReceiverMachineAfter, finiteADCReceiverMachineStart,
            finiteADCReceiverMachineStep, finiteADCReceiverMachineOutput,
            Function.iterate_succ_apply', parsed, calibrated]

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
