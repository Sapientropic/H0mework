import H0mework.Computation.ADCReceiver.RawReceiverMachine

/-!
# Raw occurrence generates the old typed receiver as a logical restriction

The commuting law holds on every raw state. Only the local range guard is
needed for offset cancellation; final acceptance is generated later.
Iteration is transported by the existing semiconjugacy theorem.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

theorem finiteADCRawDifferenceRegisters_eq
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacket source counterBits lastTick) :
    finiteADCRawDifferenceRegisters checked =
      finiteADCReceiverDifferenceRegisters (unpackADCWirePacket source checked.packet) := by
  unfold finiteADCRawDifferenceRegisters finiteADCRawDifferenceRegistersFor
    finiteADCReceiverDifferenceRegisters
  congr 1
  · funext channel
    exact finiteADCRawDifference128_eq_decodedDifference source.adcCode _ _
      (checked.valid.2 .operational .resistor channel)
      (checked.valid.2 .zeroReference .resistor channel)
  · funext channel
    exact finiteADCRawDifference128_eq_decodedDifference source.adcCode _ _
      (checked.valid.2 .spanReference .resistor channel)
      (checked.valid.2 .zeroReference .resistor channel)
  · funext channel
    exact finiteADCRawDifference128_eq_decodedDifference source.adcCode _ _
      (checked.valid.2 .operational .inductor channel)
      (checked.valid.2 .zeroReference .inductor channel)
  · funext channel
    exact finiteADCRawDifference128_eq_decodedDifference source.adcCode _ _
      (checked.valid.2 .spanReference .inductor channel)
      (checked.valid.2 .zeroReference .inductor channel)

theorem finiteADCRawCalibrationGate_checked_iff
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacket source counterBits lastTick) :
    finiteADCRawCalibrationGateRun source lastTick checked.packet = true ↔
      validADCEnergyCalibration (unpackADCWirePacket source checked.packet) := by
  rw [finiteADCRawCalibrationGate_exact]
  simp only [decide_eq_true_eq]
  constructor
  · intro spans
    exact ((finiteADCRawPacketAdmission_iff source lastTick checked.packet).mp
      ⟨checked.valid.1, checked.valid.2, spans⟩).2
  · intro calibrated
    exact ((finiteADCRawPacketAdmission_iff source lastTick checked.packet).mpr
      ⟨checked.valid, calibrated⟩).2.2

theorem finiteADCRawReceiverStep_commutes
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {counterBits lastTick : Nat} :
    Function.Semiconj
      (@finiteADCRawReceiverReadout source counterBits lastTick)
      finiteADCRawReceiverStep finiteADCReceiverMachineStep := by
  intro state
  cases state with
  | captured packet =>
      by_cases accepted : finiteADCRawPacketGateRun source lastTick packet = true
      · have valid : validADCWirePacket source lastTick packet :=
          (⟨packet, accepted⟩ : FiniteADCRangeCheckedRawPacket source counterBits lastTick).valid
        simp [finiteADCRawReceiverStep, finiteADCRawReceiverReadout,
          finiteADCReceiverMachineStep, parseADCWirePacket, accepted, valid]
      · have invalid : ¬ validADCWirePacket source lastTick packet := by
          intro valid
          apply accepted
          rw [finiteADCRawPacketGate_exact]
          exact decide_eq_true valid
        simp [finiteADCRawReceiverStep, finiteADCRawReceiverReadout,
          finiteADCReceiverMachineStep, parseADCWirePacket, accepted, invalid]
  | parsed packet =>
      cases packet with
      | none => rfl
      | some checked =>
          simp [finiteADCRawReceiverStep, finiteADCRawReceiverReadout,
            finiteADCReceiverMachineStep, finiteADCRawCalibrationGate_checked_iff]
          split_ifs <;> rfl
  | calibrated packet =>
      cases packet with
      | none => rfl
      | some checked =>
          simp only [finiteADCRawReceiverStep, finiteADCRawReceiverReadout,
            finiteADCReceiverMachineStep, Option.map_some, finiteADCRawDifferenceRegisters_eq]
  | differenced registers =>
      simp only [finiteADCRawReceiverStep, finiteADCRawReceiverReadout,
        finiteADCReceiverMachineStep, finiteADCGateSquareRegisters_eq]
  | squared registers =>
      simp only [finiteADCRawReceiverStep, finiteADCRawReceiverReadout,
        finiteADCReceiverMachineStep, finiteADCGateProductRegisters_eq]
  | products registers =>
      simp only [finiteADCRawReceiverStep, finiteADCRawReceiverReadout,
        finiteADCReceiverMachineStep, finiteADCGateSumRegisters_eq]
  | summed registers =>
      simp only [finiteADCRawReceiverStep, finiteADCRawReceiverReadout,
        finiteADCReceiverMachineStep, finiteADCGateScaledRegisters_eq]
  | scaled registers =>
      simp only [finiteADCRawReceiverStep, finiteADCRawReceiverReadout,
        finiteADCReceiverMachineStep, finiteADCGateScaledDecision_eq]
  | done _ => rfl

theorem finiteADCRawReceiverAfter_commutes
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (ticks : Nat) :
    finiteADCRawReceiverReadout (finiteADCRawReceiverAfter source lastTick packet ticks) =
      finiteADCReceiverMachineAfter source lastTick packet ticks :=
  (finiteADCRawReceiverStep_commutes.iterate_right ticks) (.captured packet)

theorem finiteADCRawReceiverOutput_eq
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {counterBits lastTick : Nat}
    (state : FiniteADCRawReceiverState source counterBits lastTick) :
    finiteADCRawReceiverOutput state =
      finiteADCReceiverMachineOutput (finiteADCRawReceiverReadout state) := by
  cases state <;> rfl

theorem finiteADCRawReceiver_completed
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCRawReceiverOutput
      (finiteADCRawReceiverAfter source lastTick packet finiteADCReceiverMachineTicks) =
        some (receiveADC128WirePacket source lastTick packet) := by
  rw [finiteADCRawReceiverOutput_eq, finiteADCRawReceiverAfter_commutes,
    finiteADCReceiverMachine_completed]

theorem finiteADCRawReceiver_not_completed_early
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (ticks : Nat)
    (early : ticks < finiteADCReceiverMachineTicks) :
    finiteADCRawReceiverOutput (finiteADCRawReceiverAfter source lastTick packet ticks) = none := by
  rw [finiteADCRawReceiverOutput_eq, finiteADCRawReceiverAfter_commutes]
  exact finiteADCReceiverMachine_not_completed_early source lastTick packet ticks early

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
