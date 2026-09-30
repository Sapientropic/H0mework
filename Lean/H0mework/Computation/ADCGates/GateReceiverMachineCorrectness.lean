import H0mework.Computation.ADCGates.GateReceiverMachine

/-!
# Same-state gate refinement of the clocked receiver

These equalities compare two realizations of the same registered operations,
not unrelated physical occurrences. The gate-executed step preserves the
complete phase payload, hence all finite iterates and both rejection routes.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

theorem finiteADCGateDifferenceRegisters_eq
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource} :
    (finiteADCGateDifferenceRegisters (source := source)) = finiteADCReceiverDifferenceRegisters := by
  funext sample
  simp only [finiteADCGateDifferenceRegisters, finiteADC128GateSub_eq_sub,
    finiteADCReceiverDifferenceRegisters, finiteADCBitVectorDifference128]

theorem finiteADCGateSquareRegisters_eq :
    finiteADCGateSquareRegisters = finiteADCReceiverSquareRegisters := by
  funext input
  simp only [finiteADCGateSquareRegisters, finiteADC128GateMul_eq_mul, finiteADCReceiverSquareRegisters]

theorem finiteADCGateProductRegisters_eq :
    finiteADCGateProductRegisters = finiteADCReceiverProductRegisters := by
  funext input
  simp only [finiteADCGateProductRegisters, finiteADC128GateMul_eq_mul, finiteADCReceiverProductRegisters]

theorem finiteADCGateSumRegisters_eq :
    finiteADCGateSumRegisters = finiteADCReceiverSumRegisters := by
  funext input
  simp only [finiteADCGateSumRegisters, finiteADC128GateAdd_eq_add, finiteADCReceiverSumRegisters]

theorem finiteADCGateScaledRegisters_eq :
    finiteADCGateScaledRegisters = finiteADCReceiverScaledRegisters := by
  funext input
  simp only [finiteADCGateScaledRegisters, finiteADC128GateMul_eq_mul, finiteADCReceiverScaledRegisters]

theorem finiteADCGateScaledDecision_eq :
    finiteADCGateScaledDecision = finiteADCReceiverScaledDecision := by
  funext input channel
  simp only [finiteADCGateScaledDecision, finiteADC128GateSLt_eq_slt,
    finiteADC128GateULt_eq_ult, finiteADCReceiverScaledDecision]

/-- Whole register-state equality, stronger than agreement of only the final bit. -/
theorem finiteADCGateReceiverMachineStep_eq
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource} {counterBits : Nat} :
    @finiteADCGateReceiverMachineStep source counterBits = finiteADCReceiverMachineStep := by
  funext state
  unfold finiteADCGateReceiverMachineStep finiteADCReceiverMachineStep
  rw [finiteADCGateDifferenceRegisters_eq, finiteADCGateSquareRegisters_eq,
    finiteADCGateProductRegisters_eq, finiteADCGateSumRegisters_eq,
    finiteADCGateScaledRegisters_eq, finiteADCGateScaledDecision_eq]
  cases state <;> rfl

theorem finiteADCGateReceiverMachineAfter_eq
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (ticks : Nat) :
    finiteADCGateReceiverMachineAfter source lastTick packet ticks =
      finiteADCReceiverMachineAfter source lastTick packet ticks := by
  unfold finiteADCGateReceiverMachineAfter finiteADCReceiverMachineAfter
  rw [finiteADCGateReceiverMachineStep_eq]

theorem finiteADCGateReceiverMachine_completed
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCReceiverMachineOutput
      (finiteADCGateReceiverMachineAfter source lastTick packet finiteADCReceiverMachineTicks) =
        some (receiveADC128WirePacket source lastTick packet) := by
  rw [finiteADCGateReceiverMachineAfter_eq, finiteADCReceiverMachine_completed]

theorem finiteADCGateReceiverMachine_not_completed_early
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (ticks : Nat)
    (early : ticks < finiteADCReceiverMachineTicks) :
    finiteADCReceiverMachineOutput
      (finiteADCGateReceiverMachineAfter source lastTick packet ticks) = none := by
  rw [finiteADCGateReceiverMachineAfter_eq]
  exact finiteADCReceiverMachine_not_completed_early source lastTick packet ticks early

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
