import H0mework.Computation.ADCMicro.RawInstalledProgram

/-!
# Actual raw receiver microclock

A work state holds only the current phase payload and its source-owned partial
tables. Each work tick advances one declaration per parallel job. Completed
tables generate the next payload in an explicit control tick. The two final
Boolean conjunctions occupy separate control ticks.

The installed schedule comes from graph sizes, not packet success. Rejected
packets reach an absorbing rejection state and may idle until the same deadline.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

/-- Graph-parametric storage keeps construction and proof elimination independent
of circuit expansion. The runtime below installs the fixed source graphs. -/
inductive FiniteADCRawMicroStateAt
    (code : FiniteADCResolutionCode)
    (counterBits lastTick : Nat)
    (packetGraph calibrationGraph subGraph mulGraph addGraph signedGraph unsignedGraph :
      Std.Sat.AIG Std.Tactic.BVDecide.BVBit) where
  | packet (raw : FiniteADCWirePacketFor code counterBits)
      (current : AIGOwnedProgress packetGraph
        (finiteADCRawPacketPhaseAssignment code lastTick raw))
  | calibration (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick)
      (current : AIGOwnedProgress calibrationGraph
        (finiteADCRawCalibrationPhaseAssignment checked))
  | difference (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick)
      (current : AIGOwnedBatch subGraph
        (finiteADCRawDifferencePhaseAssignments checked))
  | square (input : FiniteADCReceiverDifferenceRegisters)
      (current : AIGOwnedBatch mulGraph
        (finiteADCRawSquarePhaseAssignments input))
  | product (input : FiniteADCReceiverSquareRegisters)
      (current : AIGOwnedBatch mulGraph
        (finiteADCRawProductPhaseAssignments input))
  | sum (input : FiniteADCReceiverProductRegisters)
      (current : AIGOwnedBatch addGraph
        (finiteADCRawSumPhaseAssignments input))
  | scale (input : FiniteADCReceiverSumRegisters)
      (current : AIGOwnedBatch mulGraph
        (finiteADCRawScalePhaseAssignments input))
  | compare (input : FiniteADCReceiverScaledRegisters)
      (signedCurrent : AIGOwnedBatch signedGraph
        (finiteADCRawSignedComparePhaseAssignments input))
      (unsignedCurrent : AIGOwnedBatch unsignedGraph
        (finiteADCRawUnsignedComparePhaseAssignments input))
  | finalAnd (spanAnd : Vector Bool 10) (input : FiniteADCReceiverScaledRegisters)
      (unsignedCurrent : AIGOwnedBatch unsignedGraph
        (finiteADCRawUnsignedComparePhaseAssignments input))
      (complete : unsignedGraph.decls.size ≤ unsignedCurrent.ticks)
  | done (result : Option (Vector Bool 10))

/-- Work tables are indexed by the same actual immutable program graphs. -/
abbrev FiniteADCRawMicroStateWithProgram
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits) (lastTick : Nat) :=
  FiniteADCRawMicroStateAt code counterBits lastTick
    program.packetGraph.aig program.calibrationGraph.aig
    finiteADC128GateSubGraph.aig finiteADC128GateMulGraph.aig finiteADC128GateAddGraph.aig
    finiteADC128GateSLtGraph.aig finiteADC128GateULtGraph.aig

/-- The source-facing type specializes the same stored-program carrier. -/
abbrev FiniteADCRawMicroStateFor (code : FiniteADCResolutionCode) (counterBits lastTick : Nat) :=
  FiniteADCRawMicroStateWithProgram (compileFiniteADCRawInstalledProgram code counterBits) lastTick

def finiteADCRawMicroStepWithProgram
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat} (program : FiniteADCRawInstalledProgram code counterBits) :
    FiniteADCRawMicroStateWithProgram program lastTick →
      FiniteADCRawMicroStateWithProgram program lastTick
  | .packet raw current =>
      if complete : program.packetGraph.aig.decls.size ≤ current.ticks then
        if accepted : finiteADCRawProgramPacketOutput program lastTick raw current complete = true then
          let checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick :=
            ⟨raw, (finiteADCRawProgramPacketOutput_eq program lastTick raw current complete).symm.trans
              accepted⟩
          .calibration checked (finiteADCRawProgramCalibrationCall program checked)
        else .done none
      else .packet raw (aigOwnedProgressStep current)
  | .calibration checked current =>
      if complete : program.calibrationGraph.aig.decls.size ≤ current.ticks then
        if finiteADCRawProgramCalibrationOutput program checked current complete then
          .difference checked (finiteADCRawDifferencePhaseCall checked)
        else .done none
      else .calibration checked (aigOwnedProgressStep current)
  | .difference checked current =>
      if complete : finiteADC128GateSubGraph.aig.decls.size ≤ current.ticks then
        let output := finiteADCRawDifferencePhaseOutput checked current complete
        .square output (finiteADCRawSquarePhaseCall output)
      else .difference checked (aigOwnedBatchStep current)
  | .square input current =>
      if complete : finiteADC128GateMulGraph.aig.decls.size ≤ current.ticks then
        let output := finiteADCRawSquarePhaseOutput input current complete
        .product output (finiteADCRawProductPhaseCall output)
      else .square input (aigOwnedBatchStep current)
  | .product input current =>
      if complete : finiteADC128GateMulGraph.aig.decls.size ≤ current.ticks then
        let output := finiteADCRawProductPhaseOutput input current complete
        .sum output (finiteADCRawSumPhaseCall output)
      else .product input (aigOwnedBatchStep current)
  | .sum input current =>
      if complete : finiteADC128GateAddGraph.aig.decls.size ≤ current.ticks then
        let output := finiteADCRawSumPhaseOutput input current complete
        .scale output (finiteADCRawScalePhaseCall output)
      else .sum input (aigOwnedBatchStep current)
  | .scale input current =>
      if complete : finiteADC128GateMulGraph.aig.decls.size ≤ current.ticks then
        let output := finiteADCRawScalePhaseOutput input current complete
        .compare output (finiteADCRawSignedComparePhaseCall output)
          (finiteADCRawUnsignedComparePhaseCall output)
      else .scale input (aigOwnedBatchStep current)
  | .compare input signedCurrent unsignedCurrent =>
      if complete : finiteADC128GateSLtGraph.aig.decls.size ≤ signedCurrent.ticks ∧
          finiteADC128GateULtGraph.aig.decls.size ≤ unsignedCurrent.ticks then
        .finalAnd (finiteADCRawSpanAndRegisters input signedCurrent complete.1)
          input unsignedCurrent complete.2
      else .compare input (aigOwnedBatchStep signedCurrent) (aigOwnedBatchStep unsignedCurrent)
  | .finalAnd spanAnd input unsignedCurrent complete =>
      .done (some (finiteADCRawFinalCompareRegisters spanAnd input unsignedCurrent complete))
  | .done result => .done result

abbrev finiteADCRawMicroStep
    {code : FiniteADCResolutionCode} {counterBits lastTick : Nat} :
    FiniteADCRawMicroStateFor code counterBits lastTick →
      FiniteADCRawMicroStateFor code counterBits lastTick :=
  finiteADCRawMicroStepWithProgram (compileFiniteADCRawInstalledProgram code counterBits)

def finiteADCRawMicroBootWithProgram
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits) (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    FiniteADCRawMicroStateWithProgram program lastTick :=
  .packet packet (finiteADCRawProgramPacketCall program lastTick packet)

abbrev finiteADCRawMicroBootFor (code : FiniteADCResolutionCode) {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits) :=
  finiteADCRawMicroBootWithProgram (compileFiniteADCRawInstalledProgram code counterBits)
    lastTick packet

def finiteADCRawMicroAfterWithProgram
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits) (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) (ticks : Nat) :
    FiniteADCRawMicroStateWithProgram program lastTick :=
  ((finiteADCRawMicroStepWithProgram program)^[ticks])
    (finiteADCRawMicroBootWithProgram program lastTick packet)

def finiteADCRawMicroAfterFor
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) (ticks : Nat) :
    FiniteADCRawMicroStateFor code counterBits lastTick :=
  let program := compileFiniteADCRawInstalledProgram code counterBits
  finiteADCRawMicroAfterWithProgram program lastTick packet ticks

def finiteADCRawMicroOutput
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    {packetGraph calibrationGraph subGraph mulGraph addGraph signedGraph unsignedGraph :
      Std.Sat.AIG Std.Tactic.BVDecide.BVBit} :
    FiniteADCRawMicroStateAt code counterBits lastTick packetGraph calibrationGraph
      subGraph mulGraph addGraph signedGraph unsignedGraph → Option (Option FiniteBinaryDrive)
  | .done result => some (result.map finiteADCRawBooleanReadout)
  | _ => none

def finiteADCRawMicroCompareTicks : Nat :=
  finiteADCRawComparePhaseGraphTicks +
    finiteADCRawSpanAndControlTicks + finiteADCRawFinalCompareControlTicks

def finiteADCRawMicroScaleTicks : Nat :=
  finiteADC128GateMulGraph.aig.decls.size + finiteADCRawPhaseCommitTicks +
    finiteADCRawMicroCompareTicks

def finiteADCRawMicroSumTicks : Nat :=
  finiteADC128GateAddGraph.aig.decls.size + finiteADCRawPhaseCommitTicks + finiteADCRawMicroScaleTicks

def finiteADCRawMicroProductTicks : Nat :=
  finiteADC128GateMulGraph.aig.decls.size + finiteADCRawPhaseCommitTicks + finiteADCRawMicroSumTicks

def finiteADCRawMicroSquareTicks : Nat :=
  finiteADC128GateMulGraph.aig.decls.size + finiteADCRawPhaseCommitTicks + finiteADCRawMicroProductTicks

def finiteADCRawMicroDifferenceTicks : Nat :=
  finiteADC128GateSubGraph.aig.decls.size + finiteADCRawPhaseCommitTicks + finiteADCRawMicroSquareTicks

def finiteADCRawMicroCalibrationTicksFor
    (code : FiniteADCResolutionCode) : Nat :=
  (finiteADCRawCalibrationGraph code).aig.decls.size + finiteADCRawPhaseCommitTicks +
    finiteADCRawMicroDifferenceTicks

def finiteADCRawMicroTicksFor
    (code : FiniteADCResolutionCode) (counterBits : Nat) : Nat :=
  (finiteADCRawPacketGraph code counterBits).aig.decls.size + finiteADCRawPhaseCommitTicks +
    finiteADCRawMicroCalibrationTicksFor code

/-- Read the schedule from the installed graphs, without recompiling them. -/
def finiteADCRawMicroTicksWithProgram
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits) : Nat :=
  program.packetGraph.aig.decls.size + finiteADCRawPhaseCommitTicks +
    (program.calibrationGraph.aig.decls.size + finiteADCRawPhaseCommitTicks +
      finiteADCRawMicroDifferenceTicks)

theorem finiteADCRawMicroTicksWithProgram_eq
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits) :
    finiteADCRawMicroTicksWithProgram program = finiteADCRawMicroTicksFor code counterBits := by
  unfold finiteADCRawMicroTicksWithProgram finiteADCRawMicroTicksFor
    finiteADCRawMicroCalibrationTicksFor
  rw [program.packet_size_eq, program.calibration_size_eq]

/-- Complete execution consumes the already installed program for both work and deadline. -/
def finiteADCRawMicroExecute
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits) (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    FiniteADCRawMicroStateWithProgram program lastTick :=
  finiteADCRawMicroAfterWithProgram program lastTick packet (finiteADCRawMicroTicksWithProgram program)

def finiteADCRawMicroExecuteFor (code : FiniteADCResolutionCode) {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits) :
    FiniteADCRawMicroStateFor code counterBits lastTick :=
  let program := compileFiniteADCRawInstalledProgram code counterBits
  finiteADCRawMicroExecute program lastTick packet

theorem finiteADCRawMicroExecuteFor_eq_afterFor
    (code : FiniteADCResolutionCode) {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits) :
    finiteADCRawMicroExecuteFor code lastTick packet =
      finiteADCRawMicroAfterFor code lastTick packet (finiteADCRawMicroTicksFor code counterBits) := by
  unfold finiteADCRawMicroExecuteFor finiteADCRawMicroExecute finiteADCRawMicroAfterFor
  dsimp only
  rw [finiteADCRawMicroTicksWithProgram_eq]

/-- Outstanding graph work and explicit control primitives. This clock is a
derived proof-side ranking; execution itself branches only on current tables. -/
def finiteADCRawMicroRemaining
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat} :
    FiniteADCRawMicroStateFor code counterBits lastTick → Nat
  | .packet _ current =>
      (finiteADCRawPacketGraph code counterBits).aig.decls.size - current.ticks +
        1 + finiteADCRawMicroCalibrationTicksFor code
  | .calibration _ current =>
      (finiteADCRawCalibrationGraph code).aig.decls.size - current.ticks +
        1 + finiteADCRawMicroDifferenceTicks
  | .difference _ current =>
      finiteADC128GateSubGraph.aig.decls.size - current.ticks + 1 + finiteADCRawMicroSquareTicks
  | .square _ current =>
      finiteADC128GateMulGraph.aig.decls.size - current.ticks + 1 + finiteADCRawMicroProductTicks
  | .product _ current =>
      finiteADC128GateMulGraph.aig.decls.size - current.ticks + 1 + finiteADCRawMicroSumTicks
  | .sum _ current =>
      finiteADC128GateAddGraph.aig.decls.size - current.ticks + 1 + finiteADCRawMicroScaleTicks
  | .scale _ current =>
      finiteADC128GateMulGraph.aig.decls.size - current.ticks + 1 + finiteADCRawMicroCompareTicks
  | .compare _ signedCurrent unsignedCurrent =>
      max (finiteADC128GateSLtGraph.aig.decls.size - signedCurrent.ticks)
        (finiteADC128GateULtGraph.aig.decls.size - unsignedCurrent.ticks) + 2
  | .finalAnd .. => 1
  | .done _ => 0

/-- The physical source contributes exactly its installed ADC-code restriction
to this digital carrier; physical provenance remains with the packet producer. -/
abbrev FiniteADCRawMicroState
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (counterBits lastTick : Nat) :=
  FiniteADCRawMicroStateFor source.adcCode counterBits lastTick

abbrev finiteADCRawMicroBoot
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits) :=
  finiteADCRawMicroBootFor source.adcCode lastTick packet

abbrev finiteADCRawMicroAfter
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (ticks : Nat) :=
  finiteADCRawMicroAfterFor source.adcCode lastTick packet ticks

abbrev finiteADCRawMicroCalibrationTicks
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) : Nat :=
  finiteADCRawMicroCalibrationTicksFor source.adcCode

abbrev finiteADCRawMicroTicks
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) (counterBits : Nat) : Nat :=
  finiteADCRawMicroTicksFor source.adcCode counterBits

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
