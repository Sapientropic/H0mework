import H0mework.Computation.ADCMicro.RawMicroRank
import H0mework.Computation.ADCMicro.RawPhaseCallsCorrectness
import H0mework.Computation.ADCReceiver.RawReceiverCorrectness

/-!
# Correctness of the declaration-clocked raw receiver

The residual below is proof-side only. It composes the arithmetic still owed by
the current phase, but is never stored or evaluated by the runtime machine.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat
open Std.Tactic.BVDecide

def finiteADCRawMicroScaleResult
    (input : FiniteADCReceiverScaledRegisters) : FiniteBinaryDrive :=
  finiteADCGateScaledDecision input

def finiteADCRawMicroSumResult
    (input : FiniteADCReceiverSumRegisters) : FiniteBinaryDrive :=
  finiteADCRawMicroScaleResult (finiteADCGateScaledRegisters input)

def finiteADCRawMicroProductResult
    (input : FiniteADCReceiverProductRegisters) : FiniteBinaryDrive :=
  finiteADCRawMicroSumResult (finiteADCGateSumRegisters input)

def finiteADCRawMicroSquareResult
    (input : FiniteADCReceiverSquareRegisters) : FiniteBinaryDrive :=
  finiteADCRawMicroProductResult (finiteADCGateProductRegisters input)

def finiteADCRawMicroDifferenceResult
    (input : FiniteADCReceiverDifferenceRegisters) : FiniteBinaryDrive :=
  finiteADCRawMicroSquareResult (finiteADCGateSquareRegisters input)

def finiteADCRawMicroCheckedResultFor
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) :
    Option FiniteBinaryDrive :=
  if finiteADCRawCalibrationGateRunFor code lastTick checked.packet = true then
    some (finiteADCRawMicroDifferenceResult (finiteADCRawDifferenceRegistersFor checked))
  else none

def finiteADCRawMicroPacketResultFor
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) : Option FiniteBinaryDrive :=
  if accepted : finiteADCRawPacketGateRunFor code lastTick packet = true then
    finiteADCRawMicroCheckedResultFor
      (⟨packet, accepted⟩ : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick)
  else none

/-- Legacy physical-source view of the code-only packet result. -/
abbrev finiteADCRawMicroPacketResult
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) : Option FiniteBinaryDrive :=
  finiteADCRawMicroPacketResultFor source.adcCode lastTick packet

/-- Graph-parametric proof-side fold. Keeping the graph family abstract prevents
the logical residual from unfolding any installed AIG declaration array. -/
def finiteADCRawMicroResidualAt
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    {packetGraph calibrationGraph subGraph mulGraph addGraph signedGraph unsignedGraph : AIG BVBit}
    (finish : ∀ (_spanAnd : FiniteADCRawBooleanRegisters)
      (input : FiniteADCReceiverScaledRegisters)
      (unsignedCurrent : AIGOwnedBatch unsignedGraph
        (finiteADCRawUnsignedComparePhaseAssignments input)),
      unsignedGraph.decls.size ≤ unsignedCurrent.ticks → FiniteADCRawBooleanRegisters) :
    FiniteADCRawMicroStateAt code counterBits lastTick packetGraph calibrationGraph
        subGraph mulGraph addGraph signedGraph unsignedGraph → Option FiniteBinaryDrive
  | .packet raw _ => finiteADCRawMicroPacketResultFor code lastTick raw
  | .calibration checked _ => finiteADCRawMicroCheckedResultFor checked
  | .difference checked _ =>
      some (finiteADCRawMicroDifferenceResult (finiteADCRawDifferenceRegistersFor checked))
  | .square input _ => some (finiteADCRawMicroDifferenceResult input)
  | .product input _ => some (finiteADCRawMicroSquareResult input)
  | .sum input _ => some (finiteADCRawMicroProductResult input)
  | .scale input _ => some (finiteADCRawMicroSumResult input)
  | .compare input _ _ => some (finiteADCRawMicroScaleResult input)
  | .finalAnd spanAnd input unsignedCurrent complete =>
      some (finiteADCRawBooleanReadout (finish spanAnd input unsignedCurrent complete))
  | .done result => result.map finiteADCRawBooleanReadout

/-- Potential final result of the installed microstate. This proof-only
projection is absent from `FiniteADCRawMicroState`. -/
def finiteADCRawMicroResidual
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (state : FiniteADCRawMicroStateFor code counterBits lastTick) : Option FiniteBinaryDrive :=
  finiteADCRawMicroResidualAt
    (fun spanAnd input unsignedCurrent complete =>
      finiteADCRawFinalCompareRegisters spanAnd input unsignedCurrent complete)
    state

theorem finiteADCRawMicroResidual_step
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (state : FiniteADCRawMicroStateFor code counterBits lastTick) :
    finiteADCRawMicroResidual (finiteADCRawMicroStep state) =
      finiteADCRawMicroResidual state := by
  cases state with
  | packet raw current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · rename_i complete
        split
        · rename_i accepted
          rw [finiteADCRawProgramPacketOutput_eq] at accepted
          simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt,
            finiteADCRawMicroPacketResultFor, accepted]
        · rename_i rejected
          rw [finiteADCRawProgramPacketOutput_eq] at rejected
          simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt,
            finiteADCRawMicroPacketResultFor, rejected]
      · simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]
  | calibration checked current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · rename_i complete
        split
        · rename_i accepted
          rw [finiteADCRawProgramCalibrationOutput_eq] at accepted
          simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt,
            finiteADCRawMicroCheckedResultFor, accepted]
        · rename_i rejected
          rw [finiteADCRawProgramCalibrationOutput_eq] at rejected
          simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt,
            finiteADCRawMicroCheckedResultFor, rejected]
      · simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]
  | difference checked current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · rw [finiteADCRawDifferencePhaseOutput_eq]
        simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]
      · simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]
  | square input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · rw [finiteADCRawSquarePhaseOutput_eq]
        simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt,
          finiteADCRawMicroDifferenceResult]
      · simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]
  | product input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · rw [finiteADCRawProductPhaseOutput_eq]
        simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt,
          finiteADCRawMicroSquareResult]
      · simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]
  | sum input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · rw [finiteADCRawSumPhaseOutput_eq]
        simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt,
          finiteADCRawMicroProductResult]
      · simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]
  | scale input current =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · rw [finiteADCRawScalePhaseOutput_eq]
        simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt,
          finiteADCRawMicroSumResult]
      · simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]
  | compare input signedCurrent unsignedCurrent =>
      simp only [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram]
      split
      · simp only [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]
        rw [finiteADCRawFinalCompareRegisters_readout_eq,
          finiteADCRawSpanAndRegisters_readout_eq,
          finiteADCRawFinalCompareOutput_of_spanAnd_eq]
        rfl
      · simp [finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]
  | finalAnd spanAnd input unsignedCurrent complete =>
      simp [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram,
        finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]
  | done result =>
      simp [finiteADCRawMicroStep, finiteADCRawMicroStepWithProgram,
        finiteADCRawMicroResidual, finiteADCRawMicroResidualAt]

/-- The proof-side residual is constant along the actual microclock trace. -/
theorem finiteADCRawMicroResidual_after
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (state : FiniteADCRawMicroStateFor code counterBits lastTick) (ticks : Nat) :
    finiteADCRawMicroResidual ((finiteADCRawMicroStep^[ticks]) state) =
      finiteADCRawMicroResidual state := by
  have semiconj : Function.Semiconj
      (@finiteADCRawMicroResidual code counterBits lastTick)
      (@finiteADCRawMicroStep code counterBits lastTick) id :=
    fun current => finiteADCRawMicroResidual_step current
  simpa only [Function.iterate_id, id_eq] using semiconj.iterate_right ticks state

theorem finiteADCRawMicroResidual_bootFor
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    finiteADCRawMicroResidual (finiteADCRawMicroBootFor code lastTick packet) =
      finiteADCRawMicroPacketResultFor code lastTick packet := rfl

theorem finiteADCRawMicroPacketResult_eq_receive
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCRawMicroPacketResultFor source.adcCode lastTick packet =
      receiveADC128WirePacket source lastTick packet := by
  have completed := finiteADCRawReceiver_completed source lastTick packet
  rw [finiteADCReceiverMachineTicks_eq] at completed
  by_cases accepted : finiteADCRawPacketGateRunFor source.adcCode lastTick packet = true
  · let checked : FiniteADCRangeCheckedRawPacket source counterBits lastTick := ⟨packet, accepted⟩
    by_cases calibrated :
        finiteADCRawCalibrationGateRunFor source.adcCode lastTick packet = true
    · have generated :
          finiteADCRawReceiverOutput (finiteADCRawReceiverAfter source lastTick packet 8) =
            some (finiteADCRawMicroPacketResultFor source.adcCode lastTick packet) := by
        simp [finiteADCRawReceiverAfter, finiteADCRawReceiverStep,
          finiteADCRawReceiverOutput, Function.iterate_succ_apply',
          finiteADCRawPacketGateRun, finiteADCRawCalibrationGateRun,
          finiteADCRawMicroPacketResultFor,
          finiteADCRawMicroCheckedResultFor, finiteADCRawDifferenceRegisters, accepted, calibrated,
          finiteADCRawMicroDifferenceResult, finiteADCRawMicroSquareResult,
          finiteADCRawMicroProductResult, finiteADCRawMicroSumResult,
          finiteADCRawMicroScaleResult]
      exact Option.some.inj (generated.symm.trans completed)
    · have generated :
          finiteADCRawReceiverOutput (finiteADCRawReceiverAfter source lastTick packet 8) =
            some (finiteADCRawMicroPacketResultFor source.adcCode lastTick packet) := by
        simp [finiteADCRawReceiverAfter, finiteADCRawReceiverStep,
          finiteADCRawReceiverOutput, Function.iterate_succ_apply',
          finiteADCRawPacketGateRun, finiteADCRawCalibrationGateRun,
          finiteADCRawMicroPacketResultFor,
          finiteADCRawMicroCheckedResultFor, accepted, calibrated,
          ]
      exact Option.some.inj (generated.symm.trans completed)
  · have generated :
        finiteADCRawReceiverOutput (finiteADCRawReceiverAfter source lastTick packet 8) =
          some (finiteADCRawMicroPacketResultFor source.adcCode lastTick packet) := by
      simp [finiteADCRawReceiverAfter, finiteADCRawReceiverStep,
        finiteADCRawReceiverOutput, Function.iterate_succ_apply',
        finiteADCRawPacketGateRun, finiteADCRawMicroPacketResultFor, accepted]
    exact Option.some.inj (generated.symm.trans completed)

theorem finiteADCRawMicroResidual_boot
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCRawMicroResidual (finiteADCRawMicroBoot source lastTick packet) =
      receiveADC128WirePacket source lastTick packet := by
  exact finiteADCRawMicroPacketResult_eq_receive source lastTick packet

theorem finiteADCRawMicroOutput_eq_residual_of_some
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (state : FiniteADCRawMicroStateFor code counterBits lastTick)
    (result : Option FiniteBinaryDrive)
    (output : finiteADCRawMicroOutput state = some result) :
    finiteADCRawMicroResidual state = result := by
  cases state <;> try { cases output }
  case done stored =>
    have outer : some (stored.map finiteADCRawBooleanReadout) = some result := by
      simpa only [finiteADCRawMicroOutput] using output
    have equality : stored.map finiteADCRawBooleanReadout = result := Option.some.inj outer
    rw [← equality]
    rfl

/-- Every code-indexed raw packet reaches the graph-generated deadline with its
independently generated code-only packet result. -/
theorem finiteADCRawMicro_completedFor
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    finiteADCRawMicroOutput
        (finiteADCRawMicroAfterFor code lastTick packet
          (finiteADCRawMicroTicksFor code counterBits)) =
      some (finiteADCRawMicroPacketResultFor code lastTick packet) := by
  let terminal := finiteADCRawMicroAfterFor code lastTick packet
    (finiteADCRawMicroTicksFor code counterBits)
  have zero : finiteADCRawMicroRemaining terminal = 0 :=
    finiteADCRawMicroAfterFor_remaining_zero code lastTick packet
  rcases (finiteADCRawMicroRemaining_zero_iff_output terminal).mp zero with
    ⟨result, output⟩
  have residual : finiteADCRawMicroResidual terminal = result :=
    finiteADCRawMicroOutput_eq_residual_of_some terminal result output
  have exact : finiteADCRawMicroResidual terminal =
      finiteADCRawMicroPacketResultFor code lastTick packet := by
    rw [show terminal =
      (finiteADCRawMicroStep^[finiteADCRawMicroTicksFor code counterBits])
        (finiteADCRawMicroBootFor code lastTick packet) from rfl,
      finiteADCRawMicroResidual_after,
      finiteADCRawMicroResidual_bootFor]
  rw [output]
  exact congrArg some (residual.symm.trans exact)

/-- Any source-owned installed program computes the same code-indexed result.
Program uniqueness erases only its source-identical graph representation; no
packet result or acceptance witness is stored in the program. -/
theorem finiteADCRawMicro_completedWithProgram
    {code : FiniteADCResolutionCode}
    {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits)
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits) :
    finiteADCRawMicroOutput
        (finiteADCRawMicroAfterWithProgram program lastTick packet
          (finiteADCRawMicroTicksFor code counterBits)) =
      some (finiteADCRawMicroPacketResultFor code lastTick packet) := by
  rw [program.eq_compile]
  simpa only [finiteADCRawMicroAfterFor] using
    finiteADCRawMicro_completedFor code lastTick packet

/-- Running the stored program to its own graph-derived deadline exposes the
same code-indexed packet result. -/
theorem finiteADCRawMicroExecute_completed
    {code : FiniteADCResolutionCode}
    {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits)
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits) :
    finiteADCRawMicroOutput (finiteADCRawMicroExecute program lastTick packet) =
      some (finiteADCRawMicroPacketResultFor code lastTick packet) := by
  unfold finiteADCRawMicroExecute
  rw [finiteADCRawMicroTicksWithProgram_eq]
  exact finiteADCRawMicro_completedWithProgram program lastTick packet

/-- The code-facing executor compiles once and then consumes that installed
program for both execution and its deadline. -/
theorem finiteADCRawMicroExecuteFor_completed
    (code : FiniteADCResolutionCode)
    {counterBits : Nat}
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits) :
    finiteADCRawMicroOutput (finiteADCRawMicroExecuteFor code lastTick packet) =
      some (finiteADCRawMicroPacketResultFor code lastTick packet) := by
  simpa only [finiteADCRawMicroExecuteFor] using
    finiteADCRawMicroExecute_completed
      (compileFiniteADCRawInstalledProgram code counterBits) lastTick packet

/-- The physical-source specialization keeps the established executable
receiver statement without reintroducing source dependence into the engine. -/
theorem finiteADCRawMicro_completed
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    finiteADCRawMicroOutput
        (finiteADCRawMicroAfter source lastTick packet
          (finiteADCRawMicroTicks source counterBits)) =
      some (receiveADC128WirePacket source lastTick packet) := by
  rw [finiteADCRawMicro_completedFor,
    finiteADCRawMicroPacketResult_eq_receive]

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
