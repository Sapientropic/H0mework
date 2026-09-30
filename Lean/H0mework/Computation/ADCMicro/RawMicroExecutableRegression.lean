import H0mework.Computation.ADCMicro.RawMicroCorrectness

/-!
# Independently specified raw-integer microreceiver fixtures

These packets are literal digital test inputs, not analog-source receipts or
precomputed receiver verdicts. Both calibration legs have a nonzero span; the
operational resistor rows specify the excitation pattern and inductor rows
stay at the zero reference.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Regression

open Physical.Interface
open Netlist.Dissipative.Dimensioned.Driven.Producer
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingCortex.FinitePrecision

def executableRawZero : QuantizedWord (adcWordBits .coarse) := ⟨4000000, by decide⟩
def executableRawSpan : QuantizedWord (adcWordBits .coarse) := ⟨4250000, by decide⟩

def executableAllHighPacket : FiniteADCWirePacketFor .coarse 3 :=
  (⟨3, by decide⟩, fun frame leg _ => match frame, leg with
    | .zeroReference, _ => executableRawZero
    | .spanReference, _ => executableRawSpan
    | .operational, .resistor => executableRawSpan
    | .operational, .inductor => executableRawZero)

def executableMixedPacket : FiniteADCWirePacketFor .coarse 3 :=
  (⟨3, by decide⟩, fun frame leg channel => match frame, leg with
    | .zeroReference, _ => executableRawZero
    | .spanReference, _ => executableRawSpan
    | .operational, .inductor => executableRawZero
    | .operational, .resistor => match channel with
      | .machineToNeuralWrite | .learnedStateTrace | .noPowerMinting => executableRawSpan
      | _ => executableRawZero)

def executableBadSpanPacket : FiniteADCWirePacketFor .coarse 3 :=
  (executableMixedPacket.1, fun frame leg channel => match frame, leg, channel with
    | .spanReference, .inductor, .sourceBound => executableRawZero
    | _, _, _ => executableMixedPacket.2 frame leg channel)

def executableUnusedWordPacket : FiniteADCWirePacketFor .coarse 3 :=
  (executableMixedPacket.1, fun frame leg channel => match frame, leg, channel with
    | .operational, .resistor, .sourceBound => ⟨8388607, by decide⟩
    | _, _, _ => executableMixedPacket.2 frame leg channel)

/-- A finite presentation of the already returned output, suitable for executable diagnostics. -/
def executableMicroReadout (output : Option (Option FiniteBinaryDrive)) :
    Option (Option (Vector Bool 10)) :=
  output.map (Option.map fun drive =>
    Vector.ofFn fun index : Fin 10 => drive (finiteADCChannelEquivFin.symm index))

theorem executable_all_high_full_micro_result :
    finiteADCRawMicroOutput
      (finiteADCRawMicroAfterFor .coarse 7 executableAllHighPacket
        (finiteADCRawMicroTicksFor .coarse 3)) = some (some (uniformBinaryDrive true)) := by
  rw [finiteADCRawMicro_completedFor]
  have packetAccepted : finiteADCRawPacketGateRunFor .coarse 7 executableAllHighPacket = true := by
    rw [finiteADCRawPacketGateFor_exact]
    decide
  have calibrationAccepted :
      finiteADCRawCalibrationGateRunFor .coarse 7 executableAllHighPacket = true := by
    rw [finiteADCRawCalibrationGateFor_exact]
    decide
  simp only [finiteADCRawMicroPacketResultFor, dif_pos packetAccepted,
    finiteADCRawMicroCheckedResultFor, calibrationAccepted, ↓reduceIte]
  congr 2
  funext channel
  simp only [finiteADCRawMicroDifferenceResult, finiteADCRawMicroSquareResult,
    finiteADCRawMicroProductResult, finiteADCRawMicroSumResult, finiteADCRawMicroScaleResult,
    finiteADCRawDifferenceRegistersFor, finiteADCGateSquareRegisters, finiteADCGateProductRegisters,
    finiteADCGateSumRegisters, finiteADCGateScaledRegisters, finiteADCGateScaledDecision,
    finiteADC128GateSub_eq_sub, finiteADC128GateMul_eq_mul, finiteADC128GateAdd_eq_add,
    finiteADC128GateSLt_eq_slt, finiteADC128GateULt_eq_ult, executableAllHighPacket,
    executableRawZero, executableRawSpan, uniformBinaryDrive]
  decide

theorem executable_mixed_full_micro_result :
    finiteADCRawMicroOutput
      (finiteADCRawMicroAfterFor .coarse 7 executableMixedPacket
        (finiteADCRawMicroTicksFor .coarse 3)) =
      some (some (fun channel => decide (channel = .machineToNeuralWrite ∨
        channel = .learnedStateTrace ∨ channel = .noPowerMinting))) := by
  rw [finiteADCRawMicro_completedFor]
  have packetAccepted : finiteADCRawPacketGateRunFor .coarse 7 executableMixedPacket = true := by
    rw [finiteADCRawPacketGateFor_exact]
    decide
  have calibrationAccepted :
      finiteADCRawCalibrationGateRunFor .coarse 7 executableMixedPacket = true := by
    rw [finiteADCRawCalibrationGateFor_exact]
    decide
  simp only [finiteADCRawMicroPacketResultFor, dif_pos packetAccepted,
    finiteADCRawMicroCheckedResultFor, calibrationAccepted, ↓reduceIte]
  congr 2
  funext channel
  cases channel <;>
    simp only [finiteADCRawMicroDifferenceResult, finiteADCRawMicroSquareResult,
      finiteADCRawMicroProductResult, finiteADCRawMicroSumResult, finiteADCRawMicroScaleResult,
      finiteADCRawDifferenceRegistersFor, finiteADCGateSquareRegisters, finiteADCGateProductRegisters,
      finiteADCGateSumRegisters, finiteADCGateScaledRegisters, finiteADCGateScaledDecision,
      finiteADC128GateSub_eq_sub, finiteADC128GateMul_eq_mul, finiteADC128GateAdd_eq_add,
      finiteADC128GateSLt_eq_slt, finiteADC128GateULt_eq_ult, executableMixedPacket,
      executableRawZero, executableRawSpan] <;> decide

theorem executable_header_rejection :
    finiteADCRawMicroOutput
      (finiteADCRawMicroAfterFor .coarse 2 executableAllHighPacket
        (finiteADCRawMicroTicksFor .coarse 3)) = some none := by
  rw [finiteADCRawMicro_completedFor]
  have rejected : ¬ finiteADCRawPacketGateRunFor .coarse 2 executableAllHighPacket = true := by
    rw [finiteADCRawPacketGateFor_exact]
    decide
  simp only [finiteADCRawMicroPacketResultFor, dif_neg rejected]

theorem executable_bad_span_rejection :
    finiteADCRawMicroOutput
      (finiteADCRawMicroAfterFor .coarse 7 executableBadSpanPacket
        (finiteADCRawMicroTicksFor .coarse 3)) = some none := by
  rw [finiteADCRawMicro_completedFor]
  have accepted : finiteADCRawPacketGateRunFor .coarse 7 executableBadSpanPacket = true := by
    rw [finiteADCRawPacketGateFor_exact]
    decide
  have rejected : ¬ finiteADCRawCalibrationGateRunFor .coarse 7 executableBadSpanPacket = true := by
    rw [finiteADCRawCalibrationGateFor_exact]
    decide
  simp only [finiteADCRawMicroPacketResultFor, dif_pos accepted,
    finiteADCRawMicroCheckedResultFor, if_neg rejected]

theorem executable_unused_word_rejection :
    finiteADCRawMicroOutput
      (finiteADCRawMicroAfterFor .coarse 7 executableUnusedWordPacket
        (finiteADCRawMicroTicksFor .coarse 3)) = some none := by
  rw [finiteADCRawMicro_completedFor]
  have rejected : ¬ finiteADCRawPacketGateRunFor .coarse 7 executableUnusedWordPacket = true := by
    rw [finiteADCRawPacketGateFor_exact]
    decide
  simp only [finiteADCRawMicroPacketResultFor, dif_neg rejected]

end Netlist.Dissipative.Dimensioned.Driven.Regression
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
