import H0mework.Computation.ADCMicro.RawPhaseCalls

/-!
# Exact outputs of raw receiver microclock calls

Completed phase assemblers read only their owned cached tables. These theorems
identify the resulting payloads with the existing raw receiver phase functions;
the old operations occur only on the specification side of the equalities.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat
open Std.Tactic.BVDecide

theorem finiteADCRawWordBatchRead_eq
    {jobs : Nat} (graph : FiniteADC128GateWordGraph)
    (assign : Fin jobs → BVBit → Bool) (current : AIGOwnedBatch graph.aig assign)
    (complete : graph.aig.decls.size ≤ current.ticks) (job : Fin jobs) :
    finiteADCRawWordBatchRead graph assign current complete job =
      aigExecutionReadVector graph (assign job) := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  unfold finiteADCRawWordBatchRead
  rw [BitVec.iunfoldr_getLsbD (state := fun _ => ())
    (i := (⟨index, bound⟩ : Fin 128)) (ind := by intro; rfl)]
  rw [aigOwnedBatchReadAt_eq_read, aigExecutionRead_eq_denote]
  symm
  exact aigExecutionReadVector_getLsbD graph (assign job) ⟨index, bound⟩

theorem finiteADCRawBoolBatchRead_eq
    {jobs : Nat} (graph : AIG.Entrypoint BVBit)
    (assign : Fin jobs → BVBit → Bool) (current : AIGOwnedBatch graph.aig assign)
    (complete : graph.aig.decls.size ≤ current.ticks) (job : Fin jobs) :
    finiteADCRawBoolBatchRead graph assign current complete job =
      aigExecutionRead (assign job) graph.ref :=
  aigOwnedBatchReadAt_eq_read current complete job graph.ref

theorem finiteADCRawPacketPhaseOutput_eq
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits)
    (current : AIGOwnedProgress (finiteADCRawPacketGraph code counterBits).aig
      (finiteADCRawPacketPhaseAssignment code lastTick packet))
    (complete : (finiteADCRawPacketGraph code counterBits).aig.decls.size ≤
      current.ticks) :
    finiteADCRawPacketPhaseOutput code lastTick packet current complete =
      finiteADCRawPacketGateRunFor code lastTick packet := by
  unfold finiteADCRawPacketPhaseOutput finiteADCRawPacketGateRunFor
  change aigOwnedProgressReadAt current _ _ =
    aigExecutionRead (finiteADCRawPacketPhaseAssignment code lastTick packet) _
  exact aigOwnedProgressReadAt_eq_read current _ _

theorem finiteADCRawCalibrationPhaseOutput_eq
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick)
    (current : AIGOwnedProgress (finiteADCRawCalibrationGraph code).aig
      (finiteADCRawCalibrationPhaseAssignment checked))
    (complete : (finiteADCRawCalibrationGraph code).aig.decls.size ≤ current.ticks) :
    finiteADCRawCalibrationPhaseOutput checked current complete =
      finiteADCRawCalibrationGateRunFor code lastTick checked.packet := by
  unfold finiteADCRawCalibrationPhaseOutput finiteADCRawCalibrationGateRunFor
  change aigOwnedProgressReadAt current _ _ =
    aigExecutionRead (finiteADCRawCalibrationPhaseAssignment checked) _
  exact aigOwnedProgressReadAt_eq_read current _ _

theorem finiteADCRawDifferencePhaseOutput_eq
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick)
    (current : AIGOwnedBatch finiteADC128GateSubGraph.aig
      (finiteADCRawDifferencePhaseAssignments checked))
    (complete : finiteADC128GateSubGraph.aig.decls.size ≤ current.ticks) :
    finiteADCRawDifferencePhaseOutput checked current complete =
      finiteADCRawDifferenceRegistersFor checked := by
  unfold finiteADCRawDifferencePhaseOutput finiteADCRawDifferenceRegistersFor
  simp only [Vector.getElem_ofFn]
  congr 1
  all_goals
    funext channel
    rw [finiteADCRawWordBatchRead_eq]
    simp [finiteADCRawDifferencePhaseAssignments, finiteADCRawDifferencePhaseOperands,
      FiniteADCPhaseBinaryOperands.assignment, finiteADC128GateSub,
      finiteADC128GateReadWord]

theorem finiteADCRawSquarePhaseOutput_eq
    (input : FiniteADCReceiverDifferenceRegisters)
    (current : AIGOwnedBatch finiteADC128GateMulGraph.aig
      (finiteADCRawSquarePhaseAssignments input))
    (complete : finiteADC128GateMulGraph.aig.decls.size ≤ current.ticks) :
    finiteADCRawSquarePhaseOutput input current complete =
      finiteADCGateSquareRegisters input := by
  unfold finiteADCRawSquarePhaseOutput finiteADCGateSquareRegisters
  simp only [Vector.getElem_ofFn]
  congr 1
  all_goals
    funext channel
    rw [finiteADCRawWordBatchRead_eq]
    simp [finiteADCRawSquarePhaseAssignments, finiteADCRawSquarePhaseOperands,
      finiteADCQuadratureRegisterAt, FiniteADCPhaseBinaryOperands.assignment,
      finiteADC128GateMul, finiteADC128GateReadWord]

theorem finiteADCRawProductPhaseOutput_eq
    (input : FiniteADCReceiverSquareRegisters)
    (current : AIGOwnedBatch finiteADC128GateMulGraph.aig
      (finiteADCRawProductPhaseAssignments input))
    (complete : finiteADC128GateMulGraph.aig.decls.size ≤ current.ticks) :
    finiteADCRawProductPhaseOutput input current complete =
      finiteADCGateProductRegisters input := by
  unfold finiteADCRawProductPhaseOutput finiteADCGateProductRegisters
  simp only [Vector.getElem_ofFn]
  congr 1
  all_goals
    funext channel
    rw [finiteADCRawWordBatchRead_eq]
    simp [finiteADCRawProductPhaseAssignments, finiteADCRawProductPhaseOperands,
      FiniteADCPhaseBinaryOperands.assignment, finiteADC128GateMul,
      finiteADC128GateReadWord]

theorem finiteADCRawSumPhaseOutput_eq
    (input : FiniteADCReceiverProductRegisters)
    (current : AIGOwnedBatch finiteADC128GateAddGraph.aig
      (finiteADCRawSumPhaseAssignments input))
    (complete : finiteADC128GateAddGraph.aig.decls.size ≤ current.ticks) :
    finiteADCRawSumPhaseOutput input current complete = finiteADCGateSumRegisters input := by
  unfold finiteADCRawSumPhaseOutput finiteADCGateSumRegisters
  simp only [Vector.getElem_ofFn]
  congr 1
  funext channel
  rw [finiteADCRawWordBatchRead_eq]
  simp [finiteADCRawSumPhaseAssignments, finiteADCRawSumPhaseOperands,
    FiniteADCPhaseBinaryOperands.assignment, finiteADC128GateAdd,
    finiteADC128GateReadWord]

theorem finiteADCRawScalePhaseOutput_eq
    (input : FiniteADCReceiverSumRegisters)
    (current : AIGOwnedBatch finiteADC128GateMulGraph.aig
      (finiteADCRawScalePhaseAssignments input))
    (complete : finiteADC128GateMulGraph.aig.decls.size ≤ current.ticks) :
    finiteADCRawScalePhaseOutput input current complete = finiteADCGateScaledRegisters input := by
  unfold finiteADCRawScalePhaseOutput finiteADCGateScaledRegisters
  simp only [Vector.getElem_ofFn]
  congr 1
  funext channel
  rw [finiteADCRawWordBatchRead_eq]
  simp [finiteADCRawScalePhaseAssignments, finiteADCRawScalePhaseOperands,
    FiniteADCPhaseBinaryOperands.assignment, finiteADC128GateMul,
    finiteADC128GateReadWord]

theorem finiteADCRawSpanAndRegisters_readout_eq
    (input : FiniteADCReceiverScaledRegisters)
    (signedCurrent : AIGOwnedBatch finiteADC128GateSLtGraph.aig
      (finiteADCRawSignedComparePhaseAssignments input))
    (signedComplete : finiteADC128GateSLtGraph.aig.decls.size ≤ signedCurrent.ticks) :
    finiteADCRawBooleanReadout
        (finiteADCRawSpanAndRegisters input signedCurrent signedComplete) =
      finiteADCRawSpanAndOutput input signedCurrent signedComplete := rfl

theorem finiteADCRawFinalCompareRegisters_readout_eq
    (spanAnd : FiniteADCRawBooleanRegisters) (input : FiniteADCReceiverScaledRegisters)
    (unsignedCurrent : AIGOwnedBatch finiteADC128GateULtGraph.aig
      (finiteADCRawUnsignedComparePhaseAssignments input))
    (unsignedComplete : finiteADC128GateULtGraph.aig.decls.size ≤ unsignedCurrent.ticks) :
    finiteADCRawBooleanReadout
        (finiteADCRawFinalCompareRegisters spanAnd input unsignedCurrent unsignedComplete) =
      finiteADCRawFinalCompareOutput (finiteADCRawBooleanReadout spanAnd)
        input unsignedCurrent unsignedComplete := by
  funext channel
  simp only [finiteADCRawBooleanReadout, finiteADCRawFinalCompareRegisters,
    finiteADCRawFinalCompareOutput, Vector.getElem_ofFn, Equiv.apply_symm_apply]

theorem finiteADCRawSpanAndOutput_eq
    (input : FiniteADCReceiverScaledRegisters)
    (signedCurrent : AIGOwnedBatch finiteADC128GateSLtGraph.aig
      (finiteADCRawSignedComparePhaseAssignments input))
    (signedComplete : finiteADC128GateSLtGraph.aig.decls.size ≤ signedCurrent.ticks) :
    finiteADCRawSpanAndOutput input signedCurrent signedComplete =
      fun channel =>
        finiteADC128GateSLt (BitVec.zero 128) (input.resistorSpan channel) &&
          finiteADC128GateSLt (BitVec.zero 128) (input.inductorSpan channel) := by
  funext channel
  unfold finiteADCRawSpanAndOutput finiteADCRawBooleanReadout finiteADCRawSpanAndRegisters
  simp only [Vector.getElem_ofFn]
  rw [finiteADCRawBoolBatchRead_eq, finiteADCRawBoolBatchRead_eq]
  simp [finiteADCRawSignedComparePhaseAssignments,
    finiteADCRawSignedComparePhaseOperands, FiniteADCPhaseBinaryOperands.assignment,
    finiteADC128GateSLt, finiteADC128GateReadBool]

theorem finiteADCRawFinalCompareOutput_eq
    (spanAnd : FiniteBinaryDrive) (input : FiniteADCReceiverScaledRegisters)
    (unsignedCurrent : AIGOwnedBatch finiteADC128GateULtGraph.aig
      (finiteADCRawUnsignedComparePhaseAssignments input))
    (unsignedComplete : finiteADC128GateULtGraph.aig.decls.size ≤ unsignedCurrent.ticks) :
    finiteADCRawFinalCompareOutput spanAnd input unsignedCurrent unsignedComplete =
      fun channel =>
        spanAnd channel &&
          finiteADC128GateULt (input.thresholdDenominator channel)
            (input.scaledEnergyNumerator channel) := by
  funext channel
  unfold finiteADCRawFinalCompareOutput
  simp only [Vector.getElem_ofFn]
  rw [finiteADCRawBoolBatchRead_eq]
  simp [finiteADCRawUnsignedComparePhaseAssignments,
    finiteADCRawUnsignedComparePhaseOperands, FiniteADCPhaseBinaryOperands.assignment,
    finiteADC128GateULt, finiteADC128GateReadBool]

theorem finiteADCRawFinalCompareOutput_of_spanAnd_eq
    (input : FiniteADCReceiverScaledRegisters)
    (signedCurrent : AIGOwnedBatch finiteADC128GateSLtGraph.aig
      (finiteADCRawSignedComparePhaseAssignments input))
    (unsignedCurrent : AIGOwnedBatch finiteADC128GateULtGraph.aig
      (finiteADCRawUnsignedComparePhaseAssignments input))
    (signedComplete : finiteADC128GateSLtGraph.aig.decls.size ≤ signedCurrent.ticks)
    (unsignedComplete : finiteADC128GateULtGraph.aig.decls.size ≤ unsignedCurrent.ticks) :
    finiteADCRawFinalCompareOutput
        (finiteADCRawSpanAndOutput input signedCurrent signedComplete)
        input unsignedCurrent unsignedComplete = finiteADCGateScaledDecision input := by
  rw [finiteADCRawFinalCompareOutput_eq, finiteADCRawSpanAndOutput_eq]
  rfl

@[simp] theorem finiteADCRawPhaseCommitTicks_eq : finiteADCRawPhaseCommitTicks = 1 := rfl

theorem finiteADCRawPhaseCommitTicks_pos : 0 < finiteADCRawPhaseCommitTicks := by decide

@[simp] theorem finiteADCRawSpanAndControlTicks_eq : finiteADCRawSpanAndControlTicks = 1 := rfl

theorem finiteADCRawSpanAndControlTicks_pos : 0 < finiteADCRawSpanAndControlTicks := by decide

@[simp] theorem finiteADCRawFinalCompareControlTicks_eq :
    finiteADCRawFinalCompareControlTicks = 1 := rfl

theorem finiteADCRawFinalCompareControlTicks_pos :
    0 < finiteADCRawFinalCompareControlTicks := by decide

theorem finiteADCRawSignedCompare_ticks_le :
    finiteADC128GateSLtGraph.aig.decls.size ≤ finiteADCRawComparePhaseGraphTicks :=
  le_max_left _ _

theorem finiteADCRawUnsignedCompare_ticks_le :
    finiteADC128GateULtGraph.aig.decls.size ≤ finiteADCRawComparePhaseGraphTicks :=
  le_max_right _ _

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
