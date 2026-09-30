import H0mework.Computation.ADCReceiver.RawReceiverMachine
import H0mework.Computation.AIGExecution.AIGOwnedBatch

/-!
# Source calls for the raw receiver's microclock phases

Each call is booted from the current phase payload and an empty owned AIG table.
No call stores a later payload or the result of `finiteADCRawReceiverStep`.
Parallel jobs share one fixed graph and clock count while retaining distinct
assignments. A one-tick control primitive explicitly accounts for registering a
completed ordinary phase. The final comparison instead uses two explicit
one-tick control primitives: span conjunction, then span-and-threshold output.
Each commit materializes its entire parallel output bank before any later
phase receives it. Boolean handoffs return vectors as data: a function-valued
handoff would allow compiler eta expansion to defer latching until channel readout.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface
open Std.Sat
open Std.Tactic.BVDecide

/-- A Boolean bank is data, so completion cannot defer its computation behind a channel argument. -/
abbrev FiniteADCRawBooleanRegisters := Vector Bool 10

/-- Compatibility readout performs only an addressed lookup in an already latched Boolean bank. -/
def finiteADCRawBooleanReadout (registers : FiniteADCRawBooleanRegisters) : FiniteBinaryDrive :=
  fun channel => registers[(finiteADCChannelEquivFin channel).val]

structure FiniteADCPhaseBinaryOperands where
  left : FiniteADCBitVec128
  right : FiniteADCBitVec128

def FiniteADCPhaseBinaryOperands.assignment
    (operands : FiniteADCPhaseBinaryOperands) : BVBit → Bool :=
  (finiteADC128GateAssignment operands.left operands.right).toAIGAssignment

inductive FiniteADCQuadratureJobKind where
  | resistorNumerator
  | resistorSpan
  | inductorNumerator
  | inductorSpan
  deriving DecidableEq, Repr

def finiteADCQuadratureJobKindEquivFin : FiniteADCQuadratureJobKind ≃ Fin 4 where
  toFun
    | .resistorNumerator => 0
    | .resistorSpan => 1
    | .inductorNumerator => 2
    | .inductorSpan => 3
  invFun index := match index.val with
    | 0 => .resistorNumerator
    | 1 => .resistorSpan
    | 2 => .inductorNumerator
    | _ => .inductorSpan
  left_inv := by intro kind; cases kind <;> rfl
  right_inv := by intro index; rcases index with ⟨index, bound⟩; interval_cases index <;> rfl

abbrev FiniteADCQuadratureJobAddress :=
  FiniteADCQuadratureJobKind × FiniteEmbodimentChannel

def finiteADCQuadratureJobAddressEquivFin : FiniteADCQuadratureJobAddress ≃ Fin 40 :=
  (finiteADCQuadratureJobKindEquivFin.prodCongr finiteADCChannelEquivFin).trans
    finProdFinEquiv

inductive FiniteADCProductJobKind where
  | thresholdDenominator
  | resistorEnergyTerm
  | inductorEnergyTerm
  deriving DecidableEq, Repr

def finiteADCProductJobKindEquivFin : FiniteADCProductJobKind ≃ Fin 3 where
  toFun
    | .thresholdDenominator => 0
    | .resistorEnergyTerm => 1
    | .inductorEnergyTerm => 2
  invFun index := match index.val with
    | 0 => .thresholdDenominator
    | 1 => .resistorEnergyTerm
    | _ => .inductorEnergyTerm
  left_inv := by intro kind; cases kind <;> rfl
  right_inv := by intro index; rcases index with ⟨index, bound⟩; interval_cases index <;> rfl

abbrev FiniteADCProductJobAddress := FiniteADCProductJobKind × FiniteEmbodimentChannel

def finiteADCProductJobAddressEquivFin : FiniteADCProductJobAddress ≃ Fin 30 :=
  (finiteADCProductJobKindEquivFin.prodCongr finiteADCChannelEquivFin).trans finProdFinEquiv

/-- Read one completed word job only from its stored owned table. -/
def finiteADCRawWordBatchRead
    {jobs : Nat} (graph : FiniteADC128GateWordGraph)
    (assign : Fin jobs → BVBit → Bool) (current : AIGOwnedBatch graph.aig assign)
    (complete : graph.aig.decls.size ≤ current.ticks) (job : Fin jobs) : FiniteADCBitVec128 :=
  (BitVec.iunfoldr (fun index (_ : Unit) =>
    ((), aigOwnedBatchReadAt current complete job (graph.vec.get index.val index.isLt))) ()).2

/-- Read one completed Boolean job only from its stored owned table. -/
def finiteADCRawBoolBatchRead
    {jobs : Nat} (graph : AIG.Entrypoint BVBit)
    (assign : Fin jobs → BVBit → Bool) (current : AIGOwnedBatch graph.aig assign)
    (complete : graph.aig.decls.size ≤ current.ticks) (job : Fin jobs) : Bool :=
  aigOwnedBatchReadAt current complete job graph.ref

def finiteADCRawPacketPhaseAssignment
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) : BVBit → Bool :=
  (finiteADCRawAdmissionAssignment
    (finiteADCRawAdmissionInputOfPacketFor code lastTick packet)).toAIGAssignment

def finiteADCRawPacketPhaseCall
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    AIGOwnedProgress (finiteADCRawPacketGraph code counterBits).aig
      (finiteADCRawPacketPhaseAssignment code lastTick packet) :=
  aigOwnedProgressBoot _ _

def finiteADCRawPacketPhaseOutput
    (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits)
    (current : AIGOwnedProgress (finiteADCRawPacketGraph code counterBits).aig
      (finiteADCRawPacketPhaseAssignment code lastTick packet))
    (complete : (finiteADCRawPacketGraph code counterBits).aig.decls.size ≤
      current.ticks) : Bool :=
  aigOwnedProgressReadAt current ((aigOwnedProgress_complete_iff current).mpr complete)
    (finiteADCRawPacketGraph code counterBits).ref

def finiteADCRawCalibrationPhaseAssignment
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) : BVBit → Bool :=
  (finiteADCRawAdmissionAssignment
    (finiteADCRawAdmissionInputOfPacketFor code lastTick checked.packet)).toAIGAssignment

def finiteADCRawCalibrationPhaseCall
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) :
    AIGOwnedProgress (finiteADCRawCalibrationGraph code).aig
      (finiteADCRawCalibrationPhaseAssignment checked) :=
  aigOwnedProgressBoot _ _

def finiteADCRawCalibrationPhaseOutput
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick)
    (current : AIGOwnedProgress (finiteADCRawCalibrationGraph code).aig
      (finiteADCRawCalibrationPhaseAssignment checked))
    (complete : (finiteADCRawCalibrationGraph code).aig.decls.size ≤ current.ticks) : Bool :=
  aigOwnedProgressReadAt current ((aigOwnedProgress_complete_iff current).mpr complete)
    (finiteADCRawCalibrationGraph code).ref

def finiteADCRawDifferencePhaseOperands
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) (job : Fin 40) :
    FiniteADCPhaseBinaryOperands :=
  let address := finiteADCQuadratureJobAddressEquivFin.symm job
  let channel := address.2
  match address.1 with
  | .resistorNumerator => ⟨BitVec.ofNat 128 (checked.packet.2 .operational .resistor channel).val,
      BitVec.ofNat 128 (checked.packet.2 .zeroReference .resistor channel).val⟩
  | .resistorSpan => ⟨BitVec.ofNat 128 (checked.packet.2 .spanReference .resistor channel).val,
      BitVec.ofNat 128 (checked.packet.2 .zeroReference .resistor channel).val⟩
  | .inductorNumerator => ⟨BitVec.ofNat 128 (checked.packet.2 .operational .inductor channel).val,
      BitVec.ofNat 128 (checked.packet.2 .zeroReference .inductor channel).val⟩
  | .inductorSpan => ⟨BitVec.ofNat 128 (checked.packet.2 .spanReference .inductor channel).val,
      BitVec.ofNat 128 (checked.packet.2 .zeroReference .inductor channel).val⟩

def finiteADCRawDifferencePhaseAssignments
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) :
    Fin 40 → BVBit → Bool := fun job => (finiteADCRawDifferencePhaseOperands checked job).assignment

def finiteADCRawDifferencePhaseCall
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) :
    AIGOwnedBatch finiteADC128GateSubGraph.aig (finiteADCRawDifferencePhaseAssignments checked) :=
  aigOwnedBatchBoot _ _

def finiteADCRawDifferencePhaseOutput
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick)
    (current : AIGOwnedBatch finiteADC128GateSubGraph.aig
      (finiteADCRawDifferencePhaseAssignments checked))
    (complete : finiteADC128GateSubGraph.aig.decls.size ≤ current.ticks) :
    FiniteADCReceiverDifferenceRegisters :=
  let words := Vector.ofFn fun job : Fin 40 =>
    finiteADCRawWordBatchRead finiteADC128GateSubGraph _ current complete job
  { resistorNumerator := fun channel =>
      words[(finiteADCQuadratureJobAddressEquivFin (.resistorNumerator, channel)).val]
    resistorSpan := fun channel =>
      words[(finiteADCQuadratureJobAddressEquivFin (.resistorSpan, channel)).val]
    inductorNumerator := fun channel =>
      words[(finiteADCQuadratureJobAddressEquivFin (.inductorNumerator, channel)).val]
    inductorSpan := fun channel =>
      words[(finiteADCQuadratureJobAddressEquivFin (.inductorSpan, channel)).val] }

def finiteADCQuadratureRegisterAt
    (input : FiniteADCReceiverDifferenceRegisters) (address : FiniteADCQuadratureJobAddress) :
    FiniteADCBitVec128 := match address.1 with
  | .resistorNumerator => input.resistorNumerator address.2
  | .resistorSpan => input.resistorSpan address.2
  | .inductorNumerator => input.inductorNumerator address.2
  | .inductorSpan => input.inductorSpan address.2

def finiteADCRawSquarePhaseOperands
    (input : FiniteADCReceiverDifferenceRegisters) (job : Fin 40) :
    FiniteADCPhaseBinaryOperands :=
  let value := finiteADCQuadratureRegisterAt input
    (finiteADCQuadratureJobAddressEquivFin.symm job)
  ⟨value, value⟩

def finiteADCRawSquarePhaseAssignments (input : FiniteADCReceiverDifferenceRegisters) :
    Fin 40 → BVBit → Bool := fun job => (finiteADCRawSquarePhaseOperands input job).assignment

def finiteADCRawSquarePhaseCall (input : FiniteADCReceiverDifferenceRegisters) :
    AIGOwnedBatch finiteADC128GateMulGraph.aig (finiteADCRawSquarePhaseAssignments input) :=
  aigOwnedBatchBoot _ _

def finiteADCRawSquarePhaseOutput
    (input : FiniteADCReceiverDifferenceRegisters)
    (current : AIGOwnedBatch finiteADC128GateMulGraph.aig
      (finiteADCRawSquarePhaseAssignments input))
    (complete : finiteADC128GateMulGraph.aig.decls.size ≤ current.ticks) :
    FiniteADCReceiverSquareRegisters :=
  let words := Vector.ofFn fun job : Fin 40 =>
    finiteADCRawWordBatchRead finiteADC128GateMulGraph _ current complete job
  { resistorSpan := input.resistorSpan
    inductorSpan := input.inductorSpan
    resistorNumeratorSquared := fun channel =>
      words[(finiteADCQuadratureJobAddressEquivFin (.resistorNumerator, channel)).val]
    resistorSpanSquared := fun channel =>
      words[(finiteADCQuadratureJobAddressEquivFin (.resistorSpan, channel)).val]
    inductorNumeratorSquared := fun channel =>
      words[(finiteADCQuadratureJobAddressEquivFin (.inductorNumerator, channel)).val]
    inductorSpanSquared := fun channel =>
      words[(finiteADCQuadratureJobAddressEquivFin (.inductorSpan, channel)).val] }

def finiteADCRawProductPhaseOperands
    (input : FiniteADCReceiverSquareRegisters) (job : Fin 30) : FiniteADCPhaseBinaryOperands :=
  let address := finiteADCProductJobAddressEquivFin.symm job
  let channel := address.2
  match address.1 with
  | .thresholdDenominator => ⟨input.resistorSpanSquared channel, input.inductorSpanSquared channel⟩
  | .resistorEnergyTerm => ⟨input.resistorNumeratorSquared channel, input.inductorSpanSquared channel⟩
  | .inductorEnergyTerm => ⟨input.inductorNumeratorSquared channel, input.resistorSpanSquared channel⟩

def finiteADCRawProductPhaseAssignments (input : FiniteADCReceiverSquareRegisters) :
    Fin 30 → BVBit → Bool := fun job => (finiteADCRawProductPhaseOperands input job).assignment

def finiteADCRawProductPhaseCall (input : FiniteADCReceiverSquareRegisters) :
    AIGOwnedBatch finiteADC128GateMulGraph.aig (finiteADCRawProductPhaseAssignments input) :=
  aigOwnedBatchBoot _ _

def finiteADCRawProductPhaseOutput
    (input : FiniteADCReceiverSquareRegisters)
    (current : AIGOwnedBatch finiteADC128GateMulGraph.aig
      (finiteADCRawProductPhaseAssignments input))
    (complete : finiteADC128GateMulGraph.aig.decls.size ≤ current.ticks) :
    FiniteADCReceiverProductRegisters :=
  let words := Vector.ofFn fun job : Fin 30 =>
    finiteADCRawWordBatchRead finiteADC128GateMulGraph _ current complete job
  { resistorSpan := input.resistorSpan
    inductorSpan := input.inductorSpan
    thresholdDenominator := fun channel =>
      words[(finiteADCProductJobAddressEquivFin (.thresholdDenominator, channel)).val]
    resistorEnergyTerm := fun channel =>
      words[(finiteADCProductJobAddressEquivFin (.resistorEnergyTerm, channel)).val]
    inductorEnergyTerm := fun channel =>
      words[(finiteADCProductJobAddressEquivFin (.inductorEnergyTerm, channel)).val] }

def finiteADCRawSumPhaseOperands
    (input : FiniteADCReceiverProductRegisters) (job : Fin 10) : FiniteADCPhaseBinaryOperands :=
  let channel := finiteADCChannelEquivFin.symm job
  ⟨input.resistorEnergyTerm channel, input.inductorEnergyTerm channel⟩

def finiteADCRawSumPhaseAssignments (input : FiniteADCReceiverProductRegisters) :
    Fin 10 → BVBit → Bool := fun job => (finiteADCRawSumPhaseOperands input job).assignment

def finiteADCRawSumPhaseCall (input : FiniteADCReceiverProductRegisters) :
    AIGOwnedBatch finiteADC128GateAddGraph.aig (finiteADCRawSumPhaseAssignments input) :=
  aigOwnedBatchBoot _ _

def finiteADCRawSumPhaseOutput
    (input : FiniteADCReceiverProductRegisters)
    (current : AIGOwnedBatch finiteADC128GateAddGraph.aig
      (finiteADCRawSumPhaseAssignments input))
    (complete : finiteADC128GateAddGraph.aig.decls.size ≤ current.ticks) :
    FiniteADCReceiverSumRegisters :=
  let words := Vector.ofFn fun job : Fin 10 =>
    finiteADCRawWordBatchRead finiteADC128GateAddGraph _ current complete job
  { resistorSpan := input.resistorSpan
    inductorSpan := input.inductorSpan
    thresholdDenominator := input.thresholdDenominator
    energySum := fun channel => words[(finiteADCChannelEquivFin channel).val] }

def finiteADCRawScalePhaseOperands
    (input : FiniteADCReceiverSumRegisters) (job : Fin 10) : FiniteADCPhaseBinaryOperands :=
  let channel := finiteADCChannelEquivFin.symm job
  ⟨BitVec.ofNat 128 4, input.energySum channel⟩

def finiteADCRawScalePhaseAssignments (input : FiniteADCReceiverSumRegisters) :
    Fin 10 → BVBit → Bool := fun job => (finiteADCRawScalePhaseOperands input job).assignment

def finiteADCRawScalePhaseCall (input : FiniteADCReceiverSumRegisters) :
    AIGOwnedBatch finiteADC128GateMulGraph.aig (finiteADCRawScalePhaseAssignments input) :=
  aigOwnedBatchBoot _ _

def finiteADCRawScalePhaseOutput
    (input : FiniteADCReceiverSumRegisters)
    (current : AIGOwnedBatch finiteADC128GateMulGraph.aig
      (finiteADCRawScalePhaseAssignments input))
    (complete : finiteADC128GateMulGraph.aig.decls.size ≤ current.ticks) :
    FiniteADCReceiverScaledRegisters :=
  let words := Vector.ofFn fun job : Fin 10 =>
    finiteADCRawWordBatchRead finiteADC128GateMulGraph _ current complete job
  { resistorSpan := input.resistorSpan
    inductorSpan := input.inductorSpan
    thresholdDenominator := input.thresholdDenominator
    scaledEnergyNumerator := fun channel => words[(finiteADCChannelEquivFin channel).val] }

def finiteADCRawSignedComparePhaseOperands
    (input : FiniteADCReceiverScaledRegisters) (job : Fin 20) : FiniteADCPhaseBinaryOperands :=
  let address := finiteADCRawSpanAddressEquivFin.symm job
  let span := match address.1 with
    | .resistor => input.resistorSpan address.2
    | .inductor => input.inductorSpan address.2
  ⟨BitVec.zero 128, span⟩

def finiteADCRawSignedComparePhaseAssignments (input : FiniteADCReceiverScaledRegisters) :
    Fin 20 → BVBit → Bool := fun job => (finiteADCRawSignedComparePhaseOperands input job).assignment

def finiteADCRawUnsignedComparePhaseOperands
    (input : FiniteADCReceiverScaledRegisters) (job : Fin 10) : FiniteADCPhaseBinaryOperands :=
  let channel := finiteADCChannelEquivFin.symm job
  ⟨input.thresholdDenominator channel, input.scaledEnergyNumerator channel⟩

def finiteADCRawUnsignedComparePhaseAssignments (input : FiniteADCReceiverScaledRegisters) :
    Fin 10 → BVBit → Bool := fun job => (finiteADCRawUnsignedComparePhaseOperands input job).assignment

def finiteADCRawSignedComparePhaseCall (input : FiniteADCReceiverScaledRegisters) :
    AIGOwnedBatch finiteADC128GateSLtGraph.aig (finiteADCRawSignedComparePhaseAssignments input) :=
  aigOwnedBatchBoot _ _

def finiteADCRawUnsignedComparePhaseCall (input : FiniteADCReceiverScaledRegisters) :
    AIGOwnedBatch finiteADC128GateULtGraph.aig (finiteADCRawUnsignedComparePhaseAssignments input) :=
  aigOwnedBatchBoot _ _

/-- First explicit control primitive materializes all ten positive-span conjunctions. -/
def finiteADCRawSpanAndRegisters
    (input : FiniteADCReceiverScaledRegisters)
    (signedCurrent : AIGOwnedBatch finiteADC128GateSLtGraph.aig
      (finiteADCRawSignedComparePhaseAssignments input))
    (signedComplete : finiteADC128GateSLtGraph.aig.decls.size ≤ signedCurrent.ticks) :
    FiniteADCRawBooleanRegisters :=
  Vector.ofFn fun job : Fin 10 =>
    let channel := finiteADCChannelEquivFin.symm job
    finiteADCRawBoolBatchRead finiteADC128GateSLtGraph _ signedCurrent signedComplete
        (finiteADCRawSpanAddressEquivFin (.resistor, channel)) &&
      finiteADCRawBoolBatchRead finiteADC128GateSLtGraph _ signedCurrent signedComplete
        (finiteADCRawSpanAddressEquivFin (.inductor, channel))

/-- Mathematical function view; runtime states store `finiteADCRawSpanAndRegisters` itself. -/
def finiteADCRawSpanAndOutput
    (input : FiniteADCReceiverScaledRegisters)
    (signedCurrent : AIGOwnedBatch finiteADC128GateSLtGraph.aig
      (finiteADCRawSignedComparePhaseAssignments input))
    (signedComplete : finiteADC128GateSLtGraph.aig.decls.size ≤ signedCurrent.ticks) :
    FiniteBinaryDrive :=
  finiteADCRawBooleanReadout (finiteADCRawSpanAndRegisters input signedCurrent signedComplete)

/-- Second control primitive consumes the first stored Boolean bank and materializes the result bank. -/
def finiteADCRawFinalCompareRegisters
    (spanAnd : FiniteADCRawBooleanRegisters) (input : FiniteADCReceiverScaledRegisters)
    (unsignedCurrent : AIGOwnedBatch finiteADC128GateULtGraph.aig
      (finiteADCRawUnsignedComparePhaseAssignments input))
    (unsignedComplete : finiteADC128GateULtGraph.aig.decls.size ≤ unsignedCurrent.ticks) :
    FiniteADCRawBooleanRegisters :=
  Vector.ofFn fun job : Fin 10 =>
    spanAnd[job.val] &&
      finiteADCRawBoolBatchRead finiteADC128GateULtGraph _ unsignedCurrent unsignedComplete job

/-- Compatibility function specification, not a runtime handoff. The concrete
microcontroller uses `finiteADCRawFinalCompareRegisters`. -/
def finiteADCRawFinalCompareOutput
    (spanAnd : FiniteBinaryDrive) (input : FiniteADCReceiverScaledRegisters)
    (unsignedCurrent : AIGOwnedBatch finiteADC128GateULtGraph.aig
      (finiteADCRawUnsignedComparePhaseAssignments input))
    (unsignedComplete : finiteADC128GateULtGraph.aig.decls.size ≤ unsignedCurrent.ticks) :
    FiniteBinaryDrive :=
  let values := Vector.ofFn fun job : Fin 10 =>
    let channel := finiteADCChannelEquivFin.symm job
    spanAnd channel &&
      finiteADCRawBoolBatchRead finiteADC128GateULtGraph _ unsignedCurrent unsignedComplete
        (finiteADCChannelEquivFin channel)
  fun channel => values[(finiteADCChannelEquivFin channel).val]

/-- Every completed phase is registered in one explicit controller tick. -/
def finiteADCRawPhaseCommitTicks : Nat := 1

def finiteADCRawSpanAndControlTicks : Nat := 1

def finiteADCRawFinalCompareControlTicks : Nat := 1

/-- The two comparison batches advance in parallel until both actual graphs finish. -/
def finiteADCRawComparePhaseGraphTicks : Nat :=
  max finiteADC128GateSLtGraph.aig.decls.size finiteADC128GateULtGraph.aig.decls.size

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
