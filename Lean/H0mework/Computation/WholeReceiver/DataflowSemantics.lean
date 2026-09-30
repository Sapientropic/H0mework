import H0mework.Computation.WholeReceiver.DataflowSource
import H0mework.Computation.ADCReceiver.RawReceiverMachine

/-!
# The shared receiver syntax consumes the original raw packet arithmetic

Word lookup uses the existing admitted variable-address theorem. The remaining
proofs connect source expression evaluation to the existing gate-operation
semantics; no runtime state, decoded packet or expected result is constructed.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface Std.Tactic.BVDecide

theorem receiverDataflowWord_eval {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) (address : FiniteADCRawWordAddress) :
    BVExpr.eval (finiteADCRawAdmissionAssignment input) (receiverDataflowWord code address) =
      BitVec.ofNat 128 (input.rawWordAt address.1.1 address.1.2 address.2).val := by
  rw [receiverDataflowWord, BVExpr.eval_extract, finiteADCRawAdmissionAssignment_word_value]
  simp [BitVec.extractLsb']

theorem receiverDataflowSubtract_eval (assignment : BVExpr.Assignment) (left right : BVExpr 128) :
    BVExpr.eval assignment (receiverDataflowSubtract left right) =
      BVExpr.eval assignment left - BVExpr.eval assignment right := by
  rw [receiverDataflowSubtract, BVExpr.eval_bin, BVBinOp.eval_add,
    BVExpr.eval_bin, BVBinOp.eval_add, BVExpr.eval_un, BVUnOp.eval_not, BVExpr.eval_const,
    BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add]

theorem receiverDataflowSquare_eval (assignment : BVExpr.Assignment) (value : BVExpr 128) :
    BVExpr.eval assignment (receiverDataflowSquare value) =
      BVExpr.eval assignment value * BVExpr.eval assignment value := by
  rw [receiverDataflowSquare, BVExpr.eval_bin, BVBinOp.eval_mul]

theorem receiverDataflowSignedLt_eval (assignment : BVExpr.Assignment) (left right : BVExpr 128) :
    BVLogicalExpr.eval assignment (receiverDataflowSignedLt left right) =
      (BVExpr.eval assignment left).slt (BVExpr.eval assignment right) := by
  rw [receiverDataflowSignedLt, BVLogicalExpr.eval_gate, BVLogicalExpr.eval_gate,
    BVLogicalExpr.eval_literal, BVPred.eval_getLsbD, BVLogicalExpr.eval_literal, BVPred.eval_getLsbD,
    BVLogicalExpr.eval_literal, BVPred.eval_bin, BVBinPred.eval_ult,
    BitVec.getLsbD_eq_getElem (by decide : 127 < 128),
    BitVec.getLsbD_eq_getElem (by decide : 127 < 128), BitVec.slt_eq_ult]
  rfl

theorem receiverDataflowDifference_eval {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) (frame : FiniteAffineMeterFrame)
    (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) :
    BVExpr.eval (finiteADCRawAdmissionAssignment input) (receiverDataflowDifference code frame leg channel) =
      BitVec.ofNat 128 (input.rawWordAt frame leg channel).val -
        BitVec.ofNat 128 (input.rawWordAt .zeroReference leg channel).val := by
  rw [receiverDataflowDifference, receiverDataflowSubtract_eval,
    receiverDataflowWord_eval, receiverDataflowWord_eval]

theorem receiverDataflowChannel_eq_scaledDecision
    {code : FiniteADCResolutionCode} {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick)
    (channel : FiniteEmbodimentChannel) :
    BVLogicalExpr.eval
        (finiteADCRawAdmissionAssignment (finiteADCRawAdmissionInputOfPacketFor code lastTick checked.packet))
        (receiverDataflowChannel code channel) =
      finiteADCGateScaledDecision
        (finiteADCGateScaledRegisters (finiteADCGateSumRegisters (finiteADCGateProductRegisters
          (finiteADCGateSquareRegisters (finiteADCRawDifferenceRegistersFor checked))))) channel := by
  simp only [receiverDataflowChannel, BVLogicalExpr.eval_gate, Gate.eval,
    receiverDataflowSignedLt_eval, BVExpr.eval_const, receiverDataflowDifference_eval,
    BVLogicalExpr.eval_literal, BVPred.eval_bin, BVBinPred.eval_ult,
    receiverDataflowDenominator, receiverDataflowScaledEnergy, receiverDataflowEnergyTerm,
    BVExpr.eval_bin, BVBinOp.eval_mul, BVBinOp.eval_add, receiverDataflowSquare_eval,
    finiteADCGateScaledDecision, finiteADCGateScaledRegisters, finiteADCGateSumRegisters,
    finiteADCGateProductRegisters, finiteADCGateSquareRegisters, finiteADCRawDifferenceRegistersFor,
    finiteADC128GateSLt_eq_slt, finiteADC128GateULt_eq_ult, finiteADC128GateSub_eq_sub,
    finiteADC128GateMul_eq_mul, finiteADC128GateAdd_eq_add]
  rfl

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
