import H0mework.Computation.ADCGates.Gate128Operations

/-!
# Correctness of the fixed 128-bit ADC AIGs

The proofs consume the standard library's verified bitblaster semantics.  They
do not evaluate the large multiplication graph by reduction and use neither a
SAT oracle nor `native_decide`.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat
open Std.Tactic.BVDecide

private theorem finiteADC128GateAssignment_eval_left
    (left right : FiniteADCBitVec128) :
    BVExpr.eval (finiteADC128GateAssignment left right) (.var 0 : BVExpr 128) = left := by
  rw [BVExpr.eval_var]
  change left.truncate 128 = left
  simp

private theorem finiteADC128GateAssignment_eval_right
    (left right : FiniteADCBitVec128) :
    BVExpr.eval (finiteADC128GateAssignment left right) (.var 1 : BVExpr 128) = right := by
  rw [BVExpr.eval_var]
  change right.truncate 128 = right
  simp

/-- Reading the public output references of a bitblasted word graph agrees
bit-for-bit with evaluation of its source expression. -/
theorem finiteADC128GateReadWord_compile_eq_eval
    (expr : BVExpr 128) (left right : FiniteADCBitVec128) :
    finiteADC128GateReadWord (finiteADC128GateCompileWord expr) left right =
      BVExpr.eval (finiteADC128GateAssignment left right) expr := by
  apply BitVec.eq_of_getLsbD_eq
  intro idx hidx
  unfold finiteADC128GateReadWord
  rw [aigExecutionReadVector_getLsbD _ _ (⟨idx, hidx⟩ : Fin 128)]
  exact BVExpr.denote_bitblast AIG.empty
    { val := expr, cache := BVExpr.Cache.empty }
    _ (BVExpr.Cache.Inv_empty _) idx hidx

/-- Denoting a public Boolean graph agrees with its source logical expression. -/
theorem finiteADC128GateReadBool_bitblast_eq_eval
    (expr : BVLogicalExpr) (left right : FiniteADCBitVec128) :
    finiteADC128GateReadBool (BVLogicalExpr.bitblast expr) left right =
      BVLogicalExpr.eval (finiteADC128GateAssignment left right) expr := by
  unfold finiteADC128GateReadBool
  rw [aigExecutionRead_eq_denote]
  exact BVLogicalExpr.denote_bitblast expr (finiteADC128GateAssignment left right)

theorem finiteADC128GateSub_eq_sub
    (left right : FiniteADCBitVec128) :
    finiteADC128GateSub left right = left - right := by
  rw [finiteADC128GateSub, finiteADC128GateSubGraph,
    finiteADC128GateReadWord_compile_eq_eval]
  rw [finiteADC128GateSubExpr, BVExpr.eval_bin, BVBinOp.eval_add,
    finiteADC128GateAssignment_eval_left, BVExpr.eval_bin, BVBinOp.eval_add,
    BVExpr.eval_un, BVUnOp.eval_not, finiteADC128GateAssignment_eval_right,
    BVExpr.eval_const]
  rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add]

theorem finiteADC128GateMul_eq_mul
    (left right : FiniteADCBitVec128) :
    finiteADC128GateMul left right = left * right := by
  rw [finiteADC128GateMul, finiteADC128GateMulGraph,
    finiteADC128GateReadWord_compile_eq_eval]
  rw [finiteADC128GateMulExpr, BVExpr.eval_bin, BVBinOp.eval_mul,
    finiteADC128GateAssignment_eval_left, finiteADC128GateAssignment_eval_right]

theorem finiteADC128GateAdd_eq_add
    (left right : FiniteADCBitVec128) :
    finiteADC128GateAdd left right = left + right := by
  rw [finiteADC128GateAdd, finiteADC128GateAddGraph,
    finiteADC128GateReadWord_compile_eq_eval]
  rw [finiteADC128GateAddExpr, BVExpr.eval_bin, BVBinOp.eval_add,
    finiteADC128GateAssignment_eval_left, finiteADC128GateAssignment_eval_right]

theorem finiteADC128GateULt_eq_ult
    (left right : FiniteADCBitVec128) :
    finiteADC128GateULt left right = left.ult right := by
  rw [finiteADC128GateULt, finiteADC128GateULtGraph,
    finiteADC128GateReadBool_bitblast_eq_eval]
  rw [finiteADC128GateULtExpr, BVLogicalExpr.eval_literal, BVPred.eval_bin,
    BVBinPred.eval_ult, finiteADC128GateAssignment_eval_left,
    finiteADC128GateAssignment_eval_right]

theorem finiteADC128GateSLt_eq_slt
    (left right : FiniteADCBitVec128) :
    finiteADC128GateSLt left right = left.slt right := by
  rw [finiteADC128GateSLt, finiteADC128GateSLtGraph,
    finiteADC128GateReadBool_bitblast_eq_eval]
  rw [finiteADC128GateSLtExpr, BVLogicalExpr.eval_gate, BVLogicalExpr.eval_gate,
    BVLogicalExpr.eval_literal, BVPred.eval_getLsbD,
    finiteADC128GateAssignment_eval_left, BVLogicalExpr.eval_literal,
    BVPred.eval_getLsbD, finiteADC128GateAssignment_eval_right,
    finiteADC128GateULtExpr, BVLogicalExpr.eval_literal, BVPred.eval_bin,
    BVBinPred.eval_ult, finiteADC128GateAssignment_eval_left,
    finiteADC128GateAssignment_eval_right,
    BitVec.getLsbD_eq_getElem (by omega : 127 < 128),
    BitVec.getLsbD_eq_getElem (by omega : 127 < 128)]
  rw [BitVec.slt_eq_ult]
  rfl

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
