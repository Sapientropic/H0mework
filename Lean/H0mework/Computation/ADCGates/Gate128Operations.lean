import Std.Tactic.BVDecide.Bitblast.BVExpr
import H0mework.Computation.AIGExecution.AIGVectorExecutionSource

/-!
# Fixed AIGs for the 128-bit ADC arithmetic path

Each graph in this file is compiled once from a two-variable expression.  Its
`AIG.decls`, `AIG.hdag`, and output references are public and contain no runtime
operand.  Runtime values enter only through the assignment used to denote the
fixed graph.  This is an arithmetic gate refinement, not a physical propagation
delay or transistor implementation claim.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat
open Std.Tactic.BVDecide

abbrev FiniteADCBitVec128 := BitVec 128

/-- Public graph carrier for a 128-bit result. -/
abbrev FiniteADC128GateWordGraph := AIG.RefVecEntry BVBit 128

/-- The two runtime operands occupy variables zero and one. -/
def finiteADC128GateAssignment
    (left right : FiniteADCBitVec128) : BVExpr.Assignment :=
  .branch 1 (.leaf { bv := left }) (.leaf { bv := right })

/-- Compile a word expression to a public AIG plus 128 output references. -/
def finiteADC128GateCompileWord
    (expr : BVExpr 128) : FiniteADC128GateWordGraph :=
  (BVExpr.bitblast AIG.empty { val := expr, cache := BVExpr.Cache.empty }).result.val

/-- Execute one shared table, then read all 128 output references from it. -/
def finiteADC128GateReadWord
    (graph : FiniteADC128GateWordGraph)
    (left right : FiniteADCBitVec128) : FiniteADCBitVec128 :=
  aigExecutionReadVector graph (finiteADC128GateAssignment left right).toAIGAssignment

/-- Read one Boolean AIG under the same two-operand assignment. -/
def finiteADC128GateReadBool
    (graph : AIG.Entrypoint BVBit)
    (left right : FiniteADCBitVec128) : Bool :=
  aigExecutionRead (finiteADC128GateAssignment left right).toAIGAssignment graph.ref

def finiteADC128GateAddExpr : BVExpr 128 :=
  .bin (.var 0) .add (.var 1)

def finiteADC128GateMulExpr : BVExpr 128 :=
  .bin (.var 0) .mul (.var 1)

/-- Subtraction lowered to `left + (not right + 1)` before bitblasting. -/
def finiteADC128GateSubExpr : BVExpr 128 :=
  .bin (.var 0) .add
    (.bin (.un .not (.var 1)) .add (.const (BitVec.ofNat 128 1)))

def finiteADC128GateULtExpr : BVLogicalExpr :=
  .literal (.bin (.var 0 : BVExpr 128) .ult (.var 1 : BVExpr 128))

/-- Signed less-than is `(left.msb xor right.msb) xor left.ult right`,
the Boolean identity used by `BitVec.slt_eq_ult`. -/
def finiteADC128GateSLtExpr : BVLogicalExpr :=
  .gate .xor
    (.gate .xor
      (.literal (.getLsbD (.var 0 : BVExpr 128) 127))
      (.literal (.getLsbD (.var 1 : BVExpr 128) 127)))
    finiteADC128GateULtExpr

/-- Fixed, operand-independent public AIGs. -/
def finiteADC128GateAddGraph : FiniteADC128GateWordGraph :=
  finiteADC128GateCompileWord finiteADC128GateAddExpr

def finiteADC128GateMulGraph : FiniteADC128GateWordGraph :=
  finiteADC128GateCompileWord finiteADC128GateMulExpr

def finiteADC128GateSubGraph : FiniteADC128GateWordGraph :=
  finiteADC128GateCompileWord finiteADC128GateSubExpr

def finiteADC128GateULtGraph : AIG.Entrypoint BVBit :=
  BVLogicalExpr.bitblast finiteADC128GateULtExpr

def finiteADC128GateSLtGraph : AIG.Entrypoint BVBit :=
  BVLogicalExpr.bitblast finiteADC128GateSLtExpr

/-- Public value APIs evaluate the fixed AIGs rather than calling the old
`BitVec` arithmetic operations. -/
def finiteADC128GateSub
    (left right : FiniteADCBitVec128) : FiniteADCBitVec128 :=
  finiteADC128GateReadWord finiteADC128GateSubGraph left right

def finiteADC128GateMul
    (left right : FiniteADCBitVec128) : FiniteADCBitVec128 :=
  finiteADC128GateReadWord finiteADC128GateMulGraph left right

def finiteADC128GateAdd
    (left right : FiniteADCBitVec128) : FiniteADCBitVec128 :=
  finiteADC128GateReadWord finiteADC128GateAddGraph left right

def finiteADC128GateSLt
    (left right : FiniteADCBitVec128) : Bool :=
  finiteADC128GateReadBool finiteADC128GateSLtGraph left right

def finiteADC128GateULt
    (left right : FiniteADCBitVec128) : Bool :=
  finiteADC128GateReadBool finiteADC128GateULtGraph left right

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
