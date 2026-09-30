import H0mework.Computation.WholeReceiver.GraphCompiler
import H0mework.Computation.WholeReceiver.DataflowSource
import H0mework.Computation.AIGExecution.AIGExecutionCorrectnessSource

/-! # One source graph supplies the complete raw receiver's eleven physical ports -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide

def receiverWholeGraph (code : FiniteADCResolutionCode) (counterBits : Nat) : AIG.RefVecEntry BVBit 11 :=
  compileSharedLogicalGraph (receiverDataflowOutputs code counterBits)

/-- The immutable graph is supplied once; the run builds one current table for all output reads. -/
def receiverWholeGraphRead {code : FiniteADCResolutionCode} {counterBits : Nat}
    (entry : AIG.RefVecEntry BVBit 11) (input : FiniteADCRawAdmissionInput code counterBits) : Vector Bool 11 :=
  let assign := (finiteADCRawAdmissionAssignment input).toAIGAssignment
  let table := aigExecutionRun entry.aig assign
  let complete := aigExecutionRun_size entry.aig assign
  Vector.ofFn fun index => aigExecutionReadAt table complete (entry.vec.get index.val index.isLt)

def receiverWholeDecode (output : Vector Bool 11) : Option (Vector Bool 10) :=
  if output[0] then some (Vector.ofFn fun index : Fin 10 => output[index.val + 1]) else none

theorem receiverWholeGraphRead_get
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (entry : AIG.RefVecEntry BVBit 11) (input : FiniteADCRawAdmissionInput code counterBits) (index : Fin 11) :
    (receiverWholeGraphRead entry input)[index.val] =
      AIG.denote (finiteADCRawAdmissionAssignment input).toAIGAssignment
        ⟨entry.aig, entry.vec.get index.val index.isLt⟩ := by
  simp only [receiverWholeGraphRead, Vector.getElem_ofFn]
  exact aigExecutionRun_read_eq_denote entry.aig _ _

theorem receiverWholeGraphRead_compiled
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) (index : Fin 11) :
    (receiverWholeGraphRead (receiverWholeGraph code counterBits) input)[index.val] =
      BVLogicalExpr.eval (finiteADCRawAdmissionAssignment input) (receiverDataflowOutputs code counterBits)[index.val] := by
  rw [receiverWholeGraphRead_get]
  exact compileSharedLogicalGraph_denote _ _ index

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
