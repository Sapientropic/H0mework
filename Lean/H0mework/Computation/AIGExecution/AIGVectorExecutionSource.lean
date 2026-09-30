import Std.Sat.AIG.RefVec
import Init.Data.BitVec.Folds
import H0mework.Computation.AIGExecution.AIGExecutionCorrectnessSource

/-!
# One completed AIG table supplies every word-output bit

The graph runs once. The bit-vector fold below performs output lookups only;
it does not repeat the graph execution for each reference.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat

variable {α : Type} [DecidableEq α] [Hashable α] {width : Nat}

def aigExecutionReadVector (graph : AIG.RefVecEntry α width) (assign : α → Bool) :
    BitVec width :=
  let table := aigExecutionRun graph.aig assign
  let complete := aigExecutionRun_size graph.aig assign
  (BitVec.iunfoldr (fun index (_ : Unit) =>
    ((), aigExecutionReadAt table complete (graph.vec.get index.val index.isLt))) ()).2

theorem aigExecutionReadVector_getLsbD
    (graph : AIG.RefVecEntry α width) (assign : α → Bool) (index : Fin width) :
    (aigExecutionReadVector graph assign).getLsbD index.val =
      AIG.denote assign ⟨graph.aig, graph.vec.get index.val index.isLt⟩ := by
  unfold aigExecutionReadVector
  rw [BitVec.iunfoldr_getLsbD (state := fun _ => ()) (i := index)
    (ind := by intro; rfl)]
  exact aigExecutionRun_read_eq_denote graph.aig assign (graph.vec.get index.val index.isLt)

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
