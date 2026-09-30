import H0mework.Physics.LCQuantization.Coupling

/-!
# Finite parallel-LC embodiment netlist topology

This file declares the finite wiring carrier used by the first circuit-level
realization of the quantized embodiment coupling family.  Every channel owns
two electrical nodes and two parallel reactive branches.  A channel-indexed
output-gain stage, one directed parasitic slot, and one independent endpoint
bias-source slot complete the finite inventory.

No differential law, solved trajectory, endpoint operator, tolerance, body,
or consciousness verdict is stored in the topology.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Netlist
namespace Interface

open Physical.Interface

inductive ParallelLCLocalNode where
  | signal
  | reference
  deriving DecidableEq, Repr, FintypeViaProxy

inductive ParallelLCCoreElementKind where
  | inductor
  | capacitor
  deriving DecidableEq, Repr, FintypeViaProxy

inductive ParallelLCGlobalElementKind where
  | directedCrosstalk
  | endpointBiasSource
  deriving DecidableEq, Repr, FintypeViaProxy

abbrev FiniteParallelLCNode :=
  FiniteEmbodimentChannel × ParallelLCLocalNode

abbrev FiniteParallelLCCoreElement :=
  FiniteEmbodimentChannel × ParallelLCCoreElementKind

/-- Twenty reactive elements, ten channel output-gain stages, one directed
parasitic slot, and one independent bias-source slot. -/
abbrev FiniteParallelLCNetlistElement :=
  FiniteParallelLCCoreElement ⊕
    (FiniteEmbodimentChannel ⊕ ParallelLCGlobalElementKind)

theorem finiteParallelLCNode_cardinality :
    Fintype.card FiniteParallelLCNode = 20 := by
  decide

theorem finiteParallelLCCoreElement_cardinality :
    Fintype.card FiniteParallelLCCoreElement = 20 := by
  decide

theorem finiteParallelLCNetlistElement_cardinality :
    Fintype.card FiniteParallelLCNetlistElement = 32 := by
  decide

/-- Both reactive branches are oriented from the signal node toward the
reference node. -/
def parallelLCCoreElementSource
    (_element : ParallelLCCoreElementKind) : ParallelLCLocalNode :=
  .signal

def parallelLCCoreElementTarget
    (_element : ParallelLCCoreElementKind) : ParallelLCLocalNode :=
  .reference

/-- Signed node/branch incidence for the fixed two-node parallel topology. -/
def parallelLCCoreIncidence :
    ParallelLCLocalNode → ParallelLCCoreElementKind → ℤ
  | .signal, _ => -1
  | .reference, _ => 1

theorem parallelLCCoreIncidence_source
    (element : ParallelLCCoreElementKind) :
    parallelLCCoreIncidence (parallelLCCoreElementSource element) element = -1 :=
  rfl

theorem parallelLCCoreIncidence_target
    (element : ParallelLCCoreElementKind) :
    parallelLCCoreIncidence (parallelLCCoreElementTarget element) element = 1 :=
  rfl

end Interface
end Netlist
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Interface.finiteParallelLCNode_cardinality
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Interface.finiteParallelLCNetlistElement_cardinality
