import H0mework.Computation.DualRailAIG.DualRailLoad

/-!
# The actual positive-rail loads of one shared packet-input driver

Repeated declarations of an atom share its physical input line. Their addressed
positive-rail pin sets are all retained: external controls, the local negative
inverter's four controls, and each registered read pin. Intrinsic driver
capacitance is added once, not once per alias.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface
open scoped BigOperators

variable {α : Type} [DecidableEq α] [Hashable α]

def packetLineLoadCount (graph : AIG α) (atom : α) : Nat :=
  ∑ node : Fin graph.decls.size,
    if graph.decls[node.val] = .atom atom then dualRailLoadCount graph node false else 0

theorem packetLineLoadCount_covers_occurrence (graph : AIG α) (atom : α)
    (node : Fin graph.decls.size) (registered : graph.decls[node.val] = .atom atom) :
    dualRailLoadCount graph node false ≤ packetLineLoadCount graph atom := by
  have retained := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin graph.decls.size)))
    (f := fun current => if graph.decls[current.val] = .atom atom then
      dualRailLoadCount graph current false else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ node)
  simpa only [packetLineLoadCount, if_pos registered] using retained

noncomputable section

def compilePacketLineDriver (technology : AIGCellTechnology) (graph : AIG α) (atom : α) :
    LoadedConductanceCellSource where
  supply := technology.supply
  resistance := technology.resistance
  capacitance := ⟨technology.intrinsicCapacitance.value +
    (packetLineLoadCount graph atom : ℝ) * technology.pinCapacitance.value⟩
  supply_pos := technology.supply_pos
  resistance_pos := technology.resistance_pos
  capacitance_pos := add_pos_of_pos_of_nonneg technology.intrinsic_pos
    (mul_nonneg (Nat.cast_nonneg _) technology.pin_nonnegative)

theorem compilePacketLineDriver_wait (technology : AIGCellTechnology) (graph : AIG α) (atom : α) :
    (compilePacketLineDriver technology graph atom).settlingTime.value =
      1152 * technology.resistance.value * (technology.intrinsicCapacitance.value +
        (packetLineLoadCount graph atom : ℝ) * technology.pinCapacitance.value) :=
  (compilePacketLineDriver technology graph atom).settlingTime_eq

def packetLineNodeReady (technology : AIGCellTechnology) (graph : AIG α)
    (node : Fin graph.decls.size) : ℝ :=
  match graph.decls[node.val] with
  | .atom atom => (compilePacketLineDriver technology graph atom).settlingTime.value
  | _ => 0

def packetLineReadyTime (technology : AIGCellTechnology) (graph : AIG α) : SISecond :=
  ⟨(Finset.univ : Finset (Fin graph.decls.size)).sup'
    ⟨⟨0, graph.hzero⟩, Finset.mem_univ _⟩ (packetLineNodeReady technology graph)⟩

theorem packetLineDriver_wait_le_ready (technology : AIGCellTechnology) (graph : AIG α) (atom : α)
    (node : Fin graph.decls.size) (registered : graph.decls[node.val] = .atom atom) :
    (compilePacketLineDriver technology graph atom).settlingTime.value ≤
      (packetLineReadyTime technology graph).value := by
  calc
    _ = packetLineNodeReady technology graph node := by simp only [packetLineNodeReady, registered]
    _ ≤ _ := Finset.le_sup' (packetLineNodeReady technology graph) (Finset.mem_univ node)

theorem packetLineReadyTime_nonneg (technology : AIGCellTechnology) (graph : AIG α) :
    0 ≤ (packetLineReadyTime technology graph).value := by
  calc
    0 = packetLineNodeReady technology graph ⟨0, graph.hzero⟩ := by
      simp only [packetLineNodeReady, graph.hconst]
    _ ≤ _ := Finset.le_sup' (packetLineNodeReady technology graph)
      (Finset.mem_univ (⟨0, graph.hzero⟩ : Fin graph.decls.size))

theorem packetLineReadyTime_pos_of_atom (technology : AIGCellTechnology) (graph : AIG α) (atom : α)
    (node : Fin graph.decls.size) (registered : graph.decls[node.val] = .atom atom) :
    0 < (packetLineReadyTime technology graph).value :=
  (compilePacketLineDriver technology graph atom).settlingTime_pos.trans_le
    (packetLineDriver_wait_le_ready technology graph atom node registered)

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
