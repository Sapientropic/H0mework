import H0mework.Computation.AIGHold.AIGHeldState
import H0mework.Physics.ConductanceCell.PacketLineDriver

/-! # Only actual registered line capacitors and node capacitors own memory coordinates -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance

variable {α : Type} [DecidableEq α] [Hashable α]

abbrev AIGInputPort (graph : AIG α) :=
  { atom : α // ∃ node : Fin graph.decls.size, graph.decls[node.val] = .atom atom }

def aigNodeHasCapacitor (graph : AIG α) (node : Fin graph.decls.size) (polarity : Bool) : Bool :=
  match graph.decls[node.val] with
  | .false => false
  | .atom _ => polarity
  | .gate _ _ => true

abbrev AIGCapacitorAddress (graph : AIG α) :=
  { address : Fin graph.decls.size × Bool // aigNodeHasCapacitor graph address.1 address.2 = true }

structure AIGCapacitorMemory (technology : AIGCellTechnology) (graph : AIG α) where
  inputVoltage : AIGInputPort graph → SIVolt
  inputRail : ∀ port, InRail (compilePacketLineDriver technology graph port.val) (inputVoltage port)
  cellVoltage : AIGCapacitorAddress graph → SIVolt
  cellRail : ∀ address,
    InRail (compileDualRailCell technology graph address.val.1 address.val.2) (cellVoltage address)

noncomputable section
namespace AIGCapacitorMemory

variable {technology : AIGCellTechnology} {graph : AIG α}

/-- One concrete boot source exists for every graph; no future gate value is preloaded. -/
def zero (technology : AIGCellTechnology) (graph : AIG α) : AIGCapacitorMemory technology graph where
  inputVoltage := fun _ => ⟨0⟩
  inputRail := fun _ => ⟨le_rfl, technology.supply_pos.le⟩
  cellVoltage := fun _ => ⟨0⟩
  cellRail := fun _ => ⟨le_rfl, technology.supply_pos.le⟩

/-- Unregistered atoms own no stored coordinates and are never read by the graph. -/
def inputInitial (memory : AIGCapacitorMemory technology graph) (atom : α) : SIVolt := by
  classical
  exact if registered : ∃ node : Fin graph.decls.size, graph.decls[node.val] = .atom atom then
    memory.inputVoltage ⟨atom, registered⟩ else ⟨0⟩

theorem inputInitial_registered (memory : AIGCapacitorMemory technology graph) (port : AIGInputPort graph) :
    memory.inputInitial port.val = memory.inputVoltage port := by
  simp only [inputInitial, dif_pos port.property]

theorem inputInitial_in_rail (memory : AIGCapacitorMemory technology graph) (atom : α)
    (node : Fin graph.decls.size) (registered : graph.decls[node.val] = .atom atom) :
    InRail (compilePacketLineDriver technology graph atom) (memory.inputInitial atom) := by
  rw [show memory.inputInitial atom = memory.inputVoltage ⟨atom, ⟨node, registered⟩⟩ from
    memory.inputInitial_registered ⟨atom, ⟨node, registered⟩⟩]
  exact memory.inputRail (⟨atom, ⟨node, registered⟩⟩ : AIGInputPort graph)

/-- Constant rails and positive atom rails are source restrictions, not extra memory cells. -/
def gateInitial (memory : AIGCapacitorMemory technology graph)
    (node : Fin graph.decls.size) (polarity : Bool) : SIVolt :=
  if capacitive : aigNodeHasCapacitor graph node polarity = true then
    memory.cellVoltage ⟨(node, polarity), capacitive⟩
  else
    match graph.decls[node.val] with
    | .atom atom => memory.inputInitial atom
    | _ => if polarity then technology.supply else ⟨0⟩

theorem gateInitial_capacitor (memory : AIGCapacitorMemory technology graph) (address : AIGCapacitorAddress graph) :
    memory.gateInitial address.val.1 address.val.2 = memory.cellVoltage address := by
  simp only [gateInitial, dif_pos address.property]

theorem gateInitial_in_rail (memory : AIGCapacitorMemory technology graph)
    (node : Fin graph.decls.size) (polarity : Bool) :
    InRail (compileDualRailCell technology graph node polarity) (memory.gateInitial node polarity) := by
  unfold gateInitial
  split
  · rename_i capacitive
    exact memory.cellRail (⟨(node, polarity), capacitive⟩ : AIGCapacitorAddress graph)
  · split
    · rename_i atom selected
      exact memory.inputInitial_in_rail atom node selected
    · split
      · exact ⟨technology.supply_pos.le, le_rfl⟩
      · exact ⟨le_rfl, technology.supply_pos.le⟩

end AIGCapacitorMemory
end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
