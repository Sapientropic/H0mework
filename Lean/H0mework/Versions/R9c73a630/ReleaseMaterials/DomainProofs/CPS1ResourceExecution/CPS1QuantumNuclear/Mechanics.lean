import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Closure

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear
noncomputable section
open CPS1ElectronicSource
open scoped InnerProductSpace

/-- Subordinate finite midpoint algebra. The live pulse supplies its field from
its same-current electron and nuclear energy; this helper selects no field. -/
def kickWith (node : CPS1AtomicDynamics.Body.Node)
    (field : CPS1AtomicDynamics.Body.Point) (time : ℝ) : CPS1AtomicDynamics.Body.Node :=
  {node with row := {node.row with
    position := node.row.position + (time/node.row.inertia) • node.row.momentum +
      (time^2/(2*node.row.inertia)) • field
    momentum := node.row.momentum+time • field}}

def moveNucleus (node : CPS1AtomicDynamics.Body.Node)
    (field : CPS1AtomicDynamics.Body.Point) (time : ℝ) : CPS1AtomicDynamics.Body.Node :=
  if isNucleus node then kickWith node field time else node

theorem kick_whole (node : CPS1AtomicDynamics.Body.Node)
    (field : CPS1AtomicDynamics.Body.Point) (time : ℝ) :
    (kickWith node field time).particle = node.particle ∧
      (kickWith node field time).row.inertia = node.row.inertia := ⟨rfl,rfl⟩

theorem nuclear_whole (node : CPS1AtomicDynamics.Body.Node)
    (field : CPS1AtomicDynamics.Body.Point) (time : ℝ) :
    (moveNucleus node field time).particle = node.particle ∧
      (moveNucleus node field time).row.inertia = node.row.inertia := by
  unfold moveNucleus
  split
  · exact kick_whole node field time
  · exact ⟨rfl,rfl⟩

theorem electron_row_retained (node : CPS1AtomicDynamics.Body.Node)
    (field : CPS1AtomicDynamics.Body.Point) (time : ℝ) (electron : isElectron node = true) :
    moveNucleus node field time = node := by
  have absent : isNucleus node = false := by
    cases flag : isNucleus node <;> simp [isElectron,flag] at electron ⊢
  simp only [moveNucleus,absent,Bool.false_eq_true,if_false]

theorem nuclear_work (node : CPS1AtomicDynamics.Body.Node)
    (field : CPS1AtomicDynamics.Body.Point) (time : ℝ) (mass : 0 < node.row.inertia)
    (nucleus : isNucleus node = true) :
    CPS1AtomicDynamics.Coulomb.kinetic node.row.inertia (moveNucleus node field time).row.momentum-
      CPS1AtomicDynamics.Coulomb.kinetic node.row.inertia node.row.momentum =
      inner ℝ field ((moveNucleus node field time).row.position-node.row.position) := by
  simp only [moveNucleus,nucleus,if_true,kickWith]
  exact CPS1AtomicDynamics.Coulomb.midpoint_work _ mass _ _ _ time

variable {frame : CPS1Recycling.Frame}

def nextNodes (state : CPS1ElectronicSource.State frame)
    (field : CPS1AtomicDynamics.Body.Node → CPS1AtomicDynamics.Body.Point) (time : ℝ) :=
  state.geometry.nodes.map (fun node => moveNucleus node (field node) time)

def movedJoint (state : CPS1ElectronicSource.State frame)
    (nodes : List CPS1AtomicDynamics.Body.Node) : CPS1EnzymeBath.Joint.State frame :=
  {state.geometry.originJoint with
    rows := nodes.map (fun node => (node.particle.address,node.row))
    reserve := state.reserve}

def movedGeometry (state : CPS1ElectronicSource.State frame)
    (nodes : List CPS1AtomicDynamics.Body.Node) : Geometry frame :=
  ⟨movedJoint state nodes,nodes⟩

def movedState (state : CPS1ElectronicSource.State frame)
    (nodes : List CPS1AtomicDynamics.Body.Node) : CPS1ElectronicSource.State frame :=
  ⟨movedGeometry state nodes,state.occupied,state.reserve⟩

theorem moved_source (state : CPS1ElectronicSource.State frame) (nodes : List CPS1AtomicDynamics.Body.Node) :
    (movedJoint state nodes).originBody = state.geometry.originJoint.originBody ∧
      (movedJoint state nodes).components = state.geometry.originJoint.components ∧
      (movedJoint state nodes).nextOccurrence = state.geometry.originJoint.nextOccurrence ∧
      (movedJoint state nodes).reserve = state.reserve := ⟨rfl,rfl,rfl,rfl⟩

theorem moved_particles (state : CPS1ElectronicSource.State frame) (nodes : List CPS1AtomicDynamics.Body.Node) :
    CPS1EnzymeBath.Joint.particles frame (movedJoint state nodes) =
      CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint := rfl

theorem moved_charge (state : CPS1ElectronicSource.State frame) (nodes : List CPS1AtomicDynamics.Body.Node) :
    CPS1EnzymeBath.Joint.charge frame (movedJoint state nodes) =
      CPS1EnzymeBath.Joint.charge frame state.geometry.originJoint := rfl

theorem moved_occupation (state : CPS1ElectronicSource.State frame) (nodes : List CPS1AtomicDynamics.Body.Node)
    (good : CPS1ElectronicEvolution.Consumer.Good state) :
    CPS1ElectronicEvolution.Consumer.Good (movedState state nodes) := good

theorem moved_particle_rows (state : CPS1ElectronicSource.State frame)
    (field : CPS1AtomicDynamics.Body.Node → CPS1AtomicDynamics.Body.Point) (time : ℝ) :
    (nextNodes state field time).map CPS1AtomicDynamics.Body.Node.particle =
      state.geometry.nodes.map CPS1AtomicDynamics.Body.Node.particle := by
  simp only [nextNodes,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro node _
  exact (nuclear_whole node (field node) time).1

end
end CPS1QuantumNuclear
