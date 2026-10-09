import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.Substrate
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Coulomb

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ElectronicSource CPS1ReactiveField.Carried CPS1AtomicDynamics
open scoped BigOperators InnerProductSpace Matrix

-- The full original E is embedded once. The NH3 packet has its own complete
-- classical kinetic/pair field and interacts with every original nuclear and
-- occupied-electron source term; no original coefficient is dropped.
def electronExternal (state : Snapshot) (charge : ℝ) (position : Point) : ℝ :=
  (∑ electron, -(charge : ℂ) *
    (∑ spin : Bool, ∑ p, ∑ q, star (state.occupied p electron) * state.occupied q electron *
      state.nuclearIntegral p q spin position)).re

def nuclearExternal (state : Snapshot) (charge : ℝ) (position : Point) : ℝ :=
  (state.nuclei.map (fun old => Coulomb.pairEnergy charge (old.particle.charge : ℝ)
    (euclideanPoint position) old.row.position)).sum

def externalEnergy (state : Snapshot) (charge : ℝ) (position : Point) : ℝ :=
  nuclearExternal state charge position + electronExternal state charge position

def interactionEnergy (state : Snapshot) (nodes : List Body.Node) : ℝ :=
  (nodes.map (fun node => externalEnergy state (node.particle.charge : ℝ)
    (fun axis => node.row.position axis))).sum

def materialEnergy (state : Snapshot) (nodes : List Body.Node) : ℝ :=
  state.energy + Body.energy nodes + interactionEnergy state nodes

def externalForce (state : Snapshot) (node : Body.Node) : Body.Point :=
  euclideanPoint (fun axis => -(fderiv ℝ (externalEnergy state (node.particle.charge : ℝ))
    (fun coordinate => node.row.position coordinate) (Pi.single axis 1)))

def sourceForce (state : Snapshot) (nodes : List Body.Node) (node : Body.Node) : Body.Point :=
  Body.force node nodes + externalForce state node

def sourceKick (state : Snapshot) (nodes : List Body.Node) (time : ℝ) (node : Body.Node) : Body.Node :=
  {node with row :=
    {node.row with
      position := Coulomb.nextR node.row.inertia node.row.position node.row.momentum (sourceForce state nodes node) time
      momentum := Coulomb.nextP node.row.momentum (sourceForce state nodes node) time}}

def sourceNext (state : Snapshot) (nodes : List Body.Node) (time : ℝ) : List Body.Node :=
  nodes.map (sourceKick state nodes time)

theorem full_original_energy_embedded (state : Snapshot) (nodes : List Body.Node) :
    materialEnergy state nodes - Body.energy nodes - interactionEnergy state nodes = state.energy := by
  unfold materialEnergy
  ring

theorem source_work (state : Snapshot) (nodes : List Body.Node) (time : ℝ) (node : Body.Node)
    (positive : 0 < node.row.inertia) :
    Coulomb.kinetic node.row.inertia (sourceKick state nodes time node).row.momentum -
      Coulomb.kinetic node.row.inertia node.row.momentum =
    inner ℝ (sourceForce state nodes node)
      ((sourceKick state nodes time node).row.position-node.row.position) :=
  Coulomb.midpoint_work _ positive _ _ _ time

theorem source_atom_preserved (state : Snapshot) (nodes : List Body.Node) (time : ℝ) (node : Body.Node) :
    (sourceKick state nodes time node).particle = node.particle ∧
    (sourceKick state nodes time node).row.inertia = node.row.inertia := ⟨rfl,rfl⟩

-- This readout measures the actual momentum update and subtracts the packet's
-- self-interaction. It does not read a success label or a product count.
def independentImpulse (before after : Body.Node) (nodes : List Body.Node) (time : ℝ) : Body.Point :=
  after.row.momentum - before.row.momentum - time • Body.force before nodes

theorem independent_response_generated (state : Snapshot) (nodes : List Body.Node)
    (time : ℝ) (node : Body.Node) :
    independentImpulse node (sourceKick state nodes time node) nodes time =
      time • externalForce state node := by
  simp only [independentImpulse,sourceKick,Coulomb.nextP,sourceForce,smul_add]
  abel

theorem independent_response_nonzero (state : Snapshot) (nodes : List Body.Node)
    (time : ℝ) (node : Body.Node) (elapsed : time ≠ 0) (action : externalForce state node ≠ 0) :
    independentImpulse node (sourceKick state nodes time node) nodes time ≠ 0 := by
  rw [independent_response_generated]
  exact smul_ne_zero elapsed action

end
end CPS1SameEventFunction
