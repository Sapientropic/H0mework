import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Contract

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators InnerProductSpace

abbrev Node := CPS1AtomicDynamics.Body.Node
abbrev BodyPoint := CPS1AtomicDynamics.Body.Point
variable {frame : CPS1Recycling.Frame}

def massTotal (state : CPS1ElectronicSource.State frame) : ℝ :=
  (state.geometry.nuclei.map (fun node => node.row.inertia)).sum

def centre (state : CPS1ElectronicSource.State frame) : BodyPoint :=
  (massTotal state)⁻¹ • (state.geometry.nuclei.map (fun node =>
    node.row.inertia • node.row.position)).sum

def massWeight (state : CPS1ElectronicSource.State frame) (node : Node) : ℝ :=
  node.row.inertia / massTotal state

/-- This is a restriction of the same lab occurrence; the source particle and momentum stay. -/
def relativeNode (centre : BodyPoint) (node : Node) : Node :=
  {node with row := {node.row with position := node.row.position-centre}}

def relativeGeometry (state : CPS1ElectronicSource.State frame) : Geometry frame :=
  let nodes := state.geometry.nodes.map (relativeNode (centre state))
  ⟨{state.geometry.originJoint with rows := nodes.map (fun node => (node.particle.address,node.row))},nodes⟩

def relativeState (state : CPS1ElectronicSource.State frame) : CPS1ElectronicSource.State frame :=
  ⟨relativeGeometry state,state.occupied,state.reserve⟩

def energy (state : CPS1ElectronicSource.State frame) : ℝ := (relativeState state).energy

@[simp] theorem relative_particle (centre : BodyPoint) (node : Node) :
    (relativeNode centre node).particle = node.particle := rfl
@[simp] theorem relative_inertia (centre : BodyPoint) (node : Node) :
    (relativeNode centre node).row.inertia = node.row.inertia := rfl
@[simp] theorem relative_momentum (centre : BodyPoint) (node : Node) :
    (relativeNode centre node).row.momentum = node.row.momentum := rfl
@[simp] theorem relative_position (centre : BodyPoint) (node : Node) :
    (relativeNode centre node).row.position = node.row.position-centre := rfl
@[simp] theorem relative_isNucleus (centre : BodyPoint) (node : Node) :
    isNucleus (relativeNode centre node) = isNucleus node := rfl
@[simp] theorem relative_isElectron (centre : BodyPoint) (node : Node) :
    isElectron (relativeNode centre node) = isElectron node := rfl

theorem relative_nuclei (state : CPS1ElectronicSource.State frame) :
    (relativeGeometry state).nuclei = state.geometry.nuclei.map (relativeNode (centre state)) := by
  simp only [relativeGeometry,Geometry.nuclei,List.filter_map,Function.comp_def,relative_isNucleus]

theorem shifted_electron_inertia (centre : BodyPoint) (nodes : List Node) :
    (((nodes.map (relativeNode centre)).find? isElectron).map (fun node => node.row.inertia)) =
      ((nodes.find? isElectron).map (fun node => node.row.inertia)) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      cases electron : isElectron node <;>
        simp only [List.map_cons,List.find?_cons,relative_isElectron,electron,ih,Option.map_some,
          relative_inertia]

theorem relative_electron_inertia (state : CPS1ElectronicSource.State frame) :
    (relativeGeometry state).electronInertia = state.geometry.electronInertia := by
  unfold Geometry.electronInertia relativeGeometry
  rw [shifted_electron_inertia]

theorem relative_source (state : CPS1ElectronicSource.State frame) :
    (relativeGeometry state).originJoint.originBody = state.geometry.originJoint.originBody ∧
    (relativeGeometry state).originJoint.components = state.geometry.originJoint.components ∧
    (relativeGeometry state).originJoint.nextOccurrence = state.geometry.originJoint.nextOccurrence ∧
    (relativeGeometry state).originJoint.reserve = state.geometry.originJoint.reserve := ⟨rfl,rfl,rfl,rfl⟩

theorem relative_particles (state : CPS1ElectronicSource.State frame) :
    CPS1EnzymeBath.Joint.particles frame (relativeGeometry state).originJoint =
      CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint := rfl

theorem relative_occupied (state : CPS1ElectronicSource.State frame) :
    (relativeState state).occupied = state.occupied := rfl

theorem relative_reserve (state : CPS1ElectronicSource.State frame) :
    (relativeState state).reserve = state.reserve := rfl


theorem massTotal_currentPrice (state : CPS1ElectronicSource.State frame) (reserve : ℝ) :
    massTotal (CPS1QuantumNuclear.currentPrice state reserve) = massTotal state := rfl

theorem centre_currentPrice (state : CPS1ElectronicSource.State frame) (reserve : ℝ) :
    centre (CPS1QuantumNuclear.currentPrice state reserve) = centre state := rfl

theorem energy_currentPrice (state : CPS1ElectronicSource.State frame) (reserve : ℝ) :
    energy (CPS1QuantumNuclear.currentPrice state reserve) = energy state := rfl

end
end CPS1Following
