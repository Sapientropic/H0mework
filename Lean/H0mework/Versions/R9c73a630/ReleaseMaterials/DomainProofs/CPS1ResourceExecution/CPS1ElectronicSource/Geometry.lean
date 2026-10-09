import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Gaussian
import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Kernel

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section

inductive Failure
  | body (failure : CPS1AtomicDynamics.Body.Failure)
  | missingJoint
  | unequalElectronInertia
  | negativeTime
  | negativeReserve
  | energyShortage
  deriving DecidableEq

structure Geometry (frame : CPS1Recycling.Frame) where
  originJoint : CPS1EnzymeBath.Joint.State frame
  nodes : List CPS1AtomicDynamics.Body.Node

variable {frame : CPS1Recycling.Frame}

def isNucleus (node : CPS1AtomicDynamics.Body.Node) : Bool :=
  match node.particle.address with | .nucleus _ => true | .electron _ _ => false

def isElectron (node : CPS1AtomicDynamics.Body.Node) : Bool := !isNucleus node

def Geometry.nuclei (geometry : Geometry frame) : List CPS1AtomicDynamics.Body.Node :=
  geometry.nodes.filter isNucleus

def Geometry.electronInertia (geometry : Geometry frame) : ℝ :=
  ((geometry.nodes.find? isElectron).map (fun node => node.row.inertia)).getD 1

def Geometry.fromJoint? (frame : CPS1Recycling.Frame) (joint : CPS1EnzymeBath.Joint.State frame) :
    Except Failure (Geometry frame) := by
  classical
  exact
    match CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame joint) joint.rows with
    | .error failure => .error (.body failure)
    | .ok nodes =>
      let geometry : Geometry frame := ⟨joint,nodes⟩
      if ¬ CPS1AtomicDynamics.Body.ready nodes then .error (.body .collision)
      else if nodes.all (fun node => !isElectron node || node.row.inertia = geometry.electronInertia)
        then .ok geometry else .error .unequalElectronInertia

def Geometry.fromActual? (frame : CPS1Recycling.Frame) (previous : CPS1EnzymeBath.Source.Occurrence frame) :
    Except Failure (Geometry frame) :=
  match CPS1EnzymeBath.Source.heldJoint frame previous.current.stock with
  | none => .error .missingJoint
  | some joint => fromJoint? frame joint

def Geometry.classicalEnergy (geometry : Geometry frame) : ℝ :=
  CPS1AtomicDynamics.Body.energy geometry.nodes

def Geometry.nuclearEnergy (geometry : Geometry frame) : ℝ :=
  CPS1AtomicDynamics.Body.energy geometry.nuclei

def Geometry.classicalElectronicEnergy (geometry : Geometry frame) : ℝ :=
  geometry.classicalEnergy-geometry.nuclearEnergy

theorem source_classical_split (frame : CPS1Recycling.Frame) (geometry : Geometry frame) :
    geometry.classicalEnergy = geometry.nuclearEnergy+geometry.classicalElectronicEnergy := by
  unfold Geometry.classicalElectronicEnergy
  ring

def Geometry.nucleusPosition (node : CPS1AtomicDynamics.Body.Node) : Point := fun axis => node.row.position axis

theorem source_joint_identity (frame : CPS1Recycling.Frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (geometry : Geometry frame) (actual : Geometry.fromJoint? frame joint = .ok geometry) :
    geometry.originJoint = joint := by
  unfold Geometry.fromJoint? at actual
  cases gathered : CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame joint) joint.rows with
  | error failure => simp [gathered] at actual
  | ok nodes =>
    simp only [gathered] at actual
    split at actual
    · cases actual
    · split at actual
      · cases Except.ok.inj actual
        rfl
      · cases actual

def euclideanPoint (point : Point) : CPS1AtomicDynamics.Coulomb.Point := WithLp.toLp 2 point

theorem same_source_kernel (point : Point) :
    SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceCoulomb.kernel point =
      ‖euclideanPoint point‖⁻¹ := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs,sq_abs]
  rfl

end
end CPS1ElectronicSource
