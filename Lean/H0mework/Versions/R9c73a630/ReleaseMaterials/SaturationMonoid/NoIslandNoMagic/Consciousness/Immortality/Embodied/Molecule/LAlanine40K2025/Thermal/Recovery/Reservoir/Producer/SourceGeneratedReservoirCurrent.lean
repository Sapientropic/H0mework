import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.RetainedBodyLift

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Current

open Load.Source Load.Producer Powered.Dynamics Propagation.Producer
open scoped Matrix ComplexOrder
noncomputable section

abbrev FullIndex := (PairController × PairController) × Fin 2
abbrev FullJoint := Matrix FullIndex FullIndex ℂ

def referencePair : Collision.JointMatrix PairController := Matrix.kronecker loadParentCurrent.joint Source.donor

theorem referencePair_positive : referencePair.PosSemidef := loadParentCurrent.positive.kronecker Source.donor_positive

theorem referencePair_trace : referencePair.trace = 1 := by
  rw [referencePair, Matrix.kronecker, Matrix.trace_kronecker, loadParentCurrent.normalized, Source.donor_trace, one_mul]

structure State where
  localClock : ℚ
  action : Matrix.unitaryGroup FullIndex ℂ

def State.joint (current : State) : FullJoint :=
  Load.Quantum.unitaryGibbsJoint referencePair environmentEnergies 1 current.action

theorem State.positive (current : State) : current.joint.PosSemidef :=
  Load.Quantum.unitaryGibbsJoint_posSemidef _ referencePair_positive _ _ _

theorem State.normalized (current : State) : current.joint.trace = 1 :=
  Load.Quantum.unitaryGibbsJoint_trace _ referencePair_trace _ _ _

def initial : State :=
  ⟨Source.received.localClock, Incidence.bodyLift Source.received.action⟩

theorem referencePair_environment :
    Matrix.kronecker referencePair environmentState =
      Incidence.receivedJoint loadInitialJoint Source.donor := by
  ext i j
  simp only [referencePair, loadInitialJoint, Incidence.receivedJoint, Incidence.bodyReservoir,
    Matrix.submatrix_apply, Equiv.coe_fn_mk, Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

theorem initial_receives_actual :
    initial.joint = Incidence.receivedJoint Source.received.joint Source.donor := by
  change Quantum.conjugation (Incidence.bodyLift Source.received.action)
    (Matrix.kronecker referencePair environmentState) = _
  rw [referencePair_environment, Incidence.bodyLift_received]
  rfl

theorem initial_body : Incidence.bodyRead initial.joint = Source.received.joint := by
  rw [initial_receives_actual, Incidence.receivedJoint_body _ _ Source.donor_trace]

theorem initial_pair : systemReduce initial.joint = Source.pairOrigin := by
  rw [initial_receives_actual, Incidence.receivedJoint_pair]
  rfl

def pulse (elapsed : ℝ) : Matrix.unitaryGroup FullIndex ℂ :=
  Load.Quantum.localUnitary (Native.pairFlow elapsed) (Load.Recovery.Control.environmentUnitary elapsed)

def supplyNext (current : State) : State :=
  ⟨current.localClock + nativeClockStep, pulse (nativeClockStep : ℝ) * current.action⟩

def loadPulse (elapsed : ℝ) : Matrix.unitaryGroup FullIndex ℂ :=
  Incidence.localLift (loadUnitary elapsed) (Native.freePCUnitary elapsed)

def loadNext (current : State) : State :=
  ⟨current.localClock + nativeClockStep, loadPulse (nativeClockStep : ℝ) * current.action⟩

theorem supplyNext_joint (current : State) :
    (supplyNext current).joint = Quantum.conjugation (pulse (nativeClockStep : ℝ)) current.joint := by
  change Unitary.conjStarAlgAut ℂ FullJoint (pulse (nativeClockStep : ℝ) * current.action)
    (Matrix.kronecker referencePair environmentState) =
    Unitary.conjStarAlgAut ℂ FullJoint (pulse (nativeClockStep : ℝ))
      (Unitary.conjStarAlgAut ℂ FullJoint current.action (Matrix.kronecker referencePair environmentState))
  exact Unitary.conjStarAlgAut_mul_apply _ _ _

theorem loadNext_joint (current : State) :
    (loadNext current).joint = Quantum.conjugation
      (Incidence.localLift (loadUnitary (nativeClockStep : ℝ)) (Native.freePCUnitary (nativeClockStep : ℝ))) current.joint := by
  change Unitary.conjStarAlgAut ℂ FullJoint
    (Incidence.localLift (loadUnitary (nativeClockStep : ℝ)) (Native.freePCUnitary (nativeClockStep : ℝ)) * current.action)
    (Matrix.kronecker referencePair environmentState) =
    Unitary.conjStarAlgAut ℂ FullJoint
      (Incidence.localLift (loadUnitary (nativeClockStep : ℝ)) (Native.freePCUnitary (nativeClockStep : ℝ)))
      (Unitary.conjStarAlgAut ℂ FullJoint current.action (Matrix.kronecker referencePair environmentState))
  exact Unitary.conjStarAlgAut_mul_apply _ _ _

theorem supplyNext_pair (current : State) :
    systemReduce (supplyNext current).joint =
      Quantum.conjugation (Native.pairFlow (nativeClockStep : ℝ)) (systemReduce current.joint) := by
  rw [supplyNext_joint]
  exact Load.Quantum.systemReduce_local_conjugation _ _ _

theorem supplyNext_environment (current : State) :
    controllerReduce (supplyNext current).joint = Quantum.conjugation (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ))
      (controllerReduce current.joint) := by
  rw [supplyNext_joint]
  exact Load.Quantum.controllerReduce_local_conjugation _ _ _

theorem first_pair_actual : systemReduce (supplyNext initial).joint = Native.pairTarget := by
  rw [supplyNext_pair, initial_pair]
  rfl

theorem loadNext_body (current : State) :
    Incidence.bodyRead (loadNext current).joint = loadAdvance (nativeClockStep : ℝ) (Incidence.bodyRead current.joint) := by
  rw [loadNext_joint, Incidence.localLift_read]
  rfl

theorem supplyNext_reflects_joint (left right : State)
    (same : (supplyNext left).joint = (supplyNext right).joint) : left.joint = right.joint := by
  rw [supplyNext_joint, supplyNext_joint] at same
  exact (Unitary.conjStarAlgAut ℂ (FullJoint) (pulse (nativeClockStep : ℝ))).injective same

def entropyProduction (current : State) : ℝ :=
  Load.Quantum.entropyProduction referencePair referencePair_positive referencePair_trace environmentEnergies 1 current.action

theorem entropyProduction_nonnegative (current : State) : 0 ≤ entropyProduction current :=
  Load.Quantum.entropyProduction_nonnegative _ _ _ _ _ _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Current
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
