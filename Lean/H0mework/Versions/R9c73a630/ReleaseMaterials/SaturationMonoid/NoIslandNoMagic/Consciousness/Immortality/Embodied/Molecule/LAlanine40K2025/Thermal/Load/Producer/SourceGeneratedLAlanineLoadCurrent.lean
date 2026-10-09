import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source.SourceGeneratedThermalBoundary
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Quantum.GibbsEntropyDisposition
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Runtime.PoweredActionRuntime

/-! # Accumulated actual source action retains the full joint and the once-prepared environment -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open scoped Matrix ComplexOrder

noncomputable section

def loadParentRuntime := Powered.Runtime.poweredRuntimeAfterFirst.tick.next

def loadParentCurrent : Powered.Producer.PoweredState :=
  Powered.Runtime.poweredCurrentState loadParentRuntime.state.current

def loadInitialJoint : LoadedJoint := Matrix.kronecker loadParentCurrent.joint environmentState

theorem loadInitialJoint_positive : loadInitialJoint.PosSemidef :=
  loadParentCurrent.positive.kronecker environmentState_positive

theorem loadInitialJoint_trace : loadInitialJoint.trace = 1 := by
  unfold loadInitialJoint
  rw [Matrix.kronecker, Matrix.trace_kronecker, loadParentCurrent.normalized, environmentState_trace, mul_one]

theorem loadInitialJoint_receives_actual : loadInitialJoint = Matrix.kronecker
    (Powered.Runtime.poweredCurrentState Powered.Runtime.poweredRuntimeAfterFirst.tick.next.state.current).joint
    environmentState := rfl

structure LoadState where
  localClock : ℚ
  action : Matrix.unitaryGroup (PairController × Fin 2) ℂ

def LoadState.joint (current : LoadState) : LoadedJoint :=
  Load.Quantum.unitaryGibbsJoint loadParentCurrent.joint environmentEnergies 1 current.action

theorem LoadState.positive (current : LoadState) : current.joint.PosSemidef :=
  Load.Quantum.unitaryGibbsJoint_posSemidef _ loadParentCurrent.positive _ _ _

theorem LoadState.normalized (current : LoadState) : current.joint.trace = 1 :=
  Load.Quantum.unitaryGibbsJoint_trace _ loadParentCurrent.normalized _ _ _

def loadInitialState : LoadState := ⟨0, 1⟩

theorem loadInitialState_received : loadInitialState.joint = loadInitialJoint := by
  change Unitary.conjStarAlgAut ℂ _ 1 loadInitialJoint = loadInitialJoint
  simp

def loadStateNext (current : LoadState) : LoadState :=
  ⟨current.localClock + Propagation.Producer.nativeClockStep,
    loadUnitary (Propagation.Producer.nativeClockStep : ℝ) * current.action⟩

theorem loadStateNext_joint (current : LoadState) :
    (loadStateNext current).joint = loadAdvance (Propagation.Producer.nativeClockStep : ℝ) current.joint := by
  change Unitary.conjStarAlgAut ℂ _
    (loadUnitary (Propagation.Producer.nativeClockStep : ℝ) * current.action) loadInitialJoint =
      Unitary.conjStarAlgAut ℂ _ (loadUnitary (Propagation.Producer.nativeClockStep : ℝ))
        (Unitary.conjStarAlgAut ℂ _ current.action loadInitialJoint)
  exact Unitary.conjStarAlgAut_mul_apply _ _ _

def loadEntropyProduction (current : LoadState) : ℝ :=
  Load.Quantum.entropyProduction loadParentCurrent.joint loadParentCurrent.positive loadParentCurrent.normalized
    environmentEnergies 1 current.action

def loadMutualInformation (current : LoadState) : ℝ :=
  Load.Quantum.jointMutualInformation loadParentCurrent.joint loadParentCurrent.positive loadParentCurrent.normalized
    environmentEnergies 1 current.action

def loadGibbsExcess (current : LoadState) : ℝ :=
  Load.Quantum.environmentGibbsExcess loadParentCurrent.joint loadParentCurrent.positive loadParentCurrent.normalized
    environmentEnergies 1 current.action

theorem loadEntropy_disposition (current : LoadState) :
    loadEntropyProduction current = loadMutualInformation current + loadGibbsExcess current :=
  Load.Quantum.entropyProduction_eq_mutual_add_gibbs _ _ _ _ _ _

theorem loadEntropy_nonnegative (current : LoadState) : 0 ≤ loadEntropyProduction current :=
  Load.Quantum.entropyProduction_nonnegative _ _ _ _ _ _

theorem loadStateNext_energyBalance (current : LoadState) :
    (pcEnergy (loadStateNext current).joint - pcEnergy current.joint) +
      (environmentEnergy (loadStateNext current).joint - environmentEnergy current.joint) +
      (boundaryEnergy (loadStateNext current).joint - boundaryEnergy current.joint) = 0 := by
  rw [loadStateNext_joint]
  exact loadAdvance_energyBalance _ _

theorem loadStateNext_signedEntropy (current : LoadState) :
    loadEntropyProduction (loadStateNext current) - loadEntropyProduction current =
      (loadMutualInformation (loadStateNext current) - loadMutualInformation current) +
        (loadGibbsExcess (loadStateNext current) - loadGibbsExcess current) := by
  rw [loadEntropy_disposition, loadEntropy_disposition]
  ring

end

end LAlanine40K2025.Thermal.Load.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
