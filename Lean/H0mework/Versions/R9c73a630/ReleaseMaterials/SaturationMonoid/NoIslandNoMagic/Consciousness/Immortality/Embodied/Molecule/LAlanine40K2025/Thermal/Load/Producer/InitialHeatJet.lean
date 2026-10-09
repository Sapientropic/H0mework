import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.SourceGeneratedLAlanineLoadCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.EnvironmentAlgebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.FlowReadout

/-! # The first actual load flow supplies its environmental heat jet -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

open StrictThermal

private def loadInitialTangent : LoadedJoint :=
  -Complex.I • (loadTotalHamiltonian * loadInitialJoint - loadInitialJoint * loadTotalHamiltonian)

/-- This continuous readout is the actual source flow whose native-q value is the first load next. -/
def loadFirstEnvironmentHeat (elapsed : ℝ) : ℝ :=
  environmentEnergy (loadAdvance elapsed loadInitialJoint)

private def loadFirstEnvironmentHeatSlope (elapsed : ℝ) : ℝ :=
  environmentEnergy (loadAdvance elapsed loadInitialTangent)

theorem loadFirstEnvironmentHeat_actual :
    loadFirstEnvironmentHeat (Propagation.Producer.nativeClockStep : ℝ) =
      environmentEnergy (loadStateNext loadInitialState).joint := by
  rw [loadStateNext_joint, loadInitialState_received]
  rfl

private theorem loadFirstEnvironmentHeat_hasDerivAt (elapsed : ℝ) :
    HasDerivAt loadFirstEnvironmentHeat (loadFirstEnvironmentHeatSlope elapsed) elapsed := by
  have derivative := coupledEnergy_hasDerivAt Powered.Producer.poweredTotalHamiltonian 2
    loadInteraction Powered.Producer.poweredTotalHamiltonian_hermitian loadInteraction_hermitian
    elapsed loadInitialJoint (environmentObservable (P := Pair))
  simp only [environmentObservable, environmentObservable_energy] at derivative
  exact derivative

/-- A once-prepared diagonal environment has zero initial energy velocity even with PC coherence. -/
theorem loadFirstEnvironmentHeat_deriv_zero : deriv loadFirstEnvironmentHeat 0 = 0 := by
  rw [(loadFirstEnvironmentHeat_hasDerivAt 0).deriv]
  change environmentEnergy (coupledNext _ _ _ _ _ 0 loadInitialTangent) = 0
  rw [coupledNext_zero]
  change controllerEnergy 2 loadInitialTangent = 0
  rw [← environmentObservable_energy]
  exact initial_heat_tangent_zero Powered.Producer.poweredTotalHamiltonian loadParentCurrent.joint _

/-- Actual PC coherence is retained; the CE curvature reads its existing C/E energy imbalance. -/
theorem loadFirstEnvironmentHeat_secondDeriv :
    deriv (deriv loadFirstEnvironmentHeat) 0 =
      2 * (Powered.Producer.poweredControllerEnergy loadParentCurrent -
        environmentEnergy loadInitialState.joint) := by
  have slope : deriv loadFirstEnvironmentHeat = loadFirstEnvironmentHeatSlope :=
    funext fun t => (loadFirstEnvironmentHeat_hasDerivAt t).deriv
  rw [slope]
  have derivative := coupledEnergy_hasDerivAt Powered.Producer.poweredTotalHamiltonian 2
    loadInteraction Powered.Producer.poweredTotalHamiltonian_hermitian loadInteraction_hermitian
    0 loadInitialTangent (environmentObservable (P := Pair))
  simp only [coupledNext_zero, environmentObservable, environmentObservable_energy] at derivative
  change HasDerivAt loadFirstEnvironmentHeatSlope _ 0 at derivative
  rw [derivative.deriv, loadInitialState_received]
  change controllerEnergy 2 _ = _
  rw [← environmentObservable_energy]
  exact initial_heat_curvature_read Powered.Producer.poweredTotalHamiltonian loadParentCurrent.joint
    _ environmentState_trace

end

end LAlanine40K2025.Thermal.Load.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
