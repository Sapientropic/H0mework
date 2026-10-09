import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.SourceGeneratedLAlanineLoadCurrent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalLoad.HamiltonianBound
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.ControllerVacancy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.FlowReadout

/-! # The actual twice-used controller pays the initial thermal gap -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace StrictThermal

theorem nativeClock_small :
    0 < (Propagation.Producer.nativeClockStep : ℝ) ∧
      (Propagation.Producer.nativeClockStep : ℝ) < 1 / 2000 := by
  rw [Propagation.Producer.nativeClockStep_exact]
  norm_num

end StrictThermal

open StrictThermal

def loadParentUnitary : Matrix.unitaryGroup PairController ℂ :=
  flowUnitary Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction
    Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian
    (2 * (Propagation.Producer.nativeClockStep : ℝ))

theorem loadParent_joint_from_preparation :
    loadParentCurrent.joint = Unitary.conjStarAlgAut ℂ _ loadParentUnitary
      (chargedInput Powered.Producer.sourceReceivedPair) := by
  change Powered.Producer.sourceAdvance (Propagation.Producer.nativeClockStep : ℝ)
    (Powered.Producer.sourceAdvance (Propagation.Producer.nativeClockStep : ℝ)
      (chargedInput Powered.Producer.sourceReceivedPair)) =
    Powered.Producer.sourceAdvance (2 * (Propagation.Producer.nativeClockStep : ℝ))
      (chargedInput Powered.Producer.sourceReceivedPair)
  rw [← Powered.Producer.sourceAdvance_add]
  congr 1
  ring

theorem loadParentUnitary_small : ‖(loadParentUnitary : Matrix PairController PairController ℂ) - 1‖ < 1 / 4 := by
  have timeNonnegative : 0 ≤ 2 * (Propagation.Producer.nativeClockStep : ℝ) :=
    mul_nonneg (by norm_num) nativeClock_small.1.le
  have bound := flowUnitary_sub_one_norm_le Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction
    Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian
    (2 * (Propagation.Producer.nativeClockStep : ℝ)) timeNonnegative
  calc
    _ ≤ ‖Powered.Producer.poweredTotalHamiltonian‖ *
        (2 * (Propagation.Producer.nativeClockStep : ℝ)) := bound
    _ ≤ 243 * (2 * (Propagation.Producer.nativeClockStep : ℝ)) :=
      mul_le_mul_of_nonneg_right poweredTotalHamiltonian_norm_le timeNonnegative
    _ < 1 / 4 := by nlinarith [nativeClock_small.2]

/-- The actual twice-evolved controller retains more than 15/8 Hartree of its one preparation. -/
theorem loadParent_controller_energy_lower :
    15 / 8 < Powered.Producer.poweredControllerEnergy loadParentCurrent := by
  change 15 / 8 < controllerEnergy 2 loadParentCurrent.joint
  rw [loadParent_joint_from_preparation]
  have bound := chargedInput_controller_lower_bound Powered.Producer.sourceReceivedPair
    Powered.Producer.sourceParentState.positive Powered.Producer.sourceParentState.normalized
    loadParentUnitary
  nlinarith [loadParentUnitary_small,
    norm_nonneg ((loadParentUnitary : Matrix PairController PairController ℂ) - 1)]

/-- The source-fixed two-level β=1 Gibbs environment starts below half a Hartree. -/
theorem loadInitial_environment_energy_upper : environmentEnergy loadInitialState.joint < 1 / 2 := by
  have read : environmentEnergy loadInitialState.joint =
      2 * (Real.exp (-2) / (1 + Real.exp (-2))) := by
    change Collision.energy (controllerHamiltonian 2) (controllerReduce loadInitialState.joint) = _
    rw [loadInitialState_received, loadInitialJoint, controllerReduce_tensor,
      loadParentCurrent.normalized, one_smul]
    norm_num [Collision.energy, controllerHamiltonian, environmentState, environmentPMF,
      Population.gibbsPMF_toReal, Population.gibbsProbability, Population.partitionFunction,
      environmentEnergies, Fin.sum_univ_two, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    positivity
  have expLower : 3 < Real.exp (2 : ℝ) := by
    have lower := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
    norm_num at lower
    exact lower
  have expSmall : Real.exp (-2) < 1 / 3 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 3) expLower
  rw [read, ← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 1 + Real.exp (-2))]
  linarith

/-- The strict imbalance is generated by the actual twice-used controller and the one Gibbs input. -/
theorem loadInitial_energyImbalance_lower :
    11 / 8 < Powered.Producer.poweredControllerEnergy loadParentCurrent -
      environmentEnergy loadInitialState.joint := by
  linarith [loadParent_controller_energy_lower, loadInitial_environment_energy_upper]

end

end LAlanine40K2025.Thermal.Load.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
