import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Source.ReceivedPairEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Producer.SourceGeneratedStrictRefill

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.HeldEnergy

open Collision Powered.Dynamics Load.Source Load.Producer Load.Producer.StrictThermal
open Load.Producer.RecoveryLedger Recovery.Producer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem interaction_charged_zero (H : SystemMatrix ι) (rho : JointMatrix ι) :
    energy (Powered.Source.interaction H) (chargedInput rho) = 0 := by
  have forward : (Powered.Source.lowering * excitedController).trace = 0 := by
    norm_num [Powered.Source.lowering, excitedController, Matrix.mul_diagonal, Matrix.trace,
      Matrix.diag, Fin.sum_univ_two, Matrix.single_apply]
  have backward : (Powered.Source.loweringᴴ * excitedController).trace = 0 := by
    norm_num [Powered.Source.lowering, excitedController, Matrix.mul_diagonal, Matrix.trace,
      Matrix.diag, Fin.sum_univ_two, Matrix.single_apply, Matrix.conjTranspose_apply]
  simp only [energy, Powered.Source.interaction, Powered.Source.transfer, chargedInput,
    Matrix.add_mul, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.trace_add, Matrix.trace_kronecker,
    forward, backward, mul_zero, add_zero, Complex.zero_re]

theorem source_initial_pc_energy_lt :
    energy Powered.Producer.poweredTotalHamiltonian (chargedInput Powered.Producer.sourceReceivedPair) < -(36 / 5 : ℝ) := by
  change energy (totalHamiltonian Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction) _ < _
  rw [totalEnergy_split_generic, systemEnergy, chargedInput_system, chargedInput_controllerEnergy 2 Powered.Producer.sourceReceivedPair
    Powered.Producer.sourceParentState.normalized]
  change energy Work.Drive.fieldBaseline Powered.Producer.sourceReceivedPair + 2 +
    energy (Powered.Source.interaction Thermal.Source.energyHamiltonian) (chargedInput _) < _
  rw [interaction_charged_zero]
  linarith [PairEnergy.source_received_pair_energy_lt]

theorem load_origin_pc_energy_lt : pcEnergy loadInitialState.joint < -(36 / 5 : ℝ) := by
  rw [loadInitialState_received]
  change energy Powered.Producer.poweredTotalHamiltonian (systemReduce (Matrix.kronecker loadParentCurrent.joint environmentState)) < _
  rw [Powered.Dynamics.systemReduce_tensor loadParentCurrent.joint environmentState, environmentState_trace, one_smul,
    loadParent_joint_from_preparation]
  have invariant := totalEnergy_conserved Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction
    Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian
    (2 * (Propagation.Producer.nativeClockStep : ℝ)) (chargedInput Powered.Producer.sourceReceivedPair)
  change energy Powered.Producer.poweredTotalHamiltonian
    (Unitary.conjStarAlgAut ℂ (Matrix PairController PairController ℂ) loadParentUnitary (chargedInput Powered.Producer.sourceReceivedPair)) = _ at invariant
  rw [invariant]
  exact source_initial_pc_energy_lt

theorem boundary_energy_abs_le_one (state : LoadState) : |boundaryEnergy state.joint| ≤ 1 :=
  (energy_abs_le_norm loadInteraction state.joint state.positive state.normalized).trans loadInteraction_norm_le_one

theorem held_pc_energy_lt : pcEnergy recoveryStateFirst.joint < -(31 / 5 : ℝ) := by
  rw [recoveryStateFirst, recoveryStep_pcEnergy, recoveryReceived_actual]
  have balance := loadStateNext_energyBalance loadInitialState
  have zero : boundaryEnergy loadInitialState.joint = 0 := by
    rw [loadInitialState_received, loadInitialJoint, loadBoundary_initial_zero]
  rw [zero] at balance
  have heat := loadFirst_strictHeat
  have boundary := (abs_le.mp (boundary_energy_abs_le_one (loadStateNext loadInitialState))).1
  linarith [load_origin_pc_energy_lt, sq_nonneg (Propagation.Producer.nativeClockStep : ℝ)]

end
end LAlanine40K2025.Thermal.Recovery.Charging.HeldEnergy
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
