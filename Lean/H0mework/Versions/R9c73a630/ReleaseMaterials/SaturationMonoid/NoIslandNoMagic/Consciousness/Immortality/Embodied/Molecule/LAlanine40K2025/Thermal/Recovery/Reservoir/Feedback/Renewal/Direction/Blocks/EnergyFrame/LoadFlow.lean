import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Load

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Propagation.Interface Powered.Source Powered.Dynamics Load.Source Load.Producer.StrictThermal
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def installedLoadFrame : Matrix.unitaryGroup (PairController × Fin 2) ℂ := spectatorFrame installedPCFrame

def numericLoadHamiltonian : LoadedJoint := totalHamiltonian (sourcePCH E) 2 loadInteraction

theorem original_load_transformed : Quantum.conjugation installedLoadFrame loadTotalHamiltonian =
    totalHamiltonian (Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian) 2 loadInteraction := by
  have one : Quantum.conjugation installedPCFrame (1 : Matrix PairController PairController ℂ) = 1 :=
    map_one (Unitary.conjStarAlgAut ℂ (Matrix PairController PairController ℂ) installedPCFrame)
  simp only [loadTotalHamiltonian,totalHamiltonian,bareHamiltonian,map_add,installedLoadFrame,
    spectator_conjugation,one]
  have fixed : Quantum.conjugation (spectatorFrame (κ := Fin 2) installedPCFrame) loadInteraction = loadInteraction := by
    unfold installedPCFrame
    exact controller_environment_invariant originalToCalculated
  rw [fixed]

theorem original_load_Hamiltonian_error :
    ‖Quantum.conjugation installedLoadFrame loadTotalHamiltonian-numericLoadHamiltonian‖ ≤ (126/10^12 : ℝ) := by
  rw [original_load_transformed]
  have delta : totalHamiltonian (Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian) 2 loadInteraction-
      numericLoadHamiltonian = Matrix.kronecker
        (Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian-sourcePCH E) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    simp only [numericLoadHamiltonian,totalHamiltonian,bareHamiltonian,Matrix.add_apply,Matrix.sub_apply,
      Matrix.kronecker,Matrix.kroneckerMap_apply]
    ring
  rw [delta]
  apply (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := PairController) (κ := Fin 2)) _).trans
  unfold installedPCFrame
  exact actual_powered_Hamiltonian_error

theorem actual_numeric_load_hermitian : numericLoadHamiltonian.IsHermitian :=
  totalHamiltonian_hermitian _ _ _ numeric_PC_hermitian loadInteraction_hermitian

theorem original_load_matrix (time : ℝ) : (loadUnitary time : LoadedJoint) = hamiltonianFlow loadTotalHamiltonian time :=
  original_controller_flow _ _ _ _ _ _

theorem actual_load_action_error (time : ℝ) :
    ‖Quantum.conjugation installedLoadFrame (loadUnitary time : LoadedJoint)-
      hamiltonianFlow numericLoadHamiltonian time‖ ≤ |time| * (126/10^12 : ℝ) := by
  rw [original_load_matrix,flow_conjugation]
  have original : (Quantum.conjugation installedLoadFrame loadTotalHamiltonian).IsHermitian := by
    rw [Quantum.conjugation_apply]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ loadTotalHamiltonian_hermitian
  exact (hamiltonian_flow_error _ _ original actual_numeric_load_hermitian time).trans
    (mul_le_mul_of_nonneg_left original_load_Hamiltonian_error (abs_nonneg time))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
