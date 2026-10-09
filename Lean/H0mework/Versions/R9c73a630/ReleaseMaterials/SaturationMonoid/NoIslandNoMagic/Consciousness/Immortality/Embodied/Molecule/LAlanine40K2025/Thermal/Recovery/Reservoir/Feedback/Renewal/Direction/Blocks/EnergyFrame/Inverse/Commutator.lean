import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Response

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem commutator_error (V A B : Matrix ι ι ℂ) :
    ‖(V*A-A*V)-(V*B-B*V)‖ ≤ 2*‖V‖*‖A-B‖ := by
  have split : (V*A-A*V)-(V*B-B*V)=V*(A-B)-(A-B)*V := by noncomm_ring
  rw [split]
  have left := norm_mul_le V (A-B)
  have right := norm_mul_le (A-B) V
  exact (norm_sub_le _ _).trans (by nlinarith)

def actualLoadPC : LoadedJoint := Matrix.kronecker
  (Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian) (1 : Matrix (Fin 2) (Fin 2) ℂ)
def numericLoadPC : LoadedJoint := Matrix.kronecker (sourcePCH E) (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem original_load_PC_transformed :
    Quantum.conjugation installedLoadFrame
      (Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ))=actualLoadPC := by
  exact spectator_conjugation installedPCFrame _ _

theorem original_load_commutator_norm :
    ‖loadInteraction*Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)-
      Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)*loadInteraction‖=
      ‖loadInteraction*actualLoadPC-actualLoadPC*loadInteraction‖ := by
  have fixed : Quantum.conjugation installedLoadFrame loadInteraction=loadInteraction :=
    controller_environment_invariant originalToCalculated
  have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint installedLoadFrame)
    (loadInteraction*Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)-
      Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)*loadInteraction)
  change ‖Quantum.conjugation installedLoadFrame (_-_)‖ = _ at same
  have product (A B : LoadedJoint) : Quantum.conjugation installedLoadFrame (A*B)=
      Quantum.conjugation installedLoadFrame A*Quantum.conjugation installedLoadFrame B :=
    map_mul (Unitary.conjStarAlgAut ℂ LoadedJoint installedLoadFrame) A B
  rw [map_sub,product,product,fixed,original_load_PC_transformed] at same
  exact same.symm

theorem load_PC_error : ‖actualLoadPC-numericLoadPC‖ ≤ (126/10^12 : ℝ) := by
  have delta : actualLoadPC-numericLoadPC=Matrix.kronecker
      (Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian-sourcePCH E)
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    simp only [actualLoadPC,numericLoadPC,Matrix.sub_apply,Matrix.kronecker,Matrix.kroneckerMap_apply]
    ring
  rw [delta]
  exact (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := PairController) (κ := Fin 2)) _).trans actual_powered_Hamiltonian_error

theorem original_load_commutator_error :
    ‖(loadInteraction*actualLoadPC-actualLoadPC*loadInteraction)-
      (loadInteraction*numericLoadPC-numericLoadPC*loadInteraction)‖ ≤ (252/10^12 : ℝ) := by
  apply (commutator_error _ _ _).trans
  have bound := mul_le_mul actual_load_interaction_norm load_PC_error (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

theorem original_load_response_numeric (time : ℝ) :
    ‖Quantum.conjugation (star (loadUnitary time))
      (Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ))-
      Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
    |time| * (‖loadInteraction*numericLoadPC-numericLoadPC*loadInteraction‖+(252/10^12 : ℝ)) := by
  apply (load_PC_response time).trans
  rw [original_load_commutator_norm]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg time)
  have bound := norm_sub_le_norm_sub_add_norm_sub (loadInteraction*actualLoadPC-actualLoadPC*loadInteraction)
    (loadInteraction*numericLoadPC-numericLoadPC*loadInteraction) 0
  simp only [sub_zero] at bound
  linarith [original_load_commutator_error]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
