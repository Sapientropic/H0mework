import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Interaction

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Propagation.Interface Powered.Source Load.Producer.StrictThermal
open Powered.Dynamics
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def sourcePCH (H : Matrix Basis Basis ℂ) : Matrix Load.Source.PairController Load.Source.PairController ℂ :=
  totalHamiltonian (pairHamiltonian H) 2 (interaction H)

theorem pair_source_perturbation (H K : Matrix Basis Basis ℂ) :
    ‖pairHamiltonian H-pairHamiltonian K‖ ≤ 2*‖H-K‖ := by
  have delta : pairHamiltonian H-pairHamiltonian K = Matrix.kronecker (H-K) 1+Matrix.kronecker 1 (H-K) := by
    ext i j
    simp only [pairHamiltonian,Thermal.Dynamics.pairH,Thermal.Dynamics.freePairH,jointHamiltonian,
      Matrix.add_apply,Matrix.sub_apply,Matrix.kronecker,Matrix.kroneckerMap_apply]
    ring
  rw [delta]
  calc
    _ ≤ ‖Matrix.kronecker (H-K) 1‖+‖Matrix.kronecker 1 (H-K)‖ := norm_add_le _ _
    _ ≤ ‖H-K‖+‖H-K‖ := add_le_add (NonUnitalStarAlgHom.norm_apply_le tensorLeft _)
      (NonUnitalStarAlgHom.norm_apply_le tensorRight _)
    _ = _ := by ring

theorem full_PC_perturbation (H K : Matrix Basis Basis ℂ) :
    ‖sourcePCH H-sourcePCH K‖ ≤ 6*‖H-K‖ := by
  have delta : sourcePCH H-sourcePCH K =
      Matrix.kronecker (pairHamiltonian H-pairHamiltonian K) (1 : Matrix (Fin 2) (Fin 2) ℂ)+
        (interaction H-interaction K) := by
    ext i j
    simp only [sourcePCH,totalHamiltonian,bareHamiltonian,Matrix.add_apply,Matrix.sub_apply,
      Matrix.kronecker,Matrix.kroneckerMap_apply]
    ring
  rw [delta]
  have tensor : ‖Matrix.kronecker (pairHamiltonian H-pairHamiltonian K) (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      ‖pairHamiltonian H-pairHamiltonian K‖ := NonUnitalStarAlgHom.norm_apply_le tensorLeft _
  have bound := norm_add_le (Matrix.kronecker (pairHamiltonian H-pairHamiltonian K) (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (interaction H-interaction K)
  linarith [pair_source_perturbation H K,source_interaction_perturbation H K]

def transformedOriginal : Matrix Basis Basis ℂ :=
  star (actualUnitary : Matrix Basis Basis ℂ)*A*(actualUnitary : Matrix Basis Basis ℂ)

theorem actual_source_PC_error : ‖sourcePCH transformedOriginal-sourcePCH E‖ ≤ (126/10^12 : ℝ) := by
  exact (full_PC_perturbation transformedOriginal E).trans (by
    have bound := actual_source_diagonal_error
    change ‖transformedOriginal-E‖ ≤ (21/10^12 : ℝ) at bound
    linarith)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
