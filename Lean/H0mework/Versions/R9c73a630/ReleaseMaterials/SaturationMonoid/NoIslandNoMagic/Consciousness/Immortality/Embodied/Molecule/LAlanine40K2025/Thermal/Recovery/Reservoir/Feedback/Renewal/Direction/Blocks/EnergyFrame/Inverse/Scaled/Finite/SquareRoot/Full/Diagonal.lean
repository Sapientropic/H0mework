import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Inputs
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.FirstSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open Propagation.Interface Load.Source Scaled.Order RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def diagonal (a : Fin 97) : Matrix (Fin 4) (Fin 4) ℚ :=
  let x := energy a.castSucc
  let u := sine^2
  !![2*x+1-u*donorEnergy,0,0,0;
     0,2*x+3-u*(donorEnergy+2),1,0;
     0,1,2*x+3-u*donorEnergy,0;
     0,0,0,2*x+5-u*(donorEnergy+2)]

theorem diagonal_source (a : Fin 97) :
    rationalCore.submatrix (diagonalPCE a.castSucc) (diagonalPCE a.castSucc)=
      (cast (diagonal a) 0).submatrix (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) := by
  rw [original_rational_diagonal_block a]
  unfold diagonalOrdinary diagonalLoaded diagonalHpc
  simp only [numericEnvironmentRead,← energy_cast,← donor_cast,← sine_cast]
  ext ⟨c,e⟩ ⟨d,f⟩
  fin_cases c <;> fin_cases e <;> fin_cases d <;> fin_cases f <;>
    norm_num [RationalMatrix.cast,diagonal,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,
      Powered.Dynamics.controllerHamiltonian,smallExchange,controllerEnvironmentExchange,Matrix.submatrix_apply,
      Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.single_apply,Fin.sum_univ_two,finProdFinEquiv,Complex.real_smul]
  all_goals ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
