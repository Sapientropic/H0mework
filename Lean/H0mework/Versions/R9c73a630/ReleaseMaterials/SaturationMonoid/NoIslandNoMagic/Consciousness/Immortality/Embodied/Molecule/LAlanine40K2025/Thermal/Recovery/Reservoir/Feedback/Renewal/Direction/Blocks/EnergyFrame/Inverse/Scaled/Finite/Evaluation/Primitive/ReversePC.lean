import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.PCSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Propagation.Interface Load.Source
open scoped Matrix
noncomputable section

def controllerSign : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1,-1]

def pcControllerSign : Matrix PairController PairController ℂ :=
  Matrix.kronecker (1 : Matrix Pair Pair ℂ) controllerSign

def smallControllerSign : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) controllerSign

theorem controller_lowering_sign : controllerSign*Powered.Source.lowering*controllerSign= -Powered.Source.lowering := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [controllerSign,Powered.Source.lowering,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.single_apply]

theorem controller_sign_square : controllerSign*controllerSign=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [controllerSign,Matrix.diagonal_mul,Matrix.diagonal_apply,Matrix.one_apply]

theorem controller_sign_self : star controllerSign=controllerSign := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [controllerSign,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,Matrix.diagonal_apply]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
