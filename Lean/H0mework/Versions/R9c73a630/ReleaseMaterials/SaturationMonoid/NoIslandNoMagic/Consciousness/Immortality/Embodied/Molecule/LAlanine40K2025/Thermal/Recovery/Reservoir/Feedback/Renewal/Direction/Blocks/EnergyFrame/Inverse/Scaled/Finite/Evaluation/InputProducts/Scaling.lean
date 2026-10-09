import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Complex

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem scaledMatrix_mul {ι : Type*} [Fintype ι] (R I A B : Matrix ι ι Int) (d e : Int) :
    scaledMatrix R I d*scaledMatrix A B e=scaledMatrix (R*A-I*B) (R*B+I*A) (d*e) := by
  unfold scaledMatrix
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,complexMatrix_mul,Int.cast_mul,mul_inv_rev]
  congr 1
  ring

theorem scaledMatrix_star {ι : Type*} (R I : Matrix ι ι Int) (d : Int) :
    star (scaledMatrix R I d)=scaledMatrix R.transpose (-I.transpose) d := by
  simp [scaledMatrix,complexMatrix_star]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
