import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Scaling

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem scaled_product_form {ι : Type*} [Fintype ι] (R I A B : Matrix ι ι Int) (d e : Int) :
    scaledMatrix R I d*scaledMatrix A B e=((d*e : Int) : ℂ)⁻¹ • (complexMatrix R I*complexMatrix A B) := by
  unfold scaledMatrix
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Int.cast_mul,mul_inv_rev]
  congr 1
  ring

theorem raw_right_star {ι : Type*} (R I : Matrix ι ι Int) :
    complexMatrix R.transpose (-I.transpose)=star (complexMatrix R I) := (complexMatrix_star R I).symm

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
