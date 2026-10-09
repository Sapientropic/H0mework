import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.FreeFormula

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_zero_compression (P V : Matrix ι ι ℂ) (c s : ℝ)
    (sandwich : P*V*P=0) (read : (V*P).trace=0) :
    inverse P c s V = ((c : ℂ)^2)⁻¹ • V+
      (((c : ℂ)^2+Complex.I*c*s)⁻¹-((c : ℂ)^2)⁻¹) • (P*V)+
      (((c : ℂ)^2-Complex.I*c*s)⁻¹-((c : ℂ)^2)⁻¹) • (V*P) := by
  simp only [inverse,read,mul_zero,zero_smul,sub_zero,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.one_mul,Matrix.mul_one,sandwich,sub_zero,smul_sub,zero_add]
  module

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
