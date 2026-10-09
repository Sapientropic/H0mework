import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Formula

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_add (P : Matrix ι ι ℂ) (c s : ℝ) (A B : Matrix ι ι ℂ) :
    inverse P c s (A+B) = inverse P c s A+inverse P c s B := by
  simp only [inverse,Matrix.add_mul,Matrix.trace_add,mul_add,add_smul,Matrix.mul_smul,Matrix.smul_mul,
    smul_add,Matrix.mul_sub,Matrix.sub_mul,smul_sub]
  abel

theorem inverse_eigenpart (P O : Matrix ι ι ℂ) (c s : ℝ) (b : ℂ)
    (idempotent : P*P=P) (normalized : P.trace=1)
    (left : P*O=b • P) (right : O*P=b • P)
    (circle : c^2+s^2=1) (nonzero : c ≠ 0) :
    inverse P c s O = ((c : ℂ)^2)⁻¹ • (O-((s : ℂ)^2*b) • 1) := by
  have cNonzero : (c : ℂ)^2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr nonzero)
  have circleC : (c : ℂ)^2+(s : ℂ)^2=1 := by exact_mod_cast circle
  have scalar : ((c : ℂ)^2)⁻¹*((s : ℂ)^2-1) = -1 := by
    rw [show (s : ℂ)^2-1=-(c : ℂ)^2 by linear_combination circleC]
    simp [cNonzero]
  have coefficient : b - b*((c : ℂ)^2)⁻¹+b*((c : ℂ)^2)⁻¹*(s : ℂ)^2=0 := by
    linear_combination b*scalar
  have expansion : inverse P c s O =
      ((c : ℂ)^2)⁻¹ • (O-((s : ℂ)^2*b) • 1)+
        (b-b*((c : ℂ)^2)⁻¹+b*((c : ℂ)^2)⁻¹*(s : ℂ)^2) • P := by
    simp only [inverse,Matrix.mul_sub,Matrix.sub_mul,Matrix.one_mul,
      Matrix.mul_smul,Matrix.smul_mul,left,right,idempotent,smul_smul,
      smul_sub,smul_zero,sub_self,add_zero,Matrix.trace_smul,normalized,smul_eq_mul,mul_one]
    module
  rw [expansion,coefficient,zero_smul,add_zero]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
