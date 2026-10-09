import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor.Consumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original inverse expression depends on the physical donor projector, not a chosen eigenvector. -/
def inverse (P : Matrix ι ι ℂ) (c s : ℝ) (O : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  P*O*P + ((c : ℂ)^2)⁻¹ • ((1-P)*(O-((s : ℂ)^2*(O*P).trace) • 1)*(1-P)) +
    ((c : ℂ)^2+Complex.I*c*s)⁻¹ • (P*O*(1-P)) +
    ((c : ℂ)^2-Complex.I*c*s)⁻¹ • ((1-P)*O*P)

theorem basis_inverse (t : ι) (c s : ℝ) (O : Matrix ι ι ℂ) :
    inverse (Spectrum.basisPure t) c s O = BasisInverse.inverse t c s O := by
  rw [inverse,BasisInverse.trace_basis]
  ext i j
  simp only [Spectrum.basisPure,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
    Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
    Matrix.one_apply,smul_eq_mul,BasisInverse.inverse]
  by_cases left : i=t
  · subst i
    by_cases right : j=t
    · subst j
      simp
    · simp [right,Ne.symm right,div_eq_mul_inv,mul_comm]
  · by_cases right : j=t
    · subst j
      simp [left,div_eq_mul_inv,mul_comm]
    · simp [left,right,div_eq_mul_inv,mul_comm]

theorem inverse_covariant (U : Matrix.unitaryGroup ι ℂ) (P O : Matrix ι ι ℂ) (c s : ℝ) :
    Quantum.conjugation U (inverse P c s O) =
      inverse (Quantum.conjugation U P) c s (Quantum.conjugation U O) := by
  have one : Quantum.conjugation U (1 : Matrix ι ι ℂ) = 1 := map_one (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U)
  have trace : (Quantum.conjugation U O*Quantum.conjugation U P).trace = (O*P).trace :=
    BasisInverse.conjugation_pair U O P
  have product (A B : Matrix ι ι ℂ) : Quantum.conjugation U (A*B) =
      Quantum.conjugation U A*Quantum.conjugation U B :=
    map_mul (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U) A B
  simp only [inverse,map_add,product,map_sub,map_smul,one,trace]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
