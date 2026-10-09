import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Restriction

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open scoped Matrix BigOperators
noncomputable section
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ] [Fintype ν] [DecidableEq ν]

theorem polynomial_reindex (e : ν ≃ ι) (A : Matrix ι ι ℂ) (N : Nat) :
    (Phase.polynomial A N).submatrix e e=Phase.polynomial (A.submatrix e e) N := by
  let f := Matrix.reindexAlgEquiv ℂ ℂ e.symm
  change f (Phase.polynomial A N)=Phase.polynomial (f A) N
  simp only [Phase.polynomial,map_sum,map_smul,map_pow]

theorem flow_reindex (e : ν ≃ ι) (H : Matrix ι ι ℂ) (time : ℝ) :
    (Phase.flowPolynomial H time).submatrix e e=Phase.flowPolynomial (H.submatrix e e) time :=
  polynomial_reindex e _ 14

theorem original_flow_restriction {label : ι → κ} {H : Matrix ι ι ℂ}
    (kept : Preserves label H) (k : κ) (e : ν ≃ {i // label i=k}) (time : ℝ) :
    (restrict label k (Phase.flowPolynomial H time)).submatrix e e=
      Phase.flowPolynomial ((restrict label k H).submatrix e e) time := by
  rw [Phase.flowPolynomial,Contraction.restriction_polynomial
    (preserves_smul (preserves_smul kept (-Complex.I)) time),polynomial_reindex]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
