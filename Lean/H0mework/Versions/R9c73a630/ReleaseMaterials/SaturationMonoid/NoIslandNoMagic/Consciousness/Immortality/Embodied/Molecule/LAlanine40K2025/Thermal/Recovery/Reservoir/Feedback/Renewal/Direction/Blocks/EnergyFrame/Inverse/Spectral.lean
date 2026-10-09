import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.NumericCompression

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem spectral_pure_eigen (H : Matrix ι ι ℂ) (hermitian : H.IsHermitian) (i : ι) :
    H*Spectrum.spectralPure H hermitian i = (hermitian.eigenvalues i : ℂ) • Spectrum.spectralPure H hermitian i := by
  let U := hermitian.eigenvectorUnitary
  have columns : H*(U : Matrix ι ι ℂ) = (U : Matrix ι ι ℂ)*Matrix.diagonal (fun j => (hermitian.eigenvalues j : ℂ)) := by
    ext a b
    rw [Matrix.mul_diagonal]
    have h := congrFun (hermitian.mulVec_eigenvectorBasis b) a
    simpa only [Matrix.mul_apply,Matrix.IsHermitian.eigenvectorUnitary_apply,Matrix.mulVec,
      dotProduct,Pi.smul_apply,Complex.real_smul,mul_comm,U] using h
  have diagonal : Matrix.diagonal (fun j => (hermitian.eigenvalues j : ℂ))*Spectrum.basisPure i =
      (hermitian.eigenvalues i : ℂ) • Spectrum.basisPure i := by
    ext a b
    simp only [Spectrum.basisPure,Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul]
    split_ifs <;> subst_vars <;> simp_all
  change H*((U : Matrix ι ι ℂ)*Spectrum.basisPure i*star (U : Matrix ι ι ℂ)) =
    (hermitian.eigenvalues i : ℂ) • ((U : Matrix ι ι ℂ)*Spectrum.basisPure i*star (U : Matrix ι ι ℂ))
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,columns,Matrix.mul_assoc (U : Matrix ι ι ℂ),diagonal]
  simp only [Matrix.mul_smul,Matrix.smul_mul]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
