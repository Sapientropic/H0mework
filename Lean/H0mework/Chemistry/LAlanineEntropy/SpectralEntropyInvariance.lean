import H0mework.Chemistry.LAlanineEntropy.SpectralEntropy

/-! # Spectral entropy follows the source characteristic polynomial -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Quantum

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open scoped ComplexOrder ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

theorem spectralEntropy_eq_of_charpoly (rho sigma : Matrix ι ι ℂ)
    (rhoPositive : rho.PosSemidef) (sigmaPositive : sigma.PosSemidef)
    (rhoTrace : rho.trace = 1) (sigmaTrace : sigma.trace = 1)
    (same : rho.charpoly = sigma.charpoly) :
    spectralEntropy rho rhoPositive rhoTrace = spectralEntropy sigma sigmaPositive sigmaTrace := by
  have eigenvalues :=
    (rhoPositive.isHermitian.eigenvalues_eq_eigenvalues_iff sigmaPositive.isHermitian).mpr same
  have probabilities : spectralPMF rho rhoPositive rhoTrace =
      spectralPMF sigma sigmaPositive sigmaTrace := by
    ext i
    change ENNReal.ofReal (rhoPositive.isHermitian.eigenvalues i) =
      ENNReal.ofReal (sigmaPositive.isHermitian.eigenvalues i)
    rw [eigenvalues]
  exact congrArg entropy probabilities

theorem unitary_conjugate_trace (rho : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    ((U : Matrix ι ι ℂ) * rho * star (U : Matrix ι ι ℂ)).trace = rho.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

theorem spectralEntropy_unitary_conjugation (rho : Matrix ι ι ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) (U : Matrix.unitaryGroup ι ℂ) :
    spectralEntropy ((U : Matrix ι ι ℂ) * rho * star (U : Matrix ι ι ℂ))
      (positive.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ))
      ((unitary_conjugate_trace rho U).trans normalized) =
        spectralEntropy rho positive normalized := by
  apply spectralEntropy_eq_of_charpoly
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]

omit [Fintype ι] in
theorem diagonal_pmf_positive (p : PMF ι) :
    (Matrix.diagonal (fun i => ((p i).toReal : ℂ))).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.nonneg_iff.mpr ⟨ENNReal.toReal_nonneg, rfl⟩

theorem diagonal_pmf_trace (p : PMF ι) :
    (Matrix.diagonal (fun i => ((p i).toReal : ℂ))).trace = 1 := by
  rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, pmf_sum_toReal, Complex.ofReal_one]

private theorem diagonal_eigenvalue_sum (values : ι → ℝ)
    (hermitian : (Matrix.diagonal (fun i => (values i : ℂ))).IsHermitian) (read : ℝ → ℝ) :
    ∑ i, read (hermitian.eigenvalues i) = ∑ i, read (values i) := by
  have diagonalRoots : (Matrix.diagonal (fun i => (values i : ℂ))).charpoly.roots =
      Multiset.map (fun i => (values i : ℂ)) Finset.univ.val := by
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have eigenvalues := hermitian.roots_charpoly_eq_eigenvalues.symm.trans diagonalRoots
  have sums := congrArg (fun roots : Multiset ℂ => (roots.map (fun z => read z.re)).sum) eigenvalues
  simpa [Multiset.map_map, Function.comp_def] using sums

theorem spectralEntropy_diagonal (p : PMF ι) :
    spectralEntropy (Matrix.diagonal (fun i => ((p i).toReal : ℂ)))
      (diagonal_pmf_positive p) (diagonal_pmf_trace p) = entropy p := by
  unfold spectralEntropy entropy
  simp only [spectralPMF_toReal]
  exact congrArg Neg.neg
    (diagonal_eigenvalue_sum (fun i => (p i).toReal) (diagonal_pmf_positive p).isHermitian
      (fun probability => probability * Real.log probability))

end

end LAlanine40K2025.Thermal.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
