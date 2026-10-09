import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Current

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Projection
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem component_zero (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (a j : ι) (lambda : ℂ)
    (row : ∀ k, H j k = if k = j then lambda else 0)
    (different : (hH.eigenvalues a : ℂ) ≠ lambda) :
    (hH.eigenvectorUnitary : Matrix ι ι ℂ) j a = 0 := by
  have eigen := congrFun (hH.mulVec_eigenvectorBasis a) j
  change (∑ k, H j k * (hH.eigenvectorUnitary : Matrix ι ι ℂ) k a) =
    (hH.eigenvalues a : ℂ) * (hH.eigenvectorUnitary : Matrix ι ι ℂ) j a at eigen
  simp_rw [row] at eigen
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at eigen
  by_contra nonzero
  exact different (mul_right_cancel₀ nonzero eigen).symm

theorem spectral_row_zero (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (a j : ι) (lambda : ℂ)
    (row : ∀ k, H j k = if k = j then lambda else 0)
    (different : (hH.eigenvalues a : ℂ) ≠ lambda) (k : ι) :
    Spectrum.spectralPure H hH a j k = 0 := by
  rw [spectralPure_entry, component_zero H hH a j lambda row different, zero_mul]

theorem source_controller_zero_row (a : Basis) (k : PairController) :
    Powered.Producer.poweredTotalHamiltonian ((a,a),(0 : Fin 2)) k =
      if k = ((a,a),(0 : Fin 2)) then 2*(Preparation.sourceEnergies a : ℂ)+1 else 0 := by
  by_cases orbit : pcOrbit k = s(a,a)
  · rcases k with ⟨pair,c⟩
    have pairEq : pair = (a,a) := by
      have choices : pair = (a,a) ∨ pair = (a,a) := Sym2.mk_eq_mk_iff.mp orbit
      exact choices.elim id id
    subst pair
    have entry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 c) (original_hpc_diagonal_block a)
    fin_cases c
    · change Powered.Producer.poweredTotalHamiltonian ((a,a),0) ((a,a),0) =
        2*(Preparation.sourceEnergies a : ℂ)+1 at entry
      simpa using entry
    · change Powered.Producer.poweredTotalHamiltonian ((a,a),0) ((a,a),1) = 0 at entry
      simpa using entry
  · have zero := source_hpc_preserves ((a,a),(0 : Fin 2)) k (fun equal => orbit equal.symm)
    rw [zero, if_neg]
    intro equal
    exact orbit (congrArg pcOrbit equal)

theorem original_donor_controller_zero (a : Basis) (k : PairController) :
    Source.donor ((a,a),(0 : Fin 2)) k = 0 := by
  apply spectral_row_zero Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian Spectrum.firstIndex
    ((a,a),(0 : Fin 2)) (2*(Preparation.sourceEnergies a : ℂ)+1)
    (source_controller_zero_row a)
  intro equal
  have realEqual : donorEigenvalue = 2*Preparation.sourceEnergies a+1 := by exact_mod_cast equal
  have upper := donorEigenvalue_ge_diagonal a
  linarith

def excitedIndex : PairController :=
  ((Spectrum.firstIndex,Spectrum.firstIndex),(1 : Fin 2))

theorem original_donor_single_support :
    ∀ i j, i ≠ excitedIndex ∨ j ≠ excitedIndex → Source.donor i j = 0 := by
  have outsideRow (i j : PairController) (different : i ≠ excitedIndex) : Source.donor i j = 0 := by
    by_cases orbit : pcOrbit i = Current.donorOrbit
    · rcases i with ⟨pair,c⟩
      have pairEq : pair = (Spectrum.firstIndex,Spectrum.firstIndex) := by
        have choices : pair = (Spectrum.firstIndex,Spectrum.firstIndex) ∨
            pair = (Spectrum.firstIndex,Spectrum.firstIndex) := Sym2.mk_eq_mk_iff.mp orbit
        exact choices.elim id id
      subst pair
      fin_cases c
      · exact original_donor_controller_zero _ _
      · exact False.elim (different rfl)
    · exact Current.donor_support i j (Or.inl orbit)
  intro i j outside
  rcases outside with left | right
  · exact outsideRow i j left
  · have symmetric := congrArg (fun M : Matrix PairController PairController ℂ => M i j)
      Source.donor_positive.isHermitian.eq
    simp only [Matrix.conjTranspose_apply] at symmetric
    rw [outsideRow j i right, star_zero] at symmetric
    exact symmetric.symm

theorem singleton_trace (rho : Matrix ι ι ℂ) (k : ι)
    (support : ∀ i j, i ≠ k ∨ j ≠ k → rho i j = 0) (normalized : rho.trace = 1) :
    rho = Spectrum.basisPure k := by
  have traceRead : rho.trace = rho k k := by
    unfold Matrix.trace Matrix.diag
    apply Finset.sum_eq_single k
    · intro i _ different
      exact support i i (Or.inl different)
    · intro absent
      exact False.elim (absent (Finset.mem_univ k))
  have center : rho k k = 1 := traceRead.symm.trans normalized
  ext i j
  by_cases left : i = k
  · subst i
    by_cases right : j = k
    · subst j
      simpa [Spectrum.basisPure] using center
    · rw [support k j (Or.inr right)]
      simp [Spectrum.basisPure, Matrix.diagonal, Ne.symm right]
  · rw [support i j (Or.inl left)]
    simp [Spectrum.basisPure, Matrix.diagonal, left]

theorem actual_donor : Source.donor = Spectrum.basisPure excitedIndex :=
  singleton_trace Source.donor excitedIndex original_donor_single_support Source.donor_trace

theorem actual_donor_eigenvalue : donorEigenvalue =
    2 * Preparation.sourceEnergies (Spectrum.firstIndex (ι := Basis)) + 3 := by
  have spectral := Spectrum.spectralPure_energy Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian (Spectrum.firstIndex (ι := PairController))
  change Collision.energy Powered.Producer.poweredTotalHamiltonian Source.donor = donorEigenvalue at spectral
  rw [actual_donor, energy_basisPure] at spectral
  have diagonal := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1)
    (original_hpc_diagonal_block (Spectrum.firstIndex (ι := Basis)))
  change Powered.Producer.poweredTotalHamiltonian excitedIndex excitedIndex =
    2*(Preparation.sourceEnergies (Spectrum.firstIndex (ι := Basis)) : ℂ)+3 at diagonal
  rw [diagonal] at spectral
  norm_num [Complex.add_re, Complex.mul_re] at spectral
  exact spectral.symm

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Projection
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
