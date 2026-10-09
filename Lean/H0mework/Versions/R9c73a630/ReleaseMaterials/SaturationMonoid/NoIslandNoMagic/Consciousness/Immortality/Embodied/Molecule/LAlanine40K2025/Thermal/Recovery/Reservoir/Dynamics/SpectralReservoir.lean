import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Producer.SourceGeneratedWholePCCharging

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Spectrum

open Collision Quantum Work.Capacity
open scoped Matrix ComplexOrder BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def firstIndex : ι := spectralIndex.symm ⟨0, Fintype.card_pos⟩
def lastIndex : ι := spectralReverse (firstIndex (ι := ι))

def basisPure (i : ι) : Matrix ι ι ℂ := Matrix.diagonal (fun j => if j = i then 1 else 0)

omit [Fintype ι] [Nonempty ι] in
theorem basisPure_positive (i : ι) : (basisPure i).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro j
  split_ifs <;> simp

omit [Nonempty ι] in
theorem basisPure_trace (i : ι) : (basisPure i).trace = 1 := by simp [basisPure, Matrix.trace_diagonal]

def spectralPure (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (i : ι) : Matrix ι ι ℂ :=
  conjugation hH.eigenvectorUnitary (basisPure i)

omit [Nonempty ι] in
theorem spectralPure_positive (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (i : ι) :
    (spectralPure H hH i).PosSemidef := conjugation_posSemidef _ _ (basisPure_positive i)

omit [Nonempty ι] in
theorem spectralPure_trace (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (i : ι) :
    (spectralPure H hH i).trace = 1 := (conjugation_trace _ _).trans (basisPure_trace i)

omit [Nonempty ι] in
theorem spectralPure_energy (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (i : ι) :
    energy H (spectralPure H hH i) = hH.eigenvalues i := by
  conv_lhs => arg 1; rw [hH.spectral_theorem]
  change energy (Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary _) (Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary _) = _
  rw [energy_unitary_conjugation]
  simp [energy, basisPure, Matrix.trace, Matrix.diag]

theorem eigenvalue_le_first (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (i : ι) :
    hH.eigenvalues i ≤ hH.eigenvalues (firstIndex (ι := ι)) := by
  change hH.eigenvalues₀ (spectralIndex i) ≤ hH.eigenvalues₀ (spectralIndex firstIndex)
  rw [firstIndex, Equiv.apply_symm_apply]
  exact hH.eigenvalues₀_antitone (Fin.zero_le _)

theorem last_le_eigenvalue (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (i : ι) :
    hH.eigenvalues (lastIndex (ι := ι)) ≤ hH.eigenvalues i := by
  change hH.eigenvalues₀ (spectralIndex lastIndex) ≤ hH.eigenvalues₀ (spectralIndex i)
  simp only [lastIndex, spectralReverse, Equiv.trans_apply, Equiv.apply_symm_apply, firstIndex]
  apply hH.eigenvalues₀_antitone
  change (spectralIndex i).val ≤ Fintype.card ι - 1
  exact Nat.le_sub_one_of_lt (spectralIndex i).isLt

theorem energy_spectral_bounds (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    hH.eigenvalues (lastIndex (ι := ι)) ≤ energy H rho ∧
      energy H rho ≤ hH.eigenvalues (firstIndex (ι := ι)) := by
  let A := conjugation (star hH.eigenvectorUnitary) rho
  have apos : A.PosSemidef := conjugation_posSemidef _ _ positive
  have asum : ∑ i, (A i i).re = 1 := by
    have h : A.trace = 1 := (conjugation_trace _ _).trans normalized
    simpa only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.one_re] using congrArg Complex.re h
  have read : energy H rho = ∑ i, hH.eigenvalues i * (A i i).re := by
    rw [← energy_unitary_conjugation H rho (star hH.eigenvectorUnitary), hH.conjStarAlgAut_star_eigenvectorUnitary]
    change energy (Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))) A = _
    simp [energy, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.mul_re]
  rw [read]
  constructor
  · calc
      _ = ∑ i, hH.eigenvalues lastIndex * (A i i).re := by rw [← Finset.mul_sum, asum, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (last_le_eigenvalue H hH i)
        (Complex.nonneg_iff.mp (apos.diag_nonneg (i := i))).1
  · calc
      _ ≤ ∑ i, hH.eigenvalues firstIndex * (A i i).re := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (eigenvalue_le_first H hH i) (Complex.nonneg_iff.mp (apos.diag_nonneg (i := i))).1
      _ = _ := by rw [← Finset.mul_sum, asum, mul_one]

def reservoirState (H : Matrix ι ι ℂ) (hH : H.IsHermitian) : Matrix ι ι ℂ := spectralPure H hH firstIndex

def extraction (H : Matrix ι ι ℂ) (hH : H.IsHermitian) : Matrix.unitaryGroup ι ℂ :=
  hH.eigenvectorUnitary * permutationUnitary (Equiv.swap firstIndex lastIndex) * star hH.eigenvectorUnitary

theorem extraction_acts (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    Unitary.conjStarAlgAut ℂ _ (extraction H hH) (reservoirState H hH) = spectralPure H hH lastIndex := by
  have cancel : Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) (star hH.eigenvectorUnitary)
      (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hH.eigenvectorUnitary (basisPure firstIndex)) = basisPure firstIndex := by
    rw [← Unitary.conjStarAlgAut_mul_apply]
    simp
  change Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)
    (hH.eigenvectorUnitary * permutationUnitary (Equiv.swap firstIndex lastIndex) * star hH.eigenvectorUnitary)
    (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hH.eigenvectorUnitary (basisPure firstIndex)) =
    Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hH.eigenvectorUnitary (basisPure lastIndex)
  rw [Unitary.conjStarAlgAut_mul_apply, Unitary.conjStarAlgAut_mul_apply, cancel]
  rw [basisPure, permutationUnitary_diagonal]
  congr 1
  ext i j
  simp [basisPure, Equiv.swap_apply_eq_iff]

theorem passive_energy_floor (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    hH.eigenvalues (lastIndex (ι := ι)) ≤ passiveEnergy H rho hH positive.isHermitian := by
  rw [← passiveEnergy_attained, ← passiveUnitary_generates]
  exact (energy_spectral_bounds H _ hH (conjugation_posSemidef _ _ positive)
    ((conjugation_trace _ _).trans normalized)).1

theorem supplied_capacity_margin (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    energy H (reservoirState H hH) - energy H rho ≤
      (energy H (reservoirState H hH) -
        energy H (Unitary.conjStarAlgAut ℂ _ (extraction H hH) (reservoirState H hH))) -
      ergotropy H rho hH positive.isHermitian := by
  rw [extraction_acts, spectralPure_energy, ergotropy]
  linarith [passive_energy_floor H rho hH positive normalized]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Spectrum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
