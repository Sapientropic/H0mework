import H0mework.Chemistry.LAlanineEntropy.UnitaryBornEntropy
import Mathlib.Analysis.Matrix.PosDef

/-! # Spectral and measured entropy are two reads of the same finite density matrix -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Quantum

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open scoped ComplexOrder ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι]

def diagonalPMF (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) (normalized : rho.trace = 1) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (rho i i).re) (by
    have total : ∑ i, (rho i i).re = 1 := by
      have realTrace := congrArg Complex.re normalized
      simpa only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.one_re] using realTrace
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun i _ => (Complex.nonneg_iff.mp (positive.diag_nonneg (i := i))).1), total, ENNReal.ofReal_one])

theorem diagonalPMF_toReal (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) (i : ι) :
    (diagonalPMF rho positive normalized i).toReal = (rho i i).re :=
  ENNReal.toReal_ofReal (Complex.nonneg_iff.mp (positive.diag_nonneg (i := i))).1

variable [DecidableEq ι]

theorem eigenvalues_normalized (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) : ∑ i, positive.isHermitian.eigenvalues i = 1 := by
  have trace := positive.isHermitian.trace_eq_sum_eigenvalues
  rw [normalized] at trace
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_one]
  exact trace.symm

def spectralPMF (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) (normalized : rho.trace = 1) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (positive.isHermitian.eigenvalues i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => positive.eigenvalues_nonneg i),
      eigenvalues_normalized rho positive normalized, ENNReal.ofReal_one])

theorem spectralPMF_toReal (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) (i : ι) :
    (spectralPMF rho positive normalized i).toReal = positive.isHermitian.eigenvalues i :=
  ENNReal.toReal_ofReal (positive.eigenvalues_nonneg i)

def spectralEntropy (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) (normalized : rho.trace = 1) : ℝ :=
  entropy (spectralPMF rho positive normalized)

theorem unitary_diagonal_complex (U : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) (i : ι) :
    ((U : Matrix ι ι ℂ) * Matrix.diagonal (fun j => (p j : ℂ)) * star (U : Matrix ι ι ℂ)) i i =
      ((∑ j, bornWeight U i j * p j : ℝ) : ℂ) := by
  rw [Matrix.mul_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal, Matrix.star_apply, Complex.ofReal_mul]
  simp only [bornWeight, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

theorem unitary_diagonal_real (U : Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) (i : ι) :
    (((U : Matrix ι ι ℂ) * Matrix.diagonal (fun j => (p j : ℂ)) * star (U : Matrix ι ι ℂ)) i i).re =
      ∑ j, p j * bornWeight U i j := by
  rw [unitary_diagonal_complex, Complex.ofReal_re]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem diagonalPMF_eq_born (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) :
    diagonalPMF rho positive normalized =
      bornPopulation positive.isHermitian.eigenvectorUnitary (spectralPMF rho positive normalized) := by
  ext i
  apply (ENNReal.toReal_eq_toReal_iff' ((diagonalPMF rho positive normalized).apply_ne_top i)
    ((bornPopulation _ _).apply_ne_top i)).mp
  rw [diagonalPMF_toReal, bornPopulation_toReal]
  simp only [spectralPMF_toReal]
  have expanded := positive.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at expanded
  conv_lhs => rw [expanded]
  exact unitary_diagonal_real _ _ i

theorem spectralEntropy_le_diagonal [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    spectralEntropy rho positive normalized ≤ entropy (diagonalPMF rho positive normalized) := by
  rw [diagonalPMF_eq_born]
  exact born_entropy_nondecreasing _ _

end

end LAlanine40K2025.Thermal.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
