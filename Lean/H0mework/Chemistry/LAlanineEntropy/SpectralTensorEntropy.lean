import H0mework.Chemistry.LAlanineEntropy.SpectralEntropyInvariance
import H0mework.Chemistry.LAlanineEntropy.ClassicalJointEntropy
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Basic

/-! # Tensor entropy is the product-PMF readout of the same spectral frames -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Quantum

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open scoped ComplexOrder ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem sourceSpectralDiagonalization (rho : Matrix ι ι ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    rho = (positive.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => ((spectralPMF rho positive normalized i).toReal : ℂ)) *
        star (positive.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) := by
  have source := positive.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at source
  simpa only [spectralPMF_toReal, RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using source

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem spectralEntropy_kronecker (rho : Matrix ι ι ℂ) (sigma : Matrix κ κ ℂ)
    (rhoPositive : rho.PosSemidef) (sigmaPositive : sigma.PosSemidef)
    (rhoTrace : rho.trace = 1) (sigmaTrace : sigma.trace = 1) :
    spectralEntropy (Matrix.kronecker rho sigma) (rhoPositive.kronecker sigmaPositive)
      (by
        change (Matrix.kroneckerMap (· * ·) rho sigma).trace = 1
        rw [Matrix.trace_kronecker, rhoTrace, sigmaTrace, mul_one]) =
        spectralEntropy rho rhoPositive rhoTrace + spectralEntropy sigma sigmaPositive sigmaTrace := by
  let p := spectralPMF rho rhoPositive rhoTrace
  let q := spectralPMF sigma sigmaPositive sigmaTrace
  let U := rhoPositive.isHermitian.eigenvectorUnitary
  let V := sigmaPositive.isHermitian.eigenvectorUnitary
  let W : Matrix.unitaryGroup (ι × κ) ℂ :=
    ⟨Matrix.kronecker (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ),
      Matrix.kronecker_mem_unitary U.property V.property⟩
  let diagonal := Matrix.diagonal (fun x => ((productPMF p q x).toReal : ℂ))
  have diagonalPositive : diagonal.PosSemidef := diagonal_pmf_positive (productPMF p q)
  have diagonalTrace : diagonal.trace = 1 := diagonal_pmf_trace (productPMF p q)
  have diagonalProduct : Matrix.kronecker
      (Matrix.diagonal (fun i => ((p i).toReal : ℂ)))
      (Matrix.diagonal (fun j => ((q j).toReal : ℂ))) = diagonal := by
    rw [Matrix.kronecker, Matrix.diagonal_kronecker_diagonal]
    apply congrArg Matrix.diagonal
    funext x
    obtain ⟨i, j⟩ := x
    simp only [productPMF_apply, ENNReal.toReal_mul, Complex.ofReal_mul]
  have generatedConjugation : Matrix.kronecker rho sigma =
      (W : Matrix (ι × κ) (ι × κ) ℂ) * diagonal * star (W : Matrix (ι × κ) (ι × κ) ℂ) := by
    calc
      _ = Matrix.kronecker
          ((U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => ((p i).toReal : ℂ)) * star (U : Matrix ι ι ℂ))
          ((V : Matrix κ κ ℂ) * Matrix.diagonal (fun j => ((q j).toReal : ℂ)) * star (V : Matrix κ κ ℂ)) :=
        congrArg₂ Matrix.kronecker (sourceSpectralDiagonalization rho rhoPositive rhoTrace)
          (sourceSpectralDiagonalization sigma sigmaPositive sigmaTrace)
      _ = _ := by
        simp only [Matrix.kronecker] at diagonalProduct ⊢
        rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul, diagonalProduct]
        change Matrix.kronecker (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ) * diagonal *
          Matrix.kronecker (star (U : Matrix ι ι ℂ)) (star (V : Matrix κ κ ℂ)) = _
        dsimp only [W]
        simp only [Matrix.kronecker, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_kronecker]
  calc
    _ = spectralEntropy
        ((W : Matrix (ι × κ) (ι × κ) ℂ) * diagonal * star (W : Matrix (ι × κ) (ι × κ) ℂ))
        (diagonalPositive.mul_mul_conjTranspose_same (W : Matrix (ι × κ) (ι × κ) ℂ))
        ((unitary_conjugate_trace diagonal W).trans diagonalTrace) :=
      spectralEntropy_eq_of_charpoly _ _ _ _ _ _ (congrArg Matrix.charpoly generatedConjugation)
    _ = spectralEntropy diagonal diagonalPositive diagonalTrace :=
      spectralEntropy_unitary_conjugation diagonal diagonalPositive diagonalTrace W
    _ = entropy (productPMF p q) := spectralEntropy_diagonal (productPMF p q)
    _ = _ := entropy_product p q

end

end LAlanine40K2025.Thermal.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
