import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.BinaryPointerDilation
import H0mework.Chemistry.LAlanineEntropy.SpectralTensorEntropy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer

open Quantum
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pointerZero : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => (((PMF.pure (0 : Fin 2)) i).toReal : ℂ))

theorem pointerZero_positive : pointerZero.PosSemidef := diagonal_pmf_positive _
theorem pointerZero_trace : pointerZero.trace = 1 := diagonal_pmf_trace _

theorem pointerZero_entropy : spectralEntropy pointerZero pointerZero_positive pointerZero_trace = 0 := by
  calc
    _ = Population.entropy (PMF.pure (0 : Fin 2)) := spectralEntropy_diagonal _
    _ = 0 := by simp [Population.entropy, PMF.pure_apply, Fin.sum_univ_succ]

def pointerIncidence : (ι ⊕ ι) ≃ (ι × Fin 2) where
  toFun := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  invFun x := if x.2 = 0 then Sum.inl x.1 else Sum.inr x.1
  left_inv x := by cases x <;> simp
  right_inv x := by rcases x with ⟨i, b⟩; fin_cases b <;> simp

omit [Fintype ι] [DecidableEq ι] in
theorem prepared_eq_pure_tensor (rho : Matrix ι ι ℂ) :
    prepared rho = (Matrix.kronecker rho pointerZero).submatrix pointerIncidence pointerIncidence := by
  ext i j
  cases i <;> cases j <;>
    simp [prepared, pointerZero, pointerIncidence, PMF.pure_apply,
      Matrix.fromBlocks, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.diagonal]

omit [DecidableEq ι] in
theorem prepared_positive (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) :
    (prepared rho).PosSemidef := by
  rw [prepared_eq_pure_tensor]
  exact (positive.kronecker pointerZero_positive).submatrix pointerIncidence

omit [DecidableEq ι] in
theorem trace_fromBlocks (A B C D : Matrix ι ι ℂ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks]

omit [DecidableEq ι] in
theorem prepared_trace (rho : Matrix ι ι ℂ) : (prepared rho).trace = rho.trace := by
  rw [prepared, trace_fromBlocks, Matrix.trace_zero, add_zero]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem submatrix_equiv_trace (rho : Matrix ι ι ℂ) (e : κ ≃ ι) :
    (rho.submatrix e e).trace = rho.trace :=
  Equiv.sum_comp e (fun i => rho i i)

theorem spectralEntropy_submatrix_equiv (rho : Matrix ι ι ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) (e : κ ≃ ι) :
    spectralEntropy (rho.submatrix e e) (positive.submatrix e)
      ((submatrix_equiv_trace rho e).trans normalized) = spectralEntropy rho positive normalized := by
  have same : (rho.submatrix e e).charpoly = rho.charpoly := Matrix.charpoly_reindex e.symm rho
  have roots := congrArg Polynomial.roots same
  rw [(positive.submatrix e).isHermitian.roots_charpoly_eq_eigenvalues,
    positive.isHermitian.roots_charpoly_eq_eigenvalues] at roots
  have read := congrArg (fun values : Multiset ℂ =>
    (values.map (fun z => z.re * Real.log z.re)).sum) roots
  unfold spectralEntropy Population.entropy
  simp only [spectralPMF_toReal]
  exact congrArg Neg.neg (by simpa [Multiset.map_map, Function.comp_def] using read)

theorem prepared_entropy (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) :
    spectralEntropy (prepared rho) (prepared_positive rho positive)
      ((prepared_trace rho).trans normalized) = spectralEntropy rho positive normalized := by
  have tensorTrace : (Matrix.kronecker rho pointerZero).trace = 1 := by
    rw [Matrix.kronecker, Matrix.trace_kronecker, normalized, pointerZero_trace, mul_one]
  have tensor := spectralEntropy_kronecker rho pointerZero positive pointerZero_positive normalized pointerZero_trace
  have reindexed := spectralEntropy_submatrix_equiv (Matrix.kronecker rho pointerZero)
    (positive.kronecker pointerZero_positive) tensorTrace (pointerIncidence (ι := ι))
  simpa only [← prepared_eq_pure_tensor] using
    reindexed.trans (tensor.trans (by rw [pointerZero_entropy, add_zero]))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
