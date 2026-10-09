import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Soundness
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem strict_rows_posDef (M : Matrix n n ℂ) (hermitian : M.IsHermitian)
    (rows : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖M i j‖ < (M i i).re) : M.PosDef := by
  apply hermitian.posDef_iff_eigenvalues_pos.mpr
  intro k
  have eigenvector : Module.End.HasEigenvector (Matrix.toLin' M) (hermitian.eigenvalues k : ℂ)
      (hermitian.eigenvectorBasis k).ofLp := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · funext i
      simpa only [Matrix.toLin'_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul] using
        congrFun (hermitian.mulVec_eigenvectorBasis k) i
    · exact (WithLp.ofLp_eq_zero 2).ne.mpr (hermitian.eigenvectorBasis.orthonormal.ne_zero k)
  obtain ⟨i,ball⟩ := eigenvalue_mem_ball (Module.End.hasEigenvalue_of_hasEigenvector eigenvector)
  have normBound := (mem_closedBall_iff_norm.mp ball)
  have realBound := (Complex.abs_re_le_norm ((hermitian.eigenvalues k : ℂ) - M i i)).trans normBound
  simp only [Complex.sub_re, Complex.ofReal_re] at realBound
  linarith [(abs_le.mp realBound).1, rows i]

theorem congruence_posDef (M R : Matrix n n ℂ) (positive : (Rᴴ * M * R).PosDef) : M.PosDef := by
  have nonzero := (ne_of_gt positive.det_pos)
  rw [Matrix.det_mul, Matrix.det_mul] at nonzero
  have determinant : R.det ≠ 0 := by
    intro zero
    exact nonzero (by rw [zero, mul_zero])
  have invertible : IsUnit R := (Matrix.isUnit_iff_isUnit_det R).mpr (isUnit_iff_ne_zero.mpr determinant)
  apply (Matrix.IsUnit.posDef_star_left_conjugate_iff invertible).mp
  simpa only [Matrix.star_eq_conjTranspose] using positive

theorem shift_coordinates (A : Matrix n n ℂ) (hA : A.IsHermitian) (mu : ℝ) :
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * ((mu : ℂ) • 1 - A) * hA.eigenvectorUnitary =
      Matrix.diagonal (fun i => ((mu - hA.eigenvalues i : ℝ) : ℂ)) := by
  rw [← Matrix.star_eq_conjTranspose, ← Unitary.conjStarAlgAut_star_apply (S := ℂ)]
  rw [map_sub, map_smul, map_one, hA.conjStarAlgAut_star_eigenvectorUnitary]
  ext i j
  by_cases same : i = j
  · subst j
    simp [Matrix.diagonal]
  · simp [Matrix.diagonal, same]

theorem shift_posDef_upper (A : Matrix n n ℂ) (hA : A.IsHermitian) (mu : ℝ)
    (positive : ((mu : ℂ) • 1 - A).PosDef) (i : n) : hA.eigenvalues i < mu := by
  have conjugated := positive.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (show IsUnit (hA.eigenvectorUnitary : Matrix n n ℂ) from Unitary.isUnit_coe))
  rw [shift_coordinates] at conjugated
  have diagonal := (Matrix.posDef_diagonal_iff.mp conjugated) i
  have realPositive : 0 < mu - hA.eigenvalues i := by exact_mod_cast diagonal
  exact sub_pos.mp realPositive

def rankOne (w : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec w (star w)

theorem rankOne_coordinates (U : Matrix.unitaryGroup n ℂ) (w : n → ℂ) :
    (U : Matrix n n ℂ)ᴴ * rankOne w * U = rankOne ((U : Matrix n n ℂ)ᴴ *ᵥ w) := by
  simp only [rankOne, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

theorem two_diagonal_rankOne (a b : ℝ) (x y : ℂ)
    (positive : ( !![(a : ℂ) + x*star x, x*star y;
      y*star x, (b : ℂ)+y*star y] ).PosDef) : 0 < a ∨ 0 < b := by
  by_contra outside
  push Not at outside
  have diagonal := (Complex.pos_iff.mp (positive.diag_pos (i := (1 : Fin 2)))).1
  change 0 < ((b : ℂ)+y*star y).re at diagonal
  have determinant := (Complex.pos_iff.mp positive.det_pos).1
  rw [Matrix.det_fin_two] at determinant
  change 0 < (((a : ℂ)+x*star x)*((b : ℂ)+y*star y) - (x*star y)*(y*star x)).re at determinant
  have factor : ((a : ℂ)+x*star x)*((b : ℂ)+y*star y) - (x*star y)*(y*star x) =
      (a*b : ℝ) + (a : ℂ)*(y*star y) + (b : ℂ)*(x*star x) := by push_cast; ring
  rw [factor] at determinant
  simp only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.ofReal_re] at diagonal determinant
  have first : a * (b + Complex.normSq y) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg outside.1 diagonal.le
  have second : b * Complex.normSq x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg outside.2 (Complex.normSq_nonneg x)
  nlinarith

omit [Fintype n] in
theorem diagonal_rankOne_separation (d : n → ℝ) (w : n → ℂ)
    (positive : (Matrix.diagonal (fun i => (d i : ℂ)) + rankOne w).PosDef)
    (i j : n) (different : i ≠ j) : 0 < d i ∨ 0 < d j := by
  let inclusion : Fin 2 → n := ![i,j]
  have injective : Function.Injective inclusion := by
    intro a b equal
    fin_cases a <;> fin_cases b <;> simp_all [inclusion]
  have minor := positive.submatrix injective
  have equality : (Matrix.diagonal (fun i => (d i : ℂ)) + rankOne w).submatrix inclusion inclusion =
      !![(d i : ℂ)+w i*star (w i), w i*star (w j);
        w j*star (w i), (d j : ℂ)+w j*star (w j)] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.submatrix, inclusion, Matrix.diagonal, rankOne, Matrix.vecMulVec,
        different, Ne.symm different]
  rw [equality] at minor
  exact two_diagonal_rankOne (d i) (d j) (w i) (w j) minor

theorem rankOne_second_upper (A : Matrix n n ℂ) (hA : A.IsHermitian) (mu : ℝ) (w : n → ℂ)
    (positive : ((mu : ℂ) • 1 - A + rankOne w).PosDef)
    (i j : n) (different : i ≠ j) (ordered : hA.eigenvalues j ≤ hA.eigenvalues i) :
    hA.eigenvalues j < mu := by
  have conjugated := positive.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (show IsUnit (hA.eigenvectorUnitary : Matrix n n ℂ) from Unitary.isUnit_coe))
  rw [Matrix.mul_add, Matrix.add_mul, shift_coordinates, rankOne_coordinates] at conjugated
  rcases diagonal_rankOne_separation _ _ conjugated i j different with left | right <;> linarith

theorem shift_posSemidef_of_spectral_bounds (A : Matrix n n ℂ) (hA : A.IsHermitian) (mu : ℝ)
    (bounded : ∀ i, hA.eigenvalues i ≤ mu) : ((mu : ℂ) • 1 - A).PosSemidef := by
  have diagonal : (Matrix.diagonal (fun i => ((mu - hA.eigenvalues i : ℝ) : ℂ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => by exact_mod_cast (sub_nonneg.mpr (bounded i)))
  rw [← shift_coordinates] at diagonal
  apply (Matrix.IsUnit.posSemidef_star_left_conjugate_iff
    (show IsUnit (hA.eigenvectorUnitary : Matrix n n ℂ) from Unitary.isUnit_coe)).mp
  simpa only [Matrix.star_eq_conjTranspose] using diagonal

theorem maximum_gt_of_rayleigh (A : Matrix n n ℂ) (hA : A.IsHermitian) (mu : ℝ) (w : n → ℂ)
    (maximum : n) (ordered : ∀ i, hA.eigenvalues i ≤ hA.eigenvalues maximum)
    (witness : mu * (star w ⬝ᵥ w).re < (star w ⬝ᵥ (A *ᵥ w)).re) :
    mu < hA.eigenvalues maximum := by
  by_contra outside
  have bounded : ∀ i, hA.eigenvalues i ≤ mu := fun i =>
    (ordered i).trans (le_of_not_gt outside)
  have nonnegative := (shift_posSemidef_of_spectral_bounds A hA mu bounded).re_dotProduct_nonneg w
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul] at nonnegative
  change 0 ≤ ((mu : ℂ)*(star w ⬝ᵥ w) - star w ⬝ᵥ (A *ᵥ w)).re at nonnegative
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at nonnegative
  linarith

theorem integer_rows_dominant (M : Matrix n n Int)
    (margins : ∀ i, 0 < 2 * M i i - ∑ j, |M i j|) :
    ∀ i, ∑ j ∈ Finset.univ.erase i, ‖(M i j : ℂ)‖ < (M i i : ℂ).re := by
  intro i
  have nonnegative : (0 : Int) ≤ ∑ j, |M i j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have diagonal : 0 < M i i := by linarith [margins i]
  have split := Finset.sum_erase_add Finset.univ (fun j => |M i j|) (Finset.mem_univ i)
  rw [abs_of_pos diagonal] at split
  have off : (∑ j ∈ Finset.univ.erase i, |M i j|) < M i i := by linarith [margins i]
  simp only [Complex.norm_intCast, Complex.intCast_re, ← Int.cast_abs]
  exact_mod_cast off

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Soundness
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
