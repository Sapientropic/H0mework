import H0mework.Quantum.GNS.NormalizedGram

/-! A vector preparation uses the existing normalized Gram construction.
Its matrix state and its positive evaluation retain the same vector incidence. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.State

open scoped ComplexOrder
open Matrix
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
  LAlanine40K2025.Thermal.Preparation

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def column (v : ι → ℂ) (anchor : ι) : Matrix ι ι ℂ :=
  fun row col => if col = anchor then v row else 0

def pureMatrix (v : ι → ℂ) : Matrix ι ι ℂ := vecMulVec v (star v)

theorem column_gram (v : ι → ℂ) (anchor : ι) :
    gram (column v anchor) = pureMatrix v := by
  ext row col
  simp [gram, column, Matrix.mul_apply, Matrix.conjTranspose_apply, pureMatrix, vecMulVec]

omit [DecidableEq ι] in
theorem pureMatrix_posSemidef (v : ι → ℂ) : (pureMatrix v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

omit [DecidableEq ι] in
theorem pureMatrix_trace (v : ι → ℂ) :
    (pureMatrix v).trace = ∑ i, star (v i) * v i := by
  simp only [pureMatrix, Matrix.trace_vecMulVec, dotProduct, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem column_ne_zero (v : ι → ℂ) (anchor : ι)
    (h : (∑ i, star (v i) * v i) = 1) : column v anchor ≠ 0 := by
  intro hzero
  have vz : v = 0 := by
    funext i
    have atColumn := congrArg (fun A : Matrix ι ι ℂ => A i anchor) hzero
    simpa [column] using atColumn
  simp [vz] at h

theorem column_gramMass (v : ι → ℂ) (anchor : ι)
    (h : (∑ i, star (v i) * v i) = 1) : gramMass (column v anchor) = 1 := by
  rw [gramMass, column_gram, pureMatrix_trace, h]
  rfl

theorem normalizedGram_column (v : ι → ℂ) (anchor : ι)
    (h : (∑ i, star (v i) * v i) = 1) :
    normalizedGram (column v anchor) = pureMatrix v := by
  rw [normalizedGram, column_gramMass v anchor h, inv_one, one_smul, column_gram]

def vectorEvaluation (v : ι → ℂ) : Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun A := star v ⬝ᵥ (A *ᵥ v)
  map_add' A B := by simp only [Matrix.add_mulVec, dotProduct_add]
  map_smul' c A := by
    simp only [Matrix.smul_mulVec, dotProduct_smul, RingHom.id_apply]

omit [DecidableEq ι] in
theorem vectorEvaluation_positive (v : ι → ℂ) (A : Matrix ι ι ℂ)
    (hA : A.PosSemidef) : 0 ≤ vectorEvaluation v A :=
  hA.dotProduct_mulVec_nonneg v

theorem vectorEvaluation_one (v : ι → ℂ)
    (h : (∑ i, star (v i) * v i) = 1) : vectorEvaluation v 1 = 1 := by
  simpa only [vectorEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.one_mulVec, dotProduct, Pi.star_apply] using h

omit [DecidableEq ι] in
theorem vectorEvaluation_eq_trace (v : ι → ℂ) (A : Matrix ι ι ℂ) :
    vectorEvaluation v A = (pureMatrix v * A).trace := by
  rw [Matrix.trace_mul_comm, pureMatrix, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  exact dotProduct_comm _ _

omit [DecidableEq ι] in
theorem pureMatrix_idempotent (v : ι → ℂ)
    (h : (∑ i, star (v i) * v i) = 1) : pureMatrix v * pureMatrix v = pureMatrix v := by
  have dot : star v ⬝ᵥ v = 1 := h
  rw [pureMatrix, Matrix.vecMulVec_mul_vecMulVec, dot, one_smul]

theorem pureMatrix_complement_posSemidef (v : ι → ℂ)
    (h : (∑ i, star (v i) * v i) = 1) : (1 - pureMatrix v).PosSemidef := by
  have hermitian := (pureMatrix_posSemidef v).isHermitian
  have square : (1 - pureMatrix v) * (1 - pureMatrix v).conjTranspose =
      1 - pureMatrix v := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hermitian.eq,
      sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, pureMatrix_idempotent v h]
    abel
  rw [← square]
  exact Matrix.posSemidef_self_mul_conjTranspose _

omit [DecidableEq ι] in
theorem vectorEvaluation_pureMatrix (v w : ι → ℂ) :
    vectorEvaluation v (pureMatrix w) = (Complex.normSq (star w ⬝ᵥ v) : ℂ) := by
  change star v ⬝ᵥ (vecMulVec w (star w) *ᵥ v) = _
  rw [Matrix.vecMulVec_mulVec]
  rw [dotProduct_smul]
  change (star v ⬝ᵥ w) * (star w ⬝ᵥ v) = _
  rw [Complex.normSq_eq_conj_mul_self]
  have overlap : starRingEnd ℂ (star w ⬝ᵥ v) = star v ⬝ᵥ w := by
    simp only [dotProduct, map_sum, map_mul, Pi.star_apply, Complex.star_def]
    apply Finset.sum_congr rfl
    intro i _
    simp only [starRingEnd_self_apply]
    ring
  rw [overlap]

end
end SaturationMonoid.PhysicsCore.Stage9DEF.State
