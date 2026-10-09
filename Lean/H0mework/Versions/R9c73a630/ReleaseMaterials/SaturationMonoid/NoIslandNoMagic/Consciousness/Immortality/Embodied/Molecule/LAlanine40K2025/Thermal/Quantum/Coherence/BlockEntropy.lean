import H0mework.Versions.R9c73a630.ThirdParty.Physlib.QuantumInfo.Entropy.VonNeumann
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

set_option autoImplicit false
set_option maxRecDepth 16384

namespace FullGammaBlockEntropy

open scoped Matrix ComplexOrder
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable instance : ContinuousFunctionalCalculus ℝ
    (CStarMatrix ι ι ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

private noncomputable instance : ContinuousFunctionalCalculus ℝ
    (CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

def blockMatrix (A B : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks A 0 0 B

omit [DecidableEq ι] in
theorem blockMatrix_posSemidef {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (blockMatrix A B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.IsHermitian.fromBlocks hA.isHermitian (by simp) hB.isHermitian
  · intro x
    have hsplit : star x ⬝ᵥ (blockMatrix A B *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
          star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
      simp [blockMatrix, Matrix.fromBlocks_mulVec, dotProduct,
        Fintype.sum_sum_type, Function.comp_def]
    rw [hsplit]
    exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hB.dotProduct_mulVec_nonneg _)

omit [DecidableEq ι] in
theorem blockMatrix_trace (A B : Matrix ι ι ℂ) :
    (blockMatrix A B).trace = A.trace + B.trace := by
  simp [blockMatrix, Matrix.trace, Fintype.sum_sum_type, Matrix.fromBlocks]

def blockState (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (ρ σ : MState ι) : MState (ι ⊕ ι) where
  M := ⟨blockMatrix (p • ρ.m) (q • σ.m),
    blockMatrix_posSemidef (ρ.psd.smul hp) (σ.psd.smul hq) |>.isHermitian⟩
  nonneg := HermitianMat.zero_le_iff.mpr
    (blockMatrix_posSemidef (ρ.psd.smul hp) (σ.psd.smul hq))
  tr := by
    change (blockMatrix (p • ρ.m) (q • σ.m)).trace.re = 1
    rw [blockMatrix_trace, Matrix.trace_smul, Matrix.trace_smul, ρ.tr', σ.tr']
    simpa only [Complex.real_smul, smul_eq_mul, mul_one, Complex.add_re, Complex.ofReal_re]
      using hpq

theorem blockState_m (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (ρ σ : MState ι) :
    (blockState p q hp hq hpq ρ σ).m = blockMatrix (p • ρ.m) (q • σ.m) := rfl

def blockHom : (Matrix ι ι ℂ × Matrix ι ι ℂ) →⋆ₐ[ℝ]
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ where
  toFun x := blockMatrix x.1 x.2
  map_one' := by
    simp [blockMatrix, Matrix.fromBlocks_one]
  map_mul' := by
    intro x y
    simp [blockMatrix, Matrix.fromBlocks_multiply]
  map_zero' := by
    simp [blockMatrix]
  map_add' := by
    intro x y
    simp [blockMatrix, Matrix.fromBlocks_add]
  commutes' := by
    intro r
    simp only [Algebra.algebraMap_eq_smul_one]
    change blockMatrix (r • 1) (r • 1) = r • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    calc
      blockMatrix (r • 1) (r • 1) =
          Matrix.fromBlocks (r • (1 : Matrix ι ι ℂ)) (r • (0 : Matrix ι ι ℂ))
            (r • (0 : Matrix ι ι ℂ)) (r • (1 : Matrix ι ι ℂ)) := by
          simp [blockMatrix]
      _ = r • Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (1 : Matrix ι ι ℂ) := by
          rw [Matrix.fromBlocks_smul]
      _ = r • 1 := by rw [Matrix.fromBlocks_one]
  map_star' := by
    intro x
    ext (i | i) (j | j) <;>
      simp [blockMatrix, Matrix.star_eq_conjTranspose, Matrix.fromBlocks]

def blockHomC : (CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ) →⋆ₐ[ℝ]
    CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ where
  toFun x := blockMatrix x.1 x.2
  map_one' := by
    change blockMatrix (1 : Matrix ι ι ℂ) 1 = 1
    exact blockHom.map_one
  map_mul' := by
    intro x y
    change blockMatrix (x.1 * y.1) (x.2 * y.2) =
      blockMatrix x.1 x.2 * blockMatrix y.1 y.2
    exact blockHom.map_mul (x.1, x.2) (y.1, y.2)
  map_zero' := by
    change blockMatrix (0 : Matrix ι ι ℂ) 0 = 0
    exact blockHom.map_zero
  map_add' := by
    intro x y
    change blockMatrix (x.1 + y.1) (x.2 + y.2) =
      blockMatrix x.1 x.2 + blockMatrix y.1 y.2
    exact blockHom.map_add (x.1, x.2) (y.1, y.2)
  commutes' := by
    intro r
    simp only [Algebra.algebraMap_eq_smul_one]
    change blockMatrix (r • 1) (r • 1) =
      r • (1 : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    calc
      blockMatrix (r • 1) (r • 1) =
          Matrix.fromBlocks (r • (1 : Matrix ι ι ℂ)) (r • (0 : Matrix ι ι ℂ))
            (r • (0 : Matrix ι ι ℂ)) (r • (1 : Matrix ι ι ℂ)) := by simp [blockMatrix]
      _ = r • Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (1 : Matrix ι ι ℂ) := by
          rw [Matrix.fromBlocks_smul]
      _ = r • 1 := by rw [Matrix.fromBlocks_one]
  map_star' := by
    intro x
    change blockMatrix (star x.1) (star x.2) = star (blockMatrix x.1 x.2)
    exact map_star blockHom (x.1, x.2)

theorem blockC_cfc (f : ℝ → ℝ) (hf : Continuous f)
    (A B : CStarMatrix ι ι ℂ) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    cfc f (blockHomC (A, B)) = blockHomC (cfc f A, cfc f B) := by
  let φ : (CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ) →⋆ₐ[ℝ]
      CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ := blockHomC
  have hφ : Continuous φ := by
    change Continuous (fun x : CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ =>
      (Matrix.fromBlocks x.1 0 0 x.2 : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ))
    fun_prop
  have hpair : IsSelfAdjoint (A, B) := by
    change star (A, B) = (A, B)
    exact Prod.ext hA.star_eq hB.star_eq
  have hpair' : IsSelfAdjoint (φ (A, B)) := hpair.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := (A, B))
    (hf := by simpa [Prod.spectrum_eq] using hf.continuousOn)
    (hφ := hφ) (ha := hpair) (hφa := hpair')
  have hprod : cfc (R := ℝ) f (A, B) = (cfc f A, cfc f B) := by
    exact cfc_map_prod (R := ℝ) (S := ℂ) f A B
      (hf := hf.continuousOn) (hab := hpair) (ha := hA) (hb := hB)
  simpa [φ, hprod] using hmap.symm

theorem matrixC_cfc (f : ℝ → ℝ) (hf : Continuous f)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    cfc f (CStarMatrix.ofMatrix A : CStarMatrix ι ι ℂ) =
      CStarMatrix.ofMatrix (cfc f A) := by
  let φ : Matrix ι ι ℂ →⋆ₐ[ℝ] CStarMatrix ι ι ℂ :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := ι) (A := ℂ)).restrictScalars ℝ |>.toStarAlgHom
  have hφ : Continuous φ := by
    change Continuous (fun A : Matrix ι ι ℂ => (CStarMatrix.ofMatrix A : CStarMatrix ι ι ℂ))
    exact continuous_id
  have hA' : IsSelfAdjoint A := hA.star_eq
  have hCA : IsSelfAdjoint (φ A) := hA'.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := A)
    (hf := hf.continuousOn) (hφ := hφ) (ha := hA') (hφa := hCA)
  change cfc f (CStarMatrix.ofMatrixStarAlgEquiv A) =
    CStarMatrix.ofMatrixStarAlgEquiv (cfc f A)
  exact hmap.symm

theorem blockMatrix_cfc (f : ℝ → ℝ) (hf : Continuous f)
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    cfc f (blockMatrix A B) = blockMatrix (cfc f A) (cfc f B) := by
  have hA' : IsSelfAdjoint (CStarMatrix.ofMatrix A : CStarMatrix ι ι ℂ) :=
    (show IsSelfAdjoint A from hA.star_eq).map
      ((CStarMatrix.ofMatrixStarAlgEquiv (n := ι) (A := ℂ)).restrictScalars ℝ).toStarAlgHom
  have hB' : IsSelfAdjoint (CStarMatrix.ofMatrix B : CStarMatrix ι ι ℂ) :=
    (show IsSelfAdjoint B from hB.star_eq).map
      ((CStarMatrix.ofMatrixStarAlgEquiv (n := ι) (A := ℂ)).restrictScalars ℝ).toStarAlgHom
  have hBlock : (blockMatrix A B).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hA (by simp) hB
  have hAC := matrixC_cfc f hf A hA
  have hBC := matrixC_cfc f hf B hB
  have hCC := matrixC_cfc f hf (blockMatrix A B) hBlock
  calc
    cfc f (blockMatrix A B) =
        CStarMatrix.ofMatrix.symm
          (cfc f (CStarMatrix.ofMatrix (blockMatrix A B) : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ)) := by
      rw [hCC]
      rfl
    _ = CStarMatrix.ofMatrix.symm
          (blockHomC (cfc f (CStarMatrix.ofMatrix A : CStarMatrix ι ι ℂ),
            cfc f (CStarMatrix.ofMatrix B : CStarMatrix ι ι ℂ))) := by
      exact congrArg CStarMatrix.ofMatrix.symm
        (blockC_cfc f hf (CStarMatrix.ofMatrix A) (CStarMatrix.ofMatrix B) hA' hB')
    _ = blockMatrix (cfc f A) (cfc f B) := by
      rw [hAC, hBC]
      rfl

theorem weighted_entropy (p : ℝ) (ρ : MState ι) :
    ((p • ρ.M).cfc Real.negMulLog).trace =
      Real.negMulLog p + p * Sᵥₙ ρ := by
  have hfun : (fun x : ℝ => Real.negMulLog (p * x)) =
      (fun x => Real.negMulLog p * x + p * Real.negMulLog x) := by
    funext x
    rw [Real.negMulLog_mul]
    ring
  have hcfc : ((p • ρ.M).cfc Real.negMulLog) =
      Real.negMulLog p • ρ.M + p • ρ.M.cfc Real.negMulLog := by
    rw [← ρ.M.cfc_const_mul_id p, ← HermitianMat.cfc_comp_apply]
    rw [hfun, HermitianMat.cfc_add_apply,
      HermitianMat.cfc_const_mul, HermitianMat.cfc_const_mul]
    simp only [HermitianMat.cfc_id']
  rw [hcfc, HermitianMat.trace_add, HermitianMat.trace_smul,
    HermitianMat.trace_smul, ρ.tr, Sᵥₙ_eq_trace_cfc_negMulLog]
  ring

theorem blockState_entropy (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q = 1) (ρ σ : MState ι) :
    Sᵥₙ (blockState p q hp hq hpq ρ σ) =
      Real.negMulLog p + Real.negMulLog q + p * Sᵥₙ ρ + q * Sᵥₙ σ := by
  have hA : (p • ρ.m).IsHermitian := (ρ.psd.smul hp).isHermitian
  have hB : (q • σ.m).IsHermitian := (σ.psd.smul hq).isHermitian
  have hleft : (cfc Real.negMulLog (p • ρ.m)).trace.re =
      ((p • ρ.M).cfc Real.negMulLog).trace := by
    rw [HermitianMat.trace_eq_re_trace, HermitianMat.mat_cfc]
    rfl
  have hright : (cfc Real.negMulLog (q • σ.m)).trace.re =
      ((q • σ.M).cfc Real.negMulLog).trace := by
    rw [HermitianMat.trace_eq_re_trace, HermitianMat.mat_cfc]
    rfl
  rw [Sᵥₙ_eq_trace_cfc_negMulLog, HermitianMat.trace_eq_re_trace]
  change (cfc Real.negMulLog
    (blockMatrix (p • ρ.m) (q • σ.m))).trace.re = _
  rw [blockMatrix_cfc Real.negMulLog Real.continuous_negMulLog _ _ hA hB,
    blockMatrix_trace, Complex.add_re, hleft, hright,
    weighted_entropy p ρ, weighted_entropy q σ]
  ring

end
end FullGammaBlockEntropy
