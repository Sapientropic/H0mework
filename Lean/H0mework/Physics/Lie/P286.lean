/-
  Proposition 286: matrix-level Standard-Model block embedding.

  P270 fixed the direction of the Standard-Model gauge map: it is an injective
  embedding into the SU(7) carrier, not a quotient/surjection out of it.  This
  file lowers that certificate one layer by constructing the actual block
  matrix

      diag(C, W, z, z⁻¹)

  on the finite index type `Fin 3 ⊕ (Fin 2 ⊕ (Fin 1 ⊕ Fin 1))`, then transporting
  it to `Fin 7`.

  Boundary: this is the compact gauge-product embedding.  It does not address
  representation content, Higgs breaking, anomalies, RG running, or parameter
  values.
-/

import H0mework.Physics.RepresentationSources.P270
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! ## Concrete block matrix producer -/

namespace SaturationMonoid
namespace GaugeProjection
namespace ConcreteBlockDiagonal

open Matrix

/-- The concrete block-index carrier `3 + 2 + 1 + 1 = 7`. -/
abbrev SMBlockIndex := Fin 3 ⊕ (Fin 2 ⊕ (Fin 1 ⊕ Fin 1))

/-- A canonical equivalence from the block carrier to `Fin 7`. -/
noncomputable def smBlockIndexEquivFin7 : SMBlockIndex ≃ Fin 7 :=
  (Equiv.sumCongr (Equiv.refl (Fin 3))
      ((Equiv.sumCongr (Equiv.refl (Fin 2)) finSumFinEquiv).trans
        (finSumFinEquiv.trans (finCongr (show 2 + (1 + 1) = 4 by norm_num))))).trans
    (finSumFinEquiv.trans (finCongr (show 3 + 4 = 7 by norm_num)))

/-- The one-dimensional scalar block. -/
def scalarOneBlock (z : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  diagonal fun _ => z

@[simp]
theorem scalarOneBlock_one : scalarOneBlock 1 = 1 := by
  simp [scalarOneBlock]

@[simp]
theorem scalarOneBlock_mul (z w : ℂ) :
    scalarOneBlock (z * w) = scalarOneBlock z * scalarOneBlock w := by
  simp [scalarOneBlock, diagonal_mul_diagonal]

@[simp]
theorem det_scalarOneBlock (z : ℂ) :
    (scalarOneBlock z).det = z := by
  simp [scalarOneBlock]

theorem circle_mul_star_coe (z : Circle) :
    (z : ℂ) * star (z : ℂ) = 1 := by
  simp [Complex.mul_conj]

theorem scalarOneBlock_mem_unitary (z : Circle) :
    scalarOneBlock (z : ℂ) ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
  ext i j
  fin_cases i
  fin_cases j
  simpa [scalarOneBlock, Matrix.mul_apply] using circle_mul_star_coe z

theorem fromBlocks_zero_mem_unitary
    {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
    {A : Matrix m m ℂ} {D : Matrix n n ℂ}
    (hA : A ∈ Matrix.unitaryGroup m ℂ)
    (hD : D ∈ Matrix.unitaryGroup n ℂ) :
    Matrix.fromBlocks A 0 0 D ∈ Matrix.unitaryGroup (m ⊕ n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
  have hA' : A * Aᴴ = 1 := by
    simpa [star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hA)
  have hD' : D * Dᴴ = 1 := by
    simpa [star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hD)
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hA', hD', Matrix.fromBlocks_one]

theorem fromBlocks_zero_det_one
    {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
    (A : Matrix m m ℂ) (D : Matrix n n ℂ)
    (hA : A.det = 1) (hD : D.det = 1) :
    (Matrix.fromBlocks A 0 0 D).det = 1 := by
  rw [Matrix.det_fromBlocks_zero₂₁]
  simp [hA, hD]

/-- The hypercharge pair `diag(z, z⁻¹)`. -/
noncomputable def hyperchargePairBlock (z : Circle) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks (scalarOneBlock (z : ℂ)) 0 0 (scalarOneBlock ((z⁻¹ : Circle) : ℂ))

@[simp]
theorem hyperchargePairBlock_one : hyperchargePairBlock 1 = 1 := by
  simp [hyperchargePairBlock, Matrix.fromBlocks_one]

theorem hyperchargePairBlock_mem_unitary (z : Circle) :
    hyperchargePairBlock z ∈ Matrix.unitaryGroup (Fin 1 ⊕ Fin 1) ℂ := by
  exact fromBlocks_zero_mem_unitary
    (scalarOneBlock_mem_unitary z)
    (scalarOneBlock_mem_unitary z⁻¹)

theorem det_hyperchargePairBlock (z : Circle) :
    (hyperchargePairBlock z).det = 1 := by
  rw [hyperchargePairBlock, Matrix.det_fromBlocks_zero₂₁,
    det_scalarOneBlock, det_scalarOneBlock]
  simp

theorem hyperchargePairBlock_mul (z w : Circle) :
    hyperchargePairBlock (z * w) = hyperchargePairBlock z * hyperchargePairBlock w := by
  simp [hyperchargePairBlock, Matrix.fromBlocks_multiply, mul_comm]

/-- The weak + hypercharge block `diag(W, z, z⁻¹)`. -/
noncomputable def weakHyperchargeBlock (w : SU2Gauge) (z : Circle) :
    Matrix (Fin 2 ⊕ (Fin 1 ⊕ Fin 1)) (Fin 2 ⊕ (Fin 1 ⊕ Fin 1)) ℂ :=
  Matrix.fromBlocks (w : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (hyperchargePairBlock z)

@[simp]
theorem weakHyperchargeBlock_one : weakHyperchargeBlock 1 1 = 1 := by
  simp [weakHyperchargeBlock, Matrix.fromBlocks_one]

theorem weakHyperchargeBlock_mem_specialUnitary (w : SU2Gauge) (z : Circle) :
    weakHyperchargeBlock w z ∈
      Matrix.specialUnitaryGroup (Fin 2 ⊕ (Fin 1 ⊕ Fin 1)) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · exact fromBlocks_zero_mem_unitary
      (Matrix.specialUnitaryGroup_le_unitaryGroup w.2)
      (hyperchargePairBlock_mem_unitary z)
  · exact fromBlocks_zero_det_one
      (w : Matrix (Fin 2) (Fin 2) ℂ) (hyperchargePairBlock z)
      w.2.2 (det_hyperchargePairBlock z)

theorem weakHyperchargeBlock_mul (w₁ w₂ : SU2Gauge) (z₁ z₂ : Circle) :
    weakHyperchargeBlock (w₁ * w₂) (z₁ * z₂) =
      weakHyperchargeBlock w₁ z₁ * weakHyperchargeBlock w₂ z₂ := by
  simp [weakHyperchargeBlock, Matrix.fromBlocks_multiply, hyperchargePairBlock_mul]

/-- The raw block matrix `diag(C, W, z, z⁻¹)` on the block carrier. -/
noncomputable def rawBlockDiagonal (g : StandardModelGaugeGroup) :
    Matrix SMBlockIndex SMBlockIndex ℂ :=
  Matrix.fromBlocks (g.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0
    (weakHyperchargeBlock g.2.1 g.2.2)

@[simp]
theorem rawBlockDiagonal_one : rawBlockDiagonal 1 = 1 := by
  simp [rawBlockDiagonal, Matrix.fromBlocks_one]

theorem rawBlockDiagonal_mem_specialUnitary (g : StandardModelGaugeGroup) :
    rawBlockDiagonal g ∈ Matrix.specialUnitaryGroup SMBlockIndex ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · exact fromBlocks_zero_mem_unitary
      (Matrix.specialUnitaryGroup_le_unitaryGroup g.1.2)
      (weakHyperchargeBlock_mem_specialUnitary g.2.1 g.2.2).1
  · exact fromBlocks_zero_det_one
      (g.1 : Matrix (Fin 3) (Fin 3) ℂ) (weakHyperchargeBlock g.2.1 g.2.2)
      g.1.2.2 (weakHyperchargeBlock_mem_specialUnitary g.2.1 g.2.2).2

theorem rawBlockDiagonal_mul (g h : StandardModelGaugeGroup) :
    rawBlockDiagonal (g * h) = rawBlockDiagonal g * rawBlockDiagonal h := by
  simp [rawBlockDiagonal, Matrix.fromBlocks_multiply, weakHyperchargeBlock_mul]

/-- The concrete block embedding on the block-index carrier. -/
noncomputable def blockDiagonalSMBlock :
    StandardModelGaugeGroup →* Matrix.specialUnitaryGroup SMBlockIndex ℂ where
  toFun g := ⟨rawBlockDiagonal g, rawBlockDiagonal_mem_specialUnitary g⟩
  map_one' := by
    exact Subtype.ext rawBlockDiagonal_one
  map_mul' g h := by
    exact Subtype.ext (rawBlockDiagonal_mul g h)

theorem blockDiagonalSMBlock_injective :
    Function.Injective blockDiagonalSMBlock := by
  intro g h hgh
  have hraw : rawBlockDiagonal g = rawBlockDiagonal h := congrArg Subtype.val hgh
  rw [rawBlockDiagonal, rawBlockDiagonal, Matrix.fromBlocks_inj] at hraw
  rcases hraw with ⟨hc, _, _, hwh⟩
  rw [weakHyperchargeBlock, weakHyperchargeBlock, Matrix.fromBlocks_inj] at hwh
  rcases hwh with ⟨hw, _, _, hyh⟩
  rw [hyperchargePairBlock, hyperchargePairBlock, Matrix.fromBlocks_inj] at hyh
  rcases hyh with ⟨hy, _, _, _⟩
  ext <;> simp_all [scalarOneBlock]

theorem reindex_mem_unitary
    {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
    (e : m ≃ n) {A : Matrix m m ℂ}
    (hA : A ∈ Matrix.unitaryGroup m ℂ) :
    Matrix.reindex e e A ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
  have hA' : A * Aᴴ = 1 := by
    simpa [star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hA)
  calc
    Matrix.reindex e e A * (Matrix.reindex e e A)ᴴ
        = Matrix.reindex e e (A * Aᴴ) := by
          rw [Matrix.conjTranspose_reindex]
          simp
    _ = 1 := by
          rw [hA']
          simp

theorem reindex_mem_specialUnitary
    {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
    (e : m ≃ n) {A : Matrix m m ℂ}
    (hA : A ∈ Matrix.specialUnitaryGroup m ℂ) :
    Matrix.reindex e e A ∈ Matrix.specialUnitaryGroup n ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hA ⊢
  refine ⟨reindex_mem_unitary e hA.1, ?_⟩
  rw [Matrix.det_reindex_self, hA.2]

/-- The transported raw block matrix on `Fin 7`. -/
noncomputable def rawBlockDiagonalFin7 (g : StandardModelGaugeGroup) :
    Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.reindex smBlockIndexEquivFin7 smBlockIndexEquivFin7 (rawBlockDiagonal g)

theorem rawBlockDiagonalFin7_mem_specialUnitary (g : StandardModelGaugeGroup) :
    rawBlockDiagonalFin7 g ∈ Matrix.specialUnitaryGroup (Fin 7) ℂ :=
  reindex_mem_specialUnitary smBlockIndexEquivFin7 (rawBlockDiagonal_mem_specialUnitary g)

@[simp]
theorem rawBlockDiagonalFin7_one : rawBlockDiagonalFin7 1 = 1 := by
  simp [rawBlockDiagonalFin7]

theorem rawBlockDiagonalFin7_mul (g h : StandardModelGaugeGroup) :
    rawBlockDiagonalFin7 (g * h) = rawBlockDiagonalFin7 g * rawBlockDiagonalFin7 h := by
  simp only [rawBlockDiagonalFin7, rawBlockDiagonal_mul]
  exact (Matrix.reindexLinearEquiv_mul ℂ ℂ smBlockIndexEquivFin7 smBlockIndexEquivFin7
    smBlockIndexEquivFin7 (rawBlockDiagonal g) (rawBlockDiagonal h)).symm

/-- THEOREM 1: the concrete `diag(C,W,z,z⁻¹)` map is a homomorphism into `SU(7)`. -/
noncomputable def blockDiagonalFin7 : StandardModelGaugeGroup →* SU7Gauge where
  toFun g := ⟨rawBlockDiagonalFin7 g, rawBlockDiagonalFin7_mem_specialUnitary g⟩
  map_one' := by
    exact Subtype.ext rawBlockDiagonalFin7_one
  map_mul' g h := by
    exact Subtype.ext (rawBlockDiagonalFin7_mul g h)

/-- THEOREM 2: the concrete block embedding into `SU(7)` is injective. -/
theorem blockDiagonalFin7_injective :
    Function.Injective blockDiagonalFin7 := by
  intro g h hgh
  apply blockDiagonalSMBlock_injective
  apply Subtype.ext
  have hraw : rawBlockDiagonalFin7 g = rawBlockDiagonalFin7 h := congrArg Subtype.val hgh
  exact (Matrix.reindex smBlockIndexEquivFin7 smBlockIndexEquivFin7).injective hraw

/-- THEOREM 3: P270's abstract injective-certificate target is inhabited by
the concrete block-diagonal matrix formula. -/
noncomputable def concreteSU7BreakingChainCertificate :
    SU7StandardModelBreakingChainCertificate where
  blockDiagonal := blockDiagonalFin7
  blockDiagonal_injective := blockDiagonalFin7_injective

end ConcreteBlockDiagonal
end GaugeProjection
end SaturationMonoid
