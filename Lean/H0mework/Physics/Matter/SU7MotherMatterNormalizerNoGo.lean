import H0mework.Physics.Gauge.SU7MotherGaugeConnection
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# SU(7) singlet-swap normalizer and the full-module weight-pairing gate

The Stage-7 Phase-0 audit ruled out the current adjoint/P508 interpretation,
but changing the complete SU(7) representation is not by itself enough.  The
two singlet coordinates admit an actual determinant-one unitary swap.  It
fixes the color and weak coordinate blocks and conjugates the P286
hypercharge generator to its negative.

Consequently every representation action in which this group normalizer
intertwines the infinitesimal hypercharge action has linearly equivalent
`q` and `-q` weight spaces.  The abstract theorem below states that exact
responsibility boundary.  It is then instantiated without an extra premise
for the actual seven-dimensional fundamental matrix action.

This is a no-go/selection gate, not a matter producer.  A chiral low-energy
image must be selected by extra source-generated projection data that is not
forced to commute with this normalizer.
-/

namespace SaturationMonoid.PhysicsCore.SU7MotherMatterNormalizerNoGo

open Matrix
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory

noncomputable section

/-- The determinant-one `90°` rotation of the two singlet coordinates. -/
def singletSwapFinMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -1; 1, 0]

/-- The same rotation on the nested `Fin 1 ⊕ Fin 1` carrier used by P286. -/
def singletSwapBlock :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  fun row column =>
    match row, column with
    | Sum.inl _, Sum.inr _ => -1
    | Sum.inr _, Sum.inl _ => 1
    | _, _ => 0

theorem singletSwapBlock_reindex :
    singletSwapBlock =
      singletSwapFinMatrix.submatrix finSumFinEquiv finSumFinEquiv := by
  ext row column
  rcases row with row | row <;> rcases column with column | column <;>
    fin_cases row <;> fin_cases column <;>
    simp [singletSwapBlock, singletSwapFinMatrix, finSumFinEquiv]

/-- Identity on color and weak blocks, determinant-one rotation on the two
singlets. -/
def singletSwapNormalizerMatrix :
    Matrix SU7MotherIndex SU7MotherIndex ℂ :=
  Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks 1 0 0 singletSwapBlock)

theorem singletSwapNormalizer_star_mul :
    star singletSwapNormalizerMatrix * singletSwapNormalizerMatrix = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [singletSwapNormalizerMatrix, singletSwapBlock,
      star_eq_conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three]

theorem singletSwapNormalizer_mul_star :
    singletSwapNormalizerMatrix * star singletSwapNormalizerMatrix = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [singletSwapNormalizerMatrix, singletSwapBlock,
      star_eq_conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three]

theorem singletSwapNormalizer_det :
    Matrix.det singletSwapNormalizerMatrix = 1 := by
  rw [singletSwapNormalizerMatrix]
  simp only [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  rw [singletSwapBlock_reindex, Matrix.det_submatrix_equiv_self]
  simp [singletSwapFinMatrix, Matrix.det_fin_two]

/-- The singlet swap is an actual element of `SU(7)`, not a permutation with
determinant `-1`. -/
def singletSwapNormalizer :
    Matrix.specialUnitaryGroup SU7MotherIndex ℂ := by
  refine ⟨singletSwapNormalizerMatrix, ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  exact ⟨Matrix.mem_unitaryGroup_iff'.2 singletSwapNormalizer_star_mul,
    singletSwapNormalizer_det⟩

@[simp] theorem singletSwapNormalizer_colorBlock
    (row column : Fin 3) :
    singletSwapNormalizerMatrix (Sum.inl row) (Sum.inl column) =
      if row = column then 1 else 0 := by
  classical
  simp [singletSwapNormalizerMatrix, Matrix.one_apply]

@[simp] theorem singletSwapNormalizer_weakBlock
    (row column : Fin 2) :
    singletSwapNormalizerMatrix
        (Sum.inr (Sum.inl row)) (Sum.inr (Sum.inl column)) =
      if row = column then 1 else 0 := by
  classical
  simp [singletSwapNormalizerMatrix, Matrix.one_apply]

/-- The exact P286 hypercharge Lie generator inside the mother algebra. -/
def p286HyperchargeLieGenerator : SU7MotherLieMatrix :=
  p286LieBlockEmbed (0, 0, hyperchargeGenerator)

theorem singletSwapNormalizer_anticommutes_hypercharge :
    singletSwapNormalizerMatrix *
        (p286HyperchargeLieGenerator :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      -(p286HyperchargeLieGenerator :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        singletSwapNormalizerMatrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [singletSwapNormalizerMatrix, singletSwapBlock,
      p286HyperchargeLieGenerator, p286LieBlockEmbed, rawP286LieBlock,
      weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
      hyperchargeGenerator, Matrix.mul_apply]

/-- Conjugation by the actual SU(7) normalizer reverses hypercharge. -/
theorem singletSwapNormalizer_conjugates_hypercharge_to_neg :
    singletSwapNormalizerMatrix *
          (p286HyperchargeLieGenerator :
            Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        star singletSwapNormalizerMatrix =
      -(p286HyperchargeLieGenerator :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) := by
  calc
    singletSwapNormalizerMatrix *
          (p286HyperchargeLieGenerator :
            Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        star singletSwapNormalizerMatrix =
      (-(p286HyperchargeLieGenerator :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        singletSwapNormalizerMatrix) * star singletSwapNormalizerMatrix := by
          rw [singletSwapNormalizer_anticommutes_hypercharge]
    _ = -(p286HyperchargeLieGenerator :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        (singletSwapNormalizerMatrix * star singletSwapNormalizerMatrix) := by
          noncomm_ring
    _ = -(p286HyperchargeLieGenerator :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) := by
          rw [singletSwapNormalizer_mul_star]
          simp

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The eigenspace of an infinitesimal hypercharge action. -/
def WeightSpace (H : Module.End ℂ V) (charge : ℂ) : Submodule ℂ V where
  carrier := {vector | H vector = charge • vector}
  zero_mem' := by simp
  add_mem' := by
    intro first second hfirst hsecond
    calc
      H (first + second) = H first + H second := map_add H first second
      _ = charge • first + charge • second := by rw [hfirst, hsecond]
      _ = charge • (first + second) := (smul_add charge first second).symm
  smul_mem' := by
    intro scalar vector hvector
    calc
      H (scalar • vector) = scalar • H vector := map_smul H scalar vector
      _ = scalar • (charge • vector) := by rw [hvector]
      _ = charge • (scalar • vector) := by
        simp only [smul_smul]
        rw [mul_comm]

/-- Any invertible action that anticommutes with hypercharge transports the
entire charge-`q` weight space to the charge-`-q` weight space.  For an
integrated SU(7) representation the intended normalizer action is `ρ(w)`;
the explicit intertwining premise is kept visible instead of hidden inside a
nominal representation certificate. -/
def normalizerWeightPairingEquiv
    (H : Module.End ℂ V) (normalizer : V ≃ₗ[ℂ] V)
    (anticommutes : ∀ vector, normalizer (H vector) = -H (normalizer vector))
    (charge : ℂ) :
    WeightSpace H charge ≃ₗ[ℂ] WeightSpace H (-charge) := by
  let forward : WeightSpace H charge →ₗ[ℂ] WeightSpace H (-charge) :=
    { toFun := fun vector => ⟨normalizer vector, by
        change H (normalizer vector) = (-charge) • normalizer vector
        calc
          H (normalizer vector) = -normalizer (H vector) := by
            simpa using (congrArg Neg.neg (anticommutes vector)).symm
          _ = -normalizer (charge • vector) := by rw [vector.property]
          _ = (-charge) • normalizer vector := by simp ⟩
      map_add' := by intro first second; ext; simp
      map_smul' := by intro scalar vector; ext; simp }
  have inverseAnticommutes :
      ∀ vector, H (normalizer.symm vector) =
        -normalizer.symm (H vector) := by
    intro vector
    have applied := congrArg (fun value => normalizer.symm value)
      (anticommutes (normalizer.symm vector))
    simpa using applied
  let backward : WeightSpace H (-charge) →ₗ[ℂ] WeightSpace H charge :=
    { toFun := fun vector => ⟨normalizer.symm vector, by
        change H (normalizer.symm vector) = charge • normalizer.symm vector
        calc
          H (normalizer.symm vector) =
              -normalizer.symm (H vector) := inverseAnticommutes vector
          _ = -normalizer.symm ((-charge) • vector) := by rw [vector.property]
          _ = charge • normalizer.symm vector := by simp ⟩
      map_add' := by intro first second; ext; simp
      map_smul' := by intro scalar vector; ext; simp }
  exact
    { toLinearMap := forward
      invFun := backward
      left_inv := by intro vector; ext; simp [forward, backward]
      right_inv := by intro vector; ext; simp [forward, backward] }

theorem normalizerWeightMultiplicity_eq
    (H : Module.End ℂ V) (normalizer : V ≃ₗ[ℂ] V)
    (anticommutes : ∀ vector, normalizer (H vector) = -H (normalizer vector))
    (charge : ℂ) :
    Module.finrank ℂ (WeightSpace H charge) =
      Module.finrank ℂ (WeightSpace H (-charge)) :=
  (normalizerWeightPairingEquiv H normalizer anticommutes charge).finrank_eq

/-! ## Concrete fundamental-representation instance -/

abbrev SU7FundamentalMatterCarrier := SU7MotherIndex → ℂ

def fundamentalLieAction (matrix : SU7MotherLieMatrix) :
    Module.End ℂ SU7FundamentalMatterCarrier :=
  Matrix.mulVecLin (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)

def singletSwapFundamentalEquiv :
    SU7FundamentalMatterCarrier ≃ₗ[ℂ] SU7FundamentalMatterCarrier :=
  LinearEquiv.ofLinear
    (Matrix.mulVecLin singletSwapNormalizerMatrix)
    (Matrix.mulVecLin (star singletSwapNormalizerMatrix))
    (by
      apply LinearMap.ext
      intro vector
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply,
        LinearMap.id_apply]
      rw [Matrix.mulVec_mulVec, singletSwapNormalizer_mul_star]
      simp)
    (by
      apply LinearMap.ext
      intro vector
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply,
        LinearMap.id_apply]
      rw [Matrix.mulVec_mulVec, singletSwapNormalizer_star_mul]
      simp)

theorem singletSwapFundamental_anticommutes_hypercharge
    (vector : SU7FundamentalMatterCarrier) :
    singletSwapFundamentalEquiv
        (fundamentalLieAction p286HyperchargeLieGenerator vector) =
      -fundamentalLieAction p286HyperchargeLieGenerator
        (singletSwapFundamentalEquiv vector) := by
  change singletSwapNormalizerMatrix *ᵥ
      ((p286HyperchargeLieGenerator :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ vector) =
    -((p286HyperchargeLieGenerator :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ
      (singletSwapNormalizerMatrix *ᵥ vector))
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [singletSwapNormalizer_anticommutes_hypercharge]
  rw [neg_mul]
  exact Matrix.neg_mulVec vector
    ((p286HyperchargeLieGenerator :
      Matrix SU7MotherIndex SU7MotherIndex ℂ) *
      singletSwapNormalizerMatrix)

/-- The actual fundamental SU(7) action has equal `q` and `-q` weight
multiplicities.  A genuinely chiral low-energy image therefore cannot be the
unprojected full fundamental module. -/
theorem fundamentalWeightMultiplicity_eq (charge : ℂ) :
    Module.finrank ℂ
        (WeightSpace (fundamentalLieAction p286HyperchargeLieGenerator) charge) =
      Module.finrank ℂ
        (WeightSpace (fundamentalLieAction p286HyperchargeLieGenerator)
          (-charge)) :=
  normalizerWeightMultiplicity_eq
    (fundamentalLieAction p286HyperchargeLieGenerator)
    singletSwapFundamentalEquiv
    singletSwapFundamental_anticommutes_hypercharge
    charge

end
end SaturationMonoid.PhysicsCore.SU7MotherMatterNormalizerNoGo
