import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.MatrixBorder

open Matrix
open scoped Matrix

universe r
variable {R : Type r} {n : Nat}

private def column (values : Fin n → R) : Matrix (Fin n) (Fin 1) R :=
  Matrix.of (fun i _ => values i)

private def row (values : Fin n → R) : Matrix (Fin 1) (Fin n) R :=
  Matrix.of (fun _ i => values i)

private def scalar (value : R) : Matrix (Fin 1) (Fin 1) R :=
  Matrix.of (fun _ _ => value)

/-- Append one observed column and one observed row without changing their order. -/
def border (old : Matrix (Fin n) (Fin n) R) (right bottom : Fin n → R) (corner : R) :
    Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks old (column right) (row bottom) (scalar corner))

@[simp] theorem border_old_old (old : Matrix (Fin n) (Fin n) R) (right bottom : Fin n → R) (corner : R)
    (i j : Fin n) : border old right bottom corner i.castSucc j.castSucc = old i j := by
  simp only [border,Matrix.reindex_apply,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_castSucc,
    Matrix.fromBlocks_apply₁₁]

@[simp] theorem border_old_new (old : Matrix (Fin n) (Fin n) R) (right bottom : Fin n → R) (corner : R)
    (i : Fin n) : border old right bottom corner i.castSucc (Fin.last n) = right i := by
  simp only [border,Matrix.reindex_apply,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_castSucc,
    finSumFinEquiv_symm_last,Matrix.fromBlocks_apply₁₂,column,Matrix.of_apply]

@[simp] theorem border_new_old (old : Matrix (Fin n) (Fin n) R) (right bottom : Fin n → R) (corner : R)
    (j : Fin n) : border old right bottom corner (Fin.last n) j.castSucc = bottom j := by
  simp only [border,Matrix.reindex_apply,Matrix.submatrix_apply,finSumFinEquiv_symm_apply_castSucc,
    finSumFinEquiv_symm_last,Matrix.fromBlocks_apply₂₁,row,Matrix.of_apply]

@[simp] theorem border_new_new (old : Matrix (Fin n) (Fin n) R) (right bottom : Fin n → R) (corner : R) :
    border old right bottom corner (Fin.last n) (Fin.last n) = corner := by
  simp only [border,Matrix.reindex_apply,Matrix.submatrix_apply,finSumFinEquiv_symm_last,
    Matrix.fromBlocks_apply₂₂,scalar,Matrix.of_apply]

variable [CommRing R]
variable (old : Matrix (Fin n) (Fin n) R) [Invertible old]
variable (right bottom : Fin n → R) (corner : R)

/-- The old inverse computes the contribution of the new column in the last row. -/
def pivot : R := corner - dotProduct bottom ((⅟old) *ᵥ right)

private theorem schur_cell :
    (scalar corner - row bottom * (⅟old) * column right) 0 0 = pivot old right bottom corner := by
  rw [Matrix.mul_assoc]
  rfl

theorem border_det : (border old right bottom corner).det = old.det * pivot old right bottom corner := by
  unfold border
  rw [Matrix.det_reindex_self,Matrix.det_fromBlocks₁₁,Matrix.det_fin_one,schur_cell]

/-- The actual scalar unit and old inverse supply the new inverse via the existing block factorization. -/
@[instance_reducible]
def borderInverse (unitPivot : IsUnit (pivot old right bottom corner)) :
    Invertible (border old right bottom corner) := by
  let S := scalar corner - row bottom * (⅟old) * column right
  have unitDet : IsUnit S.det := by
    change IsUnit (scalar corner - row bottom * (⅟old) * column right).det
    rw [Matrix.det_fin_one,schur_cell]
    exact unitPivot
  letI : Invertible S := Matrix.invertibleOfIsUnitDet S unitDet
  letI := Matrix.fromBlocks₁₁Invertible old (column right) (row bottom) (scalar corner)
  exact Matrix.submatrixEquivInvertible
    (Matrix.fromBlocks old (column right) (row bottom) (scalar corner))
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- Columns of a square observation matrix in the existing Gram carrier. -/
def columns (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Coordinates (Fin n) :=
  WithLp.toLp 2 (fun i => A i j)

private theorem synthesis_vec (A : Matrix (Fin n) (Fin n) ℂ) (a : Coordinates (Fin n)) :
    (fun i => Projection.synthesis (columns A) a i) = A *ᵥ (fun j => a j) := by
  funext i
  change (∑ j, a j • columns A j) i = _
  simp only [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,columns,
    smul_eq_mul,Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem coefficients_from_inverse (A : Matrix (Fin n) (Fin n) ℂ) [Invertible A] (input : Fin n → ℂ) :
    Projection.coefficients (columns A) (WithLp.toLp 2 input) =
      WithLp.toLp 2 ((⅟A) *ᵥ input) := by
  let y : Coordinates (Fin n) := WithLp.toLp 2 input
  let x : Coordinates (Fin n) := WithLp.toLp 2 ((⅟A) *ᵥ input)
  have lifted : Projection.synthesis (columns A) x = y := by
    ext i
    have vector := congrFun (synthesis_vec A x) i
    change _ = (A *ᵥ (⅟A) *ᵥ input) i at vector
    rw [Matrix.mulVec_mulVec,mul_invOf_self,Matrix.one_mulVec] at vector
    exact vector
  have contains : y ∈ Projection.sourceSpan (columns A) := ⟨x,lifted⟩
  have projected : Projection.synthesis (columns A) (Projection.coefficients (columns A) y) = y := by
    rw [← Projection.predictable_source,Projection.predictable_readback,
      Submodule.starProjection_eq_self_iff.mpr contains]
  have equation : A *ᵥ (fun j => Projection.coefficients (columns A) y j) = input :=
    (synthesis_vec A (Projection.coefficients (columns A) y)).symm.trans
      (congrArg (fun values : Coordinates (Fin n) => fun j => values j) projected)
  have solution := congrArg (fun values : Fin n → ℂ => (⅟A) *ᵥ values) equation
  rw [Matrix.mulVec_mulVec,invOf_mul_self,Matrix.one_mulVec] at solution
  ext j
  exact congrFun solution j

end SourceGeneratedFiniteGram.MatrixBorder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
