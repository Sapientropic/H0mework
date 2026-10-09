import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Independent
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open InnerProductSpace
open scoped BigOperators ComplexOrder Matrix

def rawFields (centre : Point) (n : Nat) (i : Fin n) : SpatialLp :=
  orbitalField centre i.val 0

def normalizedField (centre : Point) (n : Nat) (i : Fin n) : SpatialLp :=
  gramSchmidtNormed ℂ (rawFields centre n) i

def rawGram (centre : Point) (n : Nat) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.gram ℂ (rawFields centre n)

def crossGram (centre : Point) (n : Nat) : Matrix (Fin n) (Fin n) ℂ :=
  fun j i => inner ℂ (rawFields centre n j) (normalizedField centre n i)

def coefficients (centre : Point) (n : Nat) : Matrix (Fin n) (Fin n) ℂ :=
  (rawGram centre n)⁻¹ * crossGram centre n

theorem rawGram_isUnit (centre : Point) (n : Nat) : IsUnit (rawGram centre n) :=
  (Matrix.posDef_gram_iff_linearIndependent.mpr (orbitals_independent centre n)).isUnit

theorem normalized_orthonormal (centre : Point) (n : Nat) :
    Orthonormal ℂ (normalizedField centre n) :=
  gramSchmidtNormed_orthonormal (orbitals_independent centre n)

theorem normalized_mem_span (centre : Point) (n : Nat) (i : Fin n) :
    normalizedField centre n i ∈ Submodule.span ℂ (Set.range (rawFields centre n)) := by
  have member : normalizedField centre n i ∈ Submodule.span ℂ (Set.range (normalizedField centre n)) :=
    Submodule.subset_span (Set.mem_range_self i)
  have spanEqual : Submodule.span ℂ (Set.range (normalizedField centre n)) =
      Submodule.span ℂ (Set.range (rawFields centre n)) :=
    (span_gramSchmidtNormed_range (𝕜 := ℂ) (rawFields centre n)).trans (span_gramSchmidt ℂ (rawFields centre n))
  rw [spanEqual] at member
  exact member

theorem normalized_synthesis (centre : Point) (n : Nat) (i : Fin n) :
    normalizedField centre n i = ∑ j : Fin n, coefficients centre n j i • rawFields centre n j := by
  classical
  obtain ⟨coordinate,represented⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (normalized_mem_span centre n i)
  have cross (j : Fin n) : crossGram centre n j i = (rawGram centre n *ᵥ coordinate) j := by
    change inner ℂ (rawFields centre n j) (normalizedField centre n i) = _
    rw [← represented]
    simp [rawGram,Matrix.mulVec,dotProduct,inner_sum,inner_smul_right,mul_comm]
  have unitDet : IsUnit (rawGram centre n).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (rawGram_isUnit centre n)
  have coordinateEqual : (fun j => coefficients centre n j i) = coordinate := by
    calc
      _ = (rawGram centre n)⁻¹ *ᵥ (rawGram centre n *ᵥ coordinate) := by
        funext j
        simp only [coefficients,Matrix.mul_apply,cross,Matrix.mulVec,dotProduct]
      _ = coordinate := by
        rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ unitDet,Matrix.one_mulVec]
  symm
  calc
    _ = ∑ j : Fin n, coordinate j • rawFields centre n j :=
      Finset.sum_congr rfl (fun j _ => congrArg (fun a => a • rawFields centre n j) (congrFun coordinateEqual j))
    _ = normalizedField centre n i := represented

theorem normalized_gram (centre : Point) (n : Nat) :
    (coefficients centre n).conjTranspose * rawGram centre n * coefficients centre n = 1 := by
  classical
  have gramIdentity : (coefficients centre n).conjTranspose * rawGram centre n * coefficients centre n =
      Matrix.gram ℂ (normalizedField centre n) := by
    rw [Matrix.mul_assoc]
    ext i j
    change (star (fun k => coefficients centre n k i)) ⬝ᵥ
        (Matrix.gram ℂ (rawFields centre n) *ᵥ (fun k => coefficients centre n k j)) =
      inner ℂ (normalizedField centre n i) (normalizedField centre n j)
    rw [Matrix.star_dotProduct_gram_mulVec]
    rw [← normalized_synthesis centre n i,← normalized_synthesis centre n j]
  exact gramIdentity.trans (Matrix.gram_eq_one_iff_orthonormal.mpr (normalized_orthonormal centre n))

end
end CPS1ElectronicSource
