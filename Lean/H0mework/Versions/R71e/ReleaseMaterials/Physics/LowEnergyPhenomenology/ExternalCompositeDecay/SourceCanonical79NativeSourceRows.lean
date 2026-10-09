import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79SourceSparseRows
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators

def nativeIndex79 (i : Fin 48) : Fin 79 := ⟨i.val, by omega⟩
def sourceIndex97 (i : Fin 48) : Fin 97 := ⟨i.val + 9, by omega⟩

private theorem weights_native (v : Fin 16 → ℂ) (i : Fin 48) (s : Fin 8) :
    sourceWeight v (nativeIndex79 i) s = if s = 0 then v 0 else 0 := by
  fin_cases i <;> fin_cases s <;> rfl

private theorem field_native (i : Fin 48) :
    sourceField (nativeIndex79 i) 0 = sourceIndex97 i := by
  fin_cases i <;> rfl

private theorem polynomial_zero (negative : Bool) :
    sourcePolynomialPoint negative 0 = 1 := by cases negative <;> rfl

/-- The first 48 original source rows select fields 9 through 56, on both
frequency branches. -/
theorem actual_source_native_row (negative : Bool) (i : Fin 48) (a : Fin 97) :
    sourceMapPoint negative (nativeIndex79 i) a =
      if a = sourceIndex97 i then 1 else 0 := by
  unfold sourceMapPoint
  rw [actual_source_sparse_rows]
  unfold sourceSparseRow
  simp_rw [weights_native,polynomial_zero]
  have h (s : Fin 8) :
      (if sourceField (nativeIndex79 i) s = a then
        (if s = 0 then (1 : ℂ) else 0) else 0) =
      if s = 0 then (if sourceIndex97 i = a then 1 else 0) else 0 := by
    by_cases hs : s = 0
    · subst s
      simp [field_native]
    · simp [hs]
  simp_rw [h]
  simp [eq_comm]

/-- Read an arbitrary original source row before expanding its eight-slot
representation. -/
theorem source_point_right_read (negative : Bool) (j : Fin 79) (f : Fin 97 → ℂ) :
    (∑b : Fin 97,f b * sourceMapPoint negative j b) =
      ∑s : Fin 8,f (sourceField j s) * sourceWeight (sourcePolynomialPoint negative) j s := by
  unfold sourceMapPoint
  simp_rw [actual_source_sparse_rows]
  unfold sourceSparseRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp [mul_ite,eq_comm]

theorem raw_current_native_left (M : Matrix (Fin 97) (Fin 97) ℂ)
    (negativeL negativeR : Bool) (i : Fin 48) (j : Fin 79) :
    (∑a : Fin 97,∑b : Fin 97,
      sourceMapPoint negativeL (nativeIndex79 i) a * M a b *
        sourceMapPoint negativeR j b) =
      ∑b : Fin 97,M (sourceIndex97 i) b * sourceMapPoint negativeR j b := by
  simp_rw [actual_source_native_row]
  simp [ite_mul,Finset.sum_ite_eq']

theorem raw_current_native_right (M : Matrix (Fin 97) (Fin 97) ℂ)
    (negativeL negativeR : Bool) (i : Fin 79) (j : Fin 48) :
    (∑a : Fin 97,∑b : Fin 97,
      sourceMapPoint negativeL i a * M a b *
        sourceMapPoint negativeR (nativeIndex79 j) b) =
      ∑a : Fin 97,sourceMapPoint negativeL i a * M a (sourceIndex97 j) := by
  simp_rw [actual_source_native_row]
  simp [mul_ite]

theorem raw_current_native_both (M : Matrix (Fin 97) (Fin 97) ℂ)
    (negativeL negativeR : Bool) (i j : Fin 48) :
    (∑a : Fin 97,∑b : Fin 97,
      sourceMapPoint negativeL (nativeIndex79 i) a * M a b *
        sourceMapPoint negativeR (nativeIndex79 j) b) =
      M (sourceIndex97 i) (sourceIndex97 j) := by
  rw [raw_current_native_left]
  simp_rw [actual_source_native_row]
  simp [mul_ite]

theorem raw_current_native_left_sparse (M : Matrix (Fin 97) (Fin 97) ℂ)
    (negativeL negativeR : Bool) (i : Fin 48) (j : Fin 79) :
    (∑a : Fin 97,∑b : Fin 97,
      sourceMapPoint negativeL (nativeIndex79 i) a * M a b *
        sourceMapPoint negativeR j b) =
      ∑s : Fin 8,M (sourceIndex97 i) (sourceField j s) *
        sourceWeight (sourcePolynomialPoint negativeR) j s := by
  rw [raw_current_native_left,source_point_right_read]

end LowEnergy.ActualCanonical79Imaginary
