import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraCurrentFastFold
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79NativeSourceRows
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79SourceSparseSums
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators

private theorem native_sparse_left (i : Fin 48) (j : Fin 79) :
    sparseCurrentPoint (nativeIndex79 i) j =
      ∑s : Fin 8,ActualCandidateBra.primalPairPoint (sourceIndex97 i) (sourceField j s) *
        sourceWeight (sourcePolynomialPoint false) j s := by
  have h :
      (∑a : Fin 97,∑b : Fin 97,sourceMapPoint true (nativeIndex79 i) a *
        ActualCandidateBra.primalPairPoint a b * sourceMapPoint false j b) =
      sparseCurrentPoint (nativeIndex79 i) j := by
    simp only [sourceMapPoint,actual_source_sparse_rows]
    exact source_sparse_pair (sourcePolynomialPoint true) (sourcePolynomialPoint false)
      (nativeIndex79 i) j ActualCandidateBra.primalPairPoint
  exact h.symm.trans (raw_current_native_left_sparse ActualCandidateBra.primalPairPoint
    true false i j)

theorem actual_native_zero_current_row8 (j : Fin 79) :
    sparseCurrentPoint 8 j = primalCurrentPoint 8 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (8 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 8 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (8 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

theorem actual_native_zero_current_row9 (j : Fin 79) :
    sparseCurrentPoint 9 j = primalCurrentPoint 9 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (9 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 9 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (9 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

theorem actual_native_zero_current_row14 (j : Fin 79) :
    sparseCurrentPoint 14 j = primalCurrentPoint 14 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (14 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 14 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (14 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

theorem actual_native_zero_current_row15 (j : Fin 79) :
    sparseCurrentPoint 15 j = primalCurrentPoint 15 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (15 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 15 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (15 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

theorem actual_native_zero_current_row20 (j : Fin 79) :
    sparseCurrentPoint 20 j = primalCurrentPoint 20 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (20 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 20 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (20 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

theorem actual_native_zero_current_row21 (j : Fin 79) :
    sparseCurrentPoint 21 j = primalCurrentPoint 21 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (21 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 21 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (21 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

theorem actual_native_zero_current_row26 (j : Fin 79) :
    sparseCurrentPoint 26 j = primalCurrentPoint 26 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (26 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 26 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (26 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

theorem actual_native_zero_current_row27 (j : Fin 79) :
    sparseCurrentPoint 27 j = primalCurrentPoint 27 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (27 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 27 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (27 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

theorem actual_native_zero_current_row32 (j : Fin 79) :
    sparseCurrentPoint 32 j = primalCurrentPoint 32 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (32 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 32 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (32 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

theorem actual_native_zero_current_row33 (j : Fin 79) :
    sparseCurrentPoint 33 j = primalCurrentPoint 33 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (33 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 33 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (33 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

theorem actual_native_zero_current_row44 (j : Fin 79) :
    sparseCurrentPoint 44 j = primalCurrentPoint 44 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (44 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 44 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (44 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

theorem actual_native_zero_current_row45 (j : Fin 79) :
    sparseCurrentPoint 45 j = primalCurrentPoint 45 j := by
  have hM : ActualCandidateBra.primalPairPoint (sourceIndex97 (45 : Fin 48)) =
      (fun _ : Fin 97 => (0 : ℂ)) := by
    funext b
    rfl
  have hR : primalCurrentPoint 45 j = 0 := by rfl
  change sparseCurrentPoint (nativeIndex79 (45 : Fin 48)) j = _
  rw [native_sparse_left,hM,hR]
  simp only [zero_mul,Finset.sum_const_zero]

end LowEnergy.ActualCanonical79Imaginary
