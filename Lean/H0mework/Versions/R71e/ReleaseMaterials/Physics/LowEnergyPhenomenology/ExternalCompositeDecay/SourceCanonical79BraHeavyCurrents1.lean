import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraHeavyCurrentPilot
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraHeavyDeltaPilot
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraCurrentRadicalPowers
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraHeavyZeroCurrents
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
attribute [local irreducible] ActualCandidateBra.primalPairPoint sourceField sourceWeight

theorem actual_current_heavy_native55 (n : Fin 48) :
    sparseCurrentPoint 55 (nativeIndex79 n) = primalCurrentPoint 55 (nativeIndex79 n) := by
  eval_heavy_native_current 55
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy55 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 55 j = primalCurrentPoint 55 j := by
  eval_heavy_heavy_current 55
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row55 (j : Fin 79) :
    sparseCurrentPoint 55 j = primalCurrentPoint 55 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native55 n
  · exact actual_current_heavy_heavy55 j (Nat.le_of_not_gt h)

theorem actual_current_heavy_native56 (n : Fin 48) :
    sparseCurrentPoint 56 (nativeIndex79 n) = primalCurrentPoint 56 (nativeIndex79 n) := by
  eval_heavy_native_current 56
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy56 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 56 j = primalCurrentPoint 56 j := by
  eval_heavy_heavy_current 56
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row56 (j : Fin 79) :
    sparseCurrentPoint 56 j = primalCurrentPoint 56 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native56 n
  · exact actual_current_heavy_heavy56 j (Nat.le_of_not_gt h)

theorem actual_current_heavy_native57 (n : Fin 48) :
    sparseCurrentPoint 57 (nativeIndex79 n) = primalCurrentPoint 57 (nativeIndex79 n) := by
  eval_heavy_native_current 57
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy57 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 57 j = primalCurrentPoint 57 j := by
  eval_heavy_heavy_current 57
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row57 (j : Fin 79) :
    sparseCurrentPoint 57 j = primalCurrentPoint 57 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native57 n
  · exact actual_current_heavy_heavy57 j (Nat.le_of_not_gt h)

theorem actual_current_heavy_native58 (n : Fin 48) :
    sparseCurrentPoint 58 (nativeIndex79 n) = primalCurrentPoint 58 (nativeIndex79 n) := by
  eval_heavy_native_current 58
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy58 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 58 j = primalCurrentPoint 58 j := by
  eval_heavy_heavy_current 58
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row58 (j : Fin 79) :
    sparseCurrentPoint 58 j = primalCurrentPoint 58 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native58 n
  · exact actual_current_heavy_heavy58 j (Nat.le_of_not_gt h)

theorem actual_current_heavy_native60 (n : Fin 48) :
    sparseCurrentPoint 60 (nativeIndex79 n) = primalCurrentPoint 60 (nativeIndex79 n) := by
  eval_heavy_native_current 60
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy60 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 60 j = primalCurrentPoint 60 j := by
  eval_heavy_heavy_current 60
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row60 (j : Fin 79) :
    sparseCurrentPoint 60 j = primalCurrentPoint 60 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native60 n
  · exact actual_current_heavy_heavy60 j (Nat.le_of_not_gt h)

end LowEnergy.ActualCanonical79Imaginary
