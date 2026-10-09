import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraHeavyCurrentPilot
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraHeavyDeltaPilot
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraCurrentRadicalPowers
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraHeavyZeroCurrents
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
attribute [local irreducible] ActualCandidateBra.primalPairPoint sourceField sourceWeight

theorem actual_current_heavy_native50 (n : Fin 48) :
    sparseCurrentPoint 50 (nativeIndex79 n) = primalCurrentPoint 50 (nativeIndex79 n) := by
  eval_heavy_native_current 50
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy50 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 50 j = primalCurrentPoint 50 j := by
  eval_heavy_heavy_current 50
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row50 (j : Fin 79) :
    sparseCurrentPoint 50 j = primalCurrentPoint 50 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native50 n
  · exact actual_current_heavy_heavy50 j (Nat.le_of_not_gt h)

theorem actual_current_heavy_native51 (n : Fin 48) :
    sparseCurrentPoint 51 (nativeIndex79 n) = primalCurrentPoint 51 (nativeIndex79 n) := by
  eval_heavy_native_current 51
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy51 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 51 j = primalCurrentPoint 51 j := by
  eval_heavy_heavy_current 51
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row51 (j : Fin 79) :
    sparseCurrentPoint 51 j = primalCurrentPoint 51 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native51 n
  · exact actual_current_heavy_heavy51 j (Nat.le_of_not_gt h)

theorem actual_current_heavy_native53 (n : Fin 48) :
    sparseCurrentPoint 53 (nativeIndex79 n) = primalCurrentPoint 53 (nativeIndex79 n) := by
  eval_heavy_native_current 53
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy53 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 53 j = primalCurrentPoint 53 j := by
  eval_heavy_heavy_current 53
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row53 (j : Fin 79) :
    sparseCurrentPoint 53 j = primalCurrentPoint 53 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native53 n
  · exact actual_current_heavy_heavy53 j (Nat.le_of_not_gt h)

theorem actual_current_heavy_native54 (n : Fin 48) :
    sparseCurrentPoint 54 (nativeIndex79 n) = primalCurrentPoint 54 (nativeIndex79 n) := by
  eval_heavy_native_current 54
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy54 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 54 j = primalCurrentPoint 54 j := by
  eval_heavy_heavy_current 54
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row54 (j : Fin 79) :
    sparseCurrentPoint 54 j = primalCurrentPoint 54 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native54 n
  · exact actual_current_heavy_heavy54 j (Nat.le_of_not_gt h)

end LowEnergy.ActualCanonical79Imaginary
