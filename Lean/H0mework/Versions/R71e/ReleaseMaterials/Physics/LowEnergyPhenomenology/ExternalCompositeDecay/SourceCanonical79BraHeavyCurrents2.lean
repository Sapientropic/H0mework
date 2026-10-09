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

theorem actual_current_heavy_native61 (n : Fin 48) :
    sparseCurrentPoint 61 (nativeIndex79 n) = primalCurrentPoint 61 (nativeIndex79 n) := by
  eval_heavy_native_current 61
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy61 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 61 j = primalCurrentPoint 61 j := by
  eval_heavy_heavy_current 61
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row61 (j : Fin 79) :
    sparseCurrentPoint 61 j = primalCurrentPoint 61 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native61 n
  · exact actual_current_heavy_heavy61 j (Nat.le_of_not_gt h)

theorem actual_current_heavy_native63 (n : Fin 48) :
    sparseCurrentPoint 63 (nativeIndex79 n) = primalCurrentPoint 63 (nativeIndex79 n) := by
  eval_heavy_native_current 63
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy63 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 63 j = primalCurrentPoint 63 j := by
  eval_heavy_heavy_current 63
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row63 (j : Fin 79) :
    sparseCurrentPoint 63 j = primalCurrentPoint 63 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native63 n
  · exact actual_current_heavy_heavy63 j (Nat.le_of_not_gt h)

theorem actual_current_heavy_native64 (n : Fin 48) :
    sparseCurrentPoint 64 (nativeIndex79 n) = primalCurrentPoint 64 (nativeIndex79 n) := by
  eval_heavy_native_current 64
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy64 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 64 j = primalCurrentPoint 64 j := by
  eval_heavy_heavy_current 64
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row64 (j : Fin 79) :
    sparseCurrentPoint 64 j = primalCurrentPoint 64 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native64 n
  · exact actual_current_heavy_heavy64 j (Nat.le_of_not_gt h)

theorem actual_current_heavy_native66 (n : Fin 48) :
    sparseCurrentPoint 66 (nativeIndex79 n) = primalCurrentPoint 66 (nativeIndex79 n) := by
  eval_heavy_native_current 66
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy66 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 66 j = primalCurrentPoint 66 j := by
  eval_heavy_heavy_current 66
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row66 (j : Fin 79) :
    sparseCurrentPoint 66 j = primalCurrentPoint 66 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native66 n
  · exact actual_current_heavy_heavy66 j (Nat.le_of_not_gt h)

end LowEnergy.ActualCanonical79Imaginary
