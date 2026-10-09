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

theorem actual_current_heavy_native73 (n : Fin 48) :
    sparseCurrentPoint 73 (nativeIndex79 n) = primalCurrentPoint 73 (nativeIndex79 n) := by
  eval_heavy_native_current 73
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy73 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 73 j = primalCurrentPoint 73 j := by
  eval_heavy_heavy_current 73
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row73 (j : Fin 79) :
    sparseCurrentPoint 73 j = primalCurrentPoint 73 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native73 n
  · exact actual_current_heavy_heavy73 j (Nat.le_of_not_gt h)

theorem actual_current_heavy_native77 (n : Fin 48) :
    sparseCurrentPoint 77 (nativeIndex79 n) = primalCurrentPoint 77 (nativeIndex79 n) := by
  eval_heavy_native_current 77
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_heavy_heavy77 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 77 j = primalCurrentPoint 77 j := by
  eval_heavy_heavy_current 77
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf!
  all_goals try erw [current_sqrt2_cube]
  all_goals try erw [current_sqrt15_cube]
  all_goals try erw [Complex.I_sq]
  all_goals try erw [ActualCandidateBra.sqrt2_square]
  all_goals try erw [ActualCandidateBra.sqrt15_square]
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring!

theorem actual_current_row77 (j : Fin 79) :
    sparseCurrentPoint 77 j = primalCurrentPoint 77 j := by
  by_cases h : j.val < 48
  · let n : Fin 48 := ⟨j.val,h⟩
    have hn : nativeIndex79 n = j := by apply Fin.ext; rfl
    rw [← hn]
    exact actual_current_heavy_native77 n
  · exact actual_current_heavy_heavy77 j (Nat.le_of_not_gt h)

end LowEnergy.ActualCanonical79Imaginary
