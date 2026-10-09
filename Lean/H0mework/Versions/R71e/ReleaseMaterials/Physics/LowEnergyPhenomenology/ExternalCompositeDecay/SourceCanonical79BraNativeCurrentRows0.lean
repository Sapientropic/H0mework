import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNativeCurrentPilot
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNativeZeroCurrents
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

theorem actual_native_heavy_current_row1 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 1 j = primalCurrentPoint 1 j := by
  eval_bra_native_heavy_row 1

theorem actual_native_heavy_current_row2 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 2 j = primalCurrentPoint 2 j := by
  eval_bra_native_heavy_row 2

theorem actual_native_heavy_current_row3 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 3 j = primalCurrentPoint 3 j := by
  eval_bra_native_heavy_row 3

theorem actual_native_heavy_current_row4 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 4 j = primalCurrentPoint 4 j := by
  eval_bra_native_heavy_row 4

theorem actual_native_heavy_current_row5 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 5 j = primalCurrentPoint 5 j := by
  eval_bra_native_heavy_row 5

theorem actual_native_heavy_current_row7 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 7 j = primalCurrentPoint 7 j := by
  eval_bra_native_heavy_row 7

theorem actual_native_heavy_current_row8 (j : Fin 79) (_heavy : 48 ≤ j.val) :
    sparseCurrentPoint 8 j = primalCurrentPoint 8 j := by
  exact actual_native_zero_current_row8 j

theorem actual_native_heavy_current_row9 (j : Fin 79) (_heavy : 48 ≤ j.val) :
    sparseCurrentPoint 9 j = primalCurrentPoint 9 j := by
  exact actual_native_zero_current_row9 j

theorem actual_native_heavy_current_row10 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 10 j = primalCurrentPoint 10 j := by
  eval_bra_native_heavy_row 10

theorem actual_native_heavy_current_row11 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 11 j = primalCurrentPoint 11 j := by
  eval_bra_native_heavy_row 11

end LowEnergy.ActualCanonical79Imaginary
