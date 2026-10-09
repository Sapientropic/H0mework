import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNativeCurrentPilot
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNativeZeroCurrents
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

theorem actual_native_heavy_current_row12 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 12 j = primalCurrentPoint 12 j := by
  eval_bra_native_heavy_row 12

theorem actual_native_heavy_current_row13 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 13 j = primalCurrentPoint 13 j := by
  eval_bra_native_heavy_row 13

theorem actual_native_heavy_current_row14 (j : Fin 79) (_heavy : 48 ≤ j.val) :
    sparseCurrentPoint 14 j = primalCurrentPoint 14 j := by
  exact actual_native_zero_current_row14 j

theorem actual_native_heavy_current_row15 (j : Fin 79) (_heavy : 48 ≤ j.val) :
    sparseCurrentPoint 15 j = primalCurrentPoint 15 j := by
  exact actual_native_zero_current_row15 j

theorem actual_native_heavy_current_row16 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 16 j = primalCurrentPoint 16 j := by
  eval_bra_native_heavy_row 16

theorem actual_native_heavy_current_row17 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 17 j = primalCurrentPoint 17 j := by
  eval_bra_native_heavy_row 17

theorem actual_native_heavy_current_row18 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 18 j = primalCurrentPoint 18 j := by
  eval_bra_native_heavy_row 18

theorem actual_native_heavy_current_row19 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 19 j = primalCurrentPoint 19 j := by
  eval_bra_native_heavy_row 19

theorem actual_native_heavy_current_row20 (j : Fin 79) (_heavy : 48 ≤ j.val) :
    sparseCurrentPoint 20 j = primalCurrentPoint 20 j := by
  exact actual_native_zero_current_row20 j

theorem actual_native_heavy_current_row21 (j : Fin 79) (_heavy : 48 ≤ j.val) :
    sparseCurrentPoint 21 j = primalCurrentPoint 21 j := by
  exact actual_native_zero_current_row21 j

theorem actual_native_heavy_current_row22 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 22 j = primalCurrentPoint 22 j := by
  eval_bra_native_heavy_row 22

theorem actual_native_heavy_current_row23 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 23 j = primalCurrentPoint 23 j := by
  eval_bra_native_heavy_row 23

end LowEnergy.ActualCanonical79Imaginary
