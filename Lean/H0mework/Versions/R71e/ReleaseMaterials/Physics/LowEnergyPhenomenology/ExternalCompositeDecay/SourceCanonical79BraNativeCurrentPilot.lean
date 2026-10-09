import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNativeCurrentFold
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

theorem actual_native_heavy_current_row0 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 0 j = primalCurrentPoint 0 j := by
  eval_bra_native_heavy_row 0

theorem actual_native_heavy_current_row6 (j : Fin 79) (heavy : 48 ≤ j.val) :
    sparseCurrentPoint 6 j = primalCurrentPoint 6 j := by
  eval_bra_native_heavy_row 6

end LowEnergy.ActualCanonical79Imaginary
