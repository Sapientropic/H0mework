import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDAGPrefix
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDAGTyped
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open LowEnergy.ActualCanonical79Imaginary

theorem actual_canonical_group9_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 9) x 0 i) z := by
  analytic_canonical_group_typed 9

end LowEnergy.ActualFourBlockRealTransfer
