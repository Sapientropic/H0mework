import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDAGGroups2
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDAGTyped
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open LowEnergy.ActualCanonical79Imaginary

theorem actual_canonical_group14_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 14) x 0 i) z := by
  analytic_canonical_group_typed 14

theorem actual_canonical_group15_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 15) x 0 i) z := by
  analytic_canonical_group_typed 15

theorem actual_canonical_group16_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 16) x 0 i) z := by
  analytic_canonical_group_typed 16

theorem actual_canonical_group17_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 17) x 0 i) z := by
  analytic_canonical_group_typed 17

end LowEnergy.ActualFourBlockRealTransfer
