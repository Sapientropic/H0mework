import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDAGGroups1
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDAGTyped
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open LowEnergy.ActualCanonical79Imaginary

theorem actual_canonical_group10_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 10) x 0 i) z := by
  analytic_canonical_group_typed 10

theorem actual_canonical_group11_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 11) x 0 i) z := by
  analytic_canonical_group_typed 11

theorem actual_canonical_group12_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 12) x 0 i) z := by
  analytic_canonical_group_typed 12

theorem actual_canonical_group13_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 13) x 0 i) z := by
  analytic_canonical_group_typed 13

end LowEnergy.ActualFourBlockRealTransfer
