import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDAGPilot
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDAGStructural
set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open LowEnergy.ActualCanonical79Imaginary

theorem actual_canonical_group2_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 i) z := by
  analytic_canonical_group_structural 2

theorem actual_canonical_group3_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 i) z := by
  analytic_canonical_group_structural 3

theorem actual_canonical_group4_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 4) x 0 i) z := by
  analytic_canonical_group_structural 4

theorem actual_canonical_group5_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 5) x 0 i) z := by
  analytic_canonical_group_structural 5

end LowEnergy.ActualFourBlockRealTransfer
