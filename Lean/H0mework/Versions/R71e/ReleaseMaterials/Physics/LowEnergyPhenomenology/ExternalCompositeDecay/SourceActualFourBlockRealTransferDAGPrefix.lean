import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDAGGroups0
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDAGStructural
set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open LowEnergy.ActualCanonical79Imaginary

theorem actual_canonical_group6_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 6) x 0 i) z := by
  analytic_canonical_group_structural 6

theorem actual_canonical_group7_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 7) x 0 i) z := by
  analytic_canonical_group_structural 7

theorem actual_canonical_group8_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 8) x 0 i) z := by
  analytic_canonical_group_structural 8

end LowEnergy.ActualFourBlockRealTransfer
