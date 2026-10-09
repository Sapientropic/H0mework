import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDAG
set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open LowEnergy.ActualCanonical79Imaginary

theorem actual_canonical_group0_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 i) z := by
  analytic_canonical_group 0

theorem actual_canonical_group1_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 i) z := by
  analytic_canonical_group 1

end LowEnergy.ActualFourBlockRealTransfer
