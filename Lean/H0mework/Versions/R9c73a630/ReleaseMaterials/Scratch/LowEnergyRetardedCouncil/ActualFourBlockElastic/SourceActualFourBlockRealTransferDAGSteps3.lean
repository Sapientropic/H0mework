import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDAGStep
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open LowEnergy.ActualCanonical79Imaginary

theorem canonical_group30_step (z : ℂ)
    (ih0 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 j) z)
    (ih1 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 j) z)
    (ih2 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 j) z)
    (ih3 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 j) z)
    (ih14 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 14) x 0 j) z)
    (ih21 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 21) x 0 j) z)
    (ih28 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 28) x 0 j) z)
    (ih29 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 29) x 0 j) z)
    (i : Fin 128) : AnalyticAt ℂ (fun x => (canonical_group% 30) x 0 i) z := by
  analytic_canonical_group_step 30

theorem canonical_group31_step (z : ℂ)
    (ih0 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 j) z)
    (ih1 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 j) z)
    (ih2 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 j) z)
    (ih3 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 j) z)
    (ih14 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 14) x 0 j) z)
    (ih15 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 15) x 0 j) z)
    (ih20 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 20) x 0 j) z)
    (ih29 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 29) x 0 j) z)
    (ih30 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 30) x 0 j) z)
    (i : Fin 128) : AnalyticAt ℂ (fun x => (canonical_group% 31) x 0 i) z := by
  analytic_canonical_group_step 31

theorem canonical_group32_step (z : ℂ)
    (ih0 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 j) z)
    (ih1 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 j) z)
    (ih2 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 j) z)
    (ih3 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 j) z)
    (ih4 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 4) x 0 j) z)
    (ih9 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 9) x 0 j) z)
    (ih15 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 15) x 0 j) z)
    (ih29 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 29) x 0 j) z)
    (ih30 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 30) x 0 j) z)
    (ih31 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 31) x 0 j) z)
    (i : Fin 106) : AnalyticAt ℂ (fun x => (canonical_group% 32) x 0 i) z := by
  analytic_canonical_group_step 32

end LowEnergy.ActualFourBlockRealTransfer
