import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDAGStep
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open LowEnergy.ActualCanonical79Imaginary

theorem canonical_group26_step (z : ℂ)
    (ih0 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 j) z)
    (ih1 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 j) z)
    (ih2 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 j) z)
    (ih3 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 j) z)
    (ih4 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 4) x 0 j) z)
    (ih11 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 11) x 0 j) z)
    (ih25 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 25) x 0 j) z)
    (i : Fin 128) : AnalyticAt ℂ (fun x => (canonical_group% 26) x 0 i) z := by
  analytic_canonical_group_step 26

theorem canonical_group27_step (z : ℂ)
    (ih0 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 j) z)
    (ih1 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 j) z)
    (ih2 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 j) z)
    (ih3 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 j) z)
    (ih4 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 4) x 0 j) z)
    (ih9 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 9) x 0 j) z)
    (ih11 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 11) x 0 j) z)
    (ih13 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 13) x 0 j) z)
    (ih14 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 14) x 0 j) z)
    (ih20 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 20) x 0 j) z)
    (ih21 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 21) x 0 j) z)
    (ih25 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 25) x 0 j) z)
    (ih26 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 26) x 0 j) z)
    (i : Fin 128) : AnalyticAt ℂ (fun x => (canonical_group% 27) x 0 i) z := by
  analytic_canonical_group_step 27

theorem canonical_group28_step (z : ℂ)
    (ih0 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 j) z)
    (ih1 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 j) z)
    (ih3 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 j) z)
    (ih4 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 4) x 0 j) z)
    (ih9 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 9) x 0 j) z)
    (ih21 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 21) x 0 j) z)
    (i : Fin 128) : AnalyticAt ℂ (fun x => (canonical_group% 28) x 0 i) z := by
  analytic_canonical_group_step 28

theorem canonical_group29_step (z : ℂ)
    (ih0 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 j) z)
    (ih1 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 j) z)
    (ih2 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 j) z)
    (ih3 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 j) z)
    (ih14 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 14) x 0 j) z)
    (ih21 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 21) x 0 j) z)
    (ih28 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 28) x 0 j) z)
    (i : Fin 128) : AnalyticAt ℂ (fun x => (canonical_group% 29) x 0 i) z := by
  analytic_canonical_group_step 29

end LowEnergy.ActualFourBlockRealTransfer
