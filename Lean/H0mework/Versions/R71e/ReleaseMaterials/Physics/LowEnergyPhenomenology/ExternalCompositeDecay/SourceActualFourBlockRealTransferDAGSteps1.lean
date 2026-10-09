import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferDAGStep
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open LowEnergy.ActualCanonical79Imaginary

theorem canonical_group22_step (z : ℂ)
    (ih0 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 j) z)
    (ih1 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 j) z)
    (ih2 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 j) z)
    (ih3 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 j) z)
    (ih4 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 4) x 0 j) z)
    (ih9 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 9) x 0 j) z)
    (ih13 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 13) x 0 j) z)
    (ih14 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 14) x 0 j) z)
    (ih16 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 16) x 0 j) z)
    (ih17 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 17) x 0 j) z)
    (ih19 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 19) x 0 j) z)
    (ih21 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 21) x 0 j) z)
    (i : Fin 128) : AnalyticAt ℂ (fun x => (canonical_group% 22) x 0 i) z := by
  analytic_canonical_group_step 22

theorem canonical_group23_step (z : ℂ)
    (ih0 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 j) z)
    (ih1 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 j) z)
    (ih2 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 j) z)
    (ih3 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 j) z)
    (ih9 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 9) x 0 j) z)
    (i : Fin 128) : AnalyticAt ℂ (fun x => (canonical_group% 23) x 0 i) z := by
  analytic_canonical_group_step 23

theorem canonical_group24_step (z : ℂ)
    (ih0 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 j) z)
    (ih1 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 j) z)
    (ih2 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 j) z)
    (ih3 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 j) z)
    (ih4 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 4) x 0 j) z)
    (ih21 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 21) x 0 j) z)
    (ih23 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 23) x 0 j) z)
    (i : Fin 128) : AnalyticAt ℂ (fun x => (canonical_group% 24) x 0 i) z := by
  analytic_canonical_group_step 24

theorem canonical_group25_step (z : ℂ)
    (ih0 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 j) z)
    (ih1 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 j) z)
    (ih2 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 j) z)
    (ih3 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 j) z)
    (ih4 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 4) x 0 j) z)
    (ih13 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 13) x 0 j) z)
    (ih14 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 14) x 0 j) z)
    (ih15 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 15) x 0 j) z)
    (ih20 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 20) x 0 j) z)
    (ih24 : ∀j : Fin 128,AnalyticAt ℂ (fun x => (canonical_group% 24) x 0 j) z)
    (i : Fin 128) : AnalyticAt ℂ (fun x => (canonical_group% 25) x 0 i) z := by
  analytic_canonical_group_step 25

end LowEnergy.ActualFourBlockRealTransfer
