import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDAGGroups3
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDAGSteps0
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDAGSteps1
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDAGSteps2
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDAGSteps3
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open LowEnergy.ActualCanonical79Imaginary

theorem actual_canonical_group18_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 18) x 0 i) z :=
  canonical_group18_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group4_analytic z)
    (actual_canonical_group16_analytic z)
    (actual_canonical_group17_analytic z)
    i

theorem actual_canonical_group19_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 19) x 0 i) z :=
  canonical_group19_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group4_analytic z)
    (actual_canonical_group5_analytic z)
    (actual_canonical_group9_analytic z)
    (actual_canonical_group14_analytic z)
    (actual_canonical_group18_analytic z)
    i

theorem actual_canonical_group20_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 20) x 0 i) z :=
  canonical_group20_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group4_analytic z)
    (actual_canonical_group14_analytic z)
    (actual_canonical_group19_analytic z)
    i

theorem actual_canonical_group21_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 21) x 0 i) z :=
  canonical_group21_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group4_analytic z)
    (actual_canonical_group9_analytic z)
    (actual_canonical_group13_analytic z)
    (actual_canonical_group14_analytic z)
    (actual_canonical_group15_analytic z)
    (actual_canonical_group16_analytic z)
    (actual_canonical_group19_analytic z)
    (actual_canonical_group20_analytic z)
    i

theorem actual_canonical_group22_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 22) x 0 i) z :=
  canonical_group22_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group4_analytic z)
    (actual_canonical_group9_analytic z)
    (actual_canonical_group13_analytic z)
    (actual_canonical_group14_analytic z)
    (actual_canonical_group16_analytic z)
    (actual_canonical_group17_analytic z)
    (actual_canonical_group19_analytic z)
    (actual_canonical_group21_analytic z)
    i

theorem actual_canonical_group23_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 23) x 0 i) z :=
  canonical_group23_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group9_analytic z)
    i

theorem actual_canonical_group24_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 24) x 0 i) z :=
  canonical_group24_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group4_analytic z)
    (actual_canonical_group21_analytic z)
    (actual_canonical_group23_analytic z)
    i

theorem actual_canonical_group25_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 25) x 0 i) z :=
  canonical_group25_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group4_analytic z)
    (actual_canonical_group13_analytic z)
    (actual_canonical_group14_analytic z)
    (actual_canonical_group15_analytic z)
    (actual_canonical_group20_analytic z)
    (actual_canonical_group24_analytic z)
    i

theorem actual_canonical_group26_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 26) x 0 i) z :=
  canonical_group26_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group4_analytic z)
    (actual_canonical_group11_analytic z)
    (actual_canonical_group25_analytic z)
    i

theorem actual_canonical_group27_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 27) x 0 i) z :=
  canonical_group27_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group4_analytic z)
    (actual_canonical_group9_analytic z)
    (actual_canonical_group11_analytic z)
    (actual_canonical_group13_analytic z)
    (actual_canonical_group14_analytic z)
    (actual_canonical_group20_analytic z)
    (actual_canonical_group21_analytic z)
    (actual_canonical_group25_analytic z)
    (actual_canonical_group26_analytic z)
    i

theorem actual_canonical_group28_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 28) x 0 i) z :=
  canonical_group28_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group4_analytic z)
    (actual_canonical_group9_analytic z)
    (actual_canonical_group21_analytic z)
    i

theorem actual_canonical_group29_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 29) x 0 i) z :=
  canonical_group29_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group14_analytic z)
    (actual_canonical_group21_analytic z)
    (actual_canonical_group28_analytic z)
    i

theorem actual_canonical_group30_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 30) x 0 i) z :=
  canonical_group30_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group14_analytic z)
    (actual_canonical_group21_analytic z)
    (actual_canonical_group28_analytic z)
    (actual_canonical_group29_analytic z)
    i

theorem actual_canonical_group31_analytic (z : ℂ) (i : Fin 128) :
    AnalyticAt ℂ (fun x => (canonical_group% 31) x 0 i) z :=
  canonical_group31_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group14_analytic z)
    (actual_canonical_group15_analytic z)
    (actual_canonical_group20_analytic z)
    (actual_canonical_group29_analytic z)
    (actual_canonical_group30_analytic z)
    i

theorem actual_canonical_group32_analytic (z : ℂ) (i : Fin 106) :
    AnalyticAt ℂ (fun x => (canonical_group% 32) x 0 i) z :=
  canonical_group32_step z
    (actual_canonical_group0_analytic z)
    (actual_canonical_group1_analytic z)
    (actual_canonical_group2_analytic z)
    (actual_canonical_group3_analytic z)
    (actual_canonical_group4_analytic z)
    (actual_canonical_group9_analytic z)
    (actual_canonical_group15_analytic z)
    (actual_canonical_group29_analytic z)
    (actual_canonical_group30_analytic z)
    (actual_canonical_group31_analytic z)
    i

end LowEnergy.ActualFourBlockRealTransfer
