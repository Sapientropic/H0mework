import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairFold
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCandidateBra
theorem actual_pair_row9_pilot (b : Fin 97) :
    leftRow9 (entryMatrix b) = pairRow9 b := by
  eval_bra_pair_row 9
end LowEnergy.ActualCandidateBra
