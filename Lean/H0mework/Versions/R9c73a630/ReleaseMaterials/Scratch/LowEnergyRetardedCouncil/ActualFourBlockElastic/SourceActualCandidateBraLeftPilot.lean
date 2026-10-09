import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraLeftFold
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCandidateBra
open ActualCandidateVertexEntries

theorem actual_left9 (B : Matrix Support Support ℂ) :
    tensor (fun i j => (source_vertex_row% 9) i.1 j.1 i.2 j.2) B = leftRow9 B := by
  eval_bra_left 9

end LowEnergy.ActualCandidateBra
