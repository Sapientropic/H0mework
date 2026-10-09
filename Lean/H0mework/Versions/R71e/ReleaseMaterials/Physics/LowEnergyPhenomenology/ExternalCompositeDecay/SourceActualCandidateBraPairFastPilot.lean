import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateBraPairFold
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCandidateBra
theorem actual_pair_row10_pilot (b : Fin 97) :
    leftRow10 (entryMatrix b) = pairRow10 b := by
  eval_bra_pair_row 10
end LowEnergy.ActualCandidateBra
