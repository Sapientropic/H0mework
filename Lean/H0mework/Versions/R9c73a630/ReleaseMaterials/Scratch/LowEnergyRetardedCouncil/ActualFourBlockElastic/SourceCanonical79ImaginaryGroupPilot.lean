import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79DAGFoldContinuation
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
theorem actual_group1_point :
    (canonical_group% 1) Complex.I 0 = group1Value := by
  fold_canonical_group_continuation 1

theorem actual_group2_point :
    (canonical_group% 2) Complex.I 0 = group2Value := by
  fold_canonical_group_continuation 2

theorem actual_group3_point :
    (canonical_group% 3) Complex.I 0 = group3Value := by
  fold_canonical_group_continuation 3

end LowEnergy.ActualCanonical79Imaginary
