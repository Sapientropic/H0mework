import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferDualSelector
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer

theorem actual_dual_read_row0 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 0 b = dualRead x r 0 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row1 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 1 b = dualRead x r 1 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row2 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 2 b = dualRead x r 2 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row3 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 3 b = dualRead x r 3 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row4 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 4 b = dualRead x r 4 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row5 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 5 b = dualRead x r 5 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row6 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 6 b = dualRead x r 6 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row7 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 7 b = dualRead x r 7 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row8 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 8 b = dualRead x r 8 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row9 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 9 b = dualRead x r 9 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row10 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 10 b = dualRead x r 10 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row11 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 11 b = dualRead x r 11 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row12 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 12 b = dualRead x r 12 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row13 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 13 b = dualRead x r 13 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row14 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 14 b = dualRead x r 14 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row15 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 15 b = dualRead x r 15 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row16 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 16 b = dualRead x r 16 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row17 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 17 b = dualRead x r 17 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row18 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 18 b = dualRead x r 18 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row19 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 19 b = dualRead x r 19 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row20 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 20 b = dualRead x r 20 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row21 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 21 b = dualRead x r 21 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row22 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 22 b = dualRead x r 22 b := by
  fin_cases b <;> rfl

theorem actual_dual_read_row23 (x r : ℂ) (b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r 23 b = dualRead x r 23 b := by
  fin_cases b <;> rfl

theorem actual_dual_read (x r : ℂ) (a b : Fin 24) :
    MixedSpectatorDual24Data.axialInverse x r a b = dualRead x r a b := by
  fin_cases a
  · exact actual_dual_read_row0 x r b
  · exact actual_dual_read_row1 x r b
  · exact actual_dual_read_row2 x r b
  · exact actual_dual_read_row3 x r b
  · exact actual_dual_read_row4 x r b
  · exact actual_dual_read_row5 x r b
  · exact actual_dual_read_row6 x r b
  · exact actual_dual_read_row7 x r b
  · exact actual_dual_read_row8 x r b
  · exact actual_dual_read_row9 x r b
  · exact actual_dual_read_row10 x r b
  · exact actual_dual_read_row11 x r b
  · exact actual_dual_read_row12 x r b
  · exact actual_dual_read_row13 x r b
  · exact actual_dual_read_row14 x r b
  · exact actual_dual_read_row15 x r b
  · exact actual_dual_read_row16 x r b
  · exact actual_dual_read_row17 x r b
  · exact actual_dual_read_row18 x r b
  · exact actual_dual_read_row19 x r b
  · exact actual_dual_read_row20 x r b
  · exact actual_dual_read_row21 x r b
  · exact actual_dual_read_row22 x r b
  · exact actual_dual_read_row23 x r b

end LowEnergy.ActualFourBlockRealTransfer
