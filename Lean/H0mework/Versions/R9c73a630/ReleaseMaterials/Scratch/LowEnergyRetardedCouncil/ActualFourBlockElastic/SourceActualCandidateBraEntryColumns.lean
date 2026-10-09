import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateVertexRows
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraColumns
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualCandidateBra

theorem actual_entry_column0 (a : Fin 97) :
    entryMatrix a (0,0) (0,0) = column0 a := by
  change vertexRow a 0 0 0 0 = column0 a
  rw [←actual_primal_row, actual_column0]

theorem actual_entry_column1 (a : Fin 97) :
    entryMatrix a (0,0) (0,1) = column1 a := by
  change vertexRow a 0 0 0 1 = column1 a
  rw [←actual_primal_row, actual_column1]

theorem actual_entry_column2 (a : Fin 97) :
    entryMatrix a (0,0) (0,2) = column2 a := by
  change vertexRow a 0 0 0 2 = column2 a
  rw [←actual_primal_row, actual_column2]

theorem actual_entry_column3 (a : Fin 97) :
    entryMatrix a (0,0) (1,0) = column3 a := by
  change vertexRow a 0 1 0 0 = column3 a
  rw [←actual_primal_row, actual_column3]

theorem actual_entry_column4 (a : Fin 97) :
    entryMatrix a (0,0) (1,1) = column4 a := by
  change vertexRow a 0 1 0 1 = column4 a
  rw [←actual_primal_row, actual_column4]

theorem actual_entry_column5 (a : Fin 97) :
    entryMatrix a (0,0) (2,0) = column5 a := by
  change vertexRow a 0 2 0 0 = column5 a
  rw [←actual_primal_row, actual_column5]

theorem actual_entry_column6 (a : Fin 97) :
    entryMatrix a (0,0) (2,2) = column6 a := by
  change vertexRow a 0 2 0 2 = column6 a
  rw [←actual_primal_row, actual_column6]

theorem actual_entry_column7 (a : Fin 97) :
    entryMatrix a (1,1) (0,0) = column7 a := by
  change vertexRow a 1 0 1 0 = column7 a
  rw [←actual_primal_row, actual_column7]

theorem actual_entry_column8 (a : Fin 97) :
    entryMatrix a (1,1) (0,1) = column8 a := by
  change vertexRow a 1 0 1 1 = column8 a
  rw [←actual_primal_row, actual_column8]

theorem actual_entry_column9 (a : Fin 97) :
    entryMatrix a (1,1) (0,2) = column9 a := by
  change vertexRow a 1 0 1 2 = column9 a
  rw [←actual_primal_row, actual_column9]

theorem actual_entry_column10 (a : Fin 97) :
    entryMatrix a (1,1) (1,0) = column10 a := by
  change vertexRow a 1 1 1 0 = column10 a
  rw [←actual_primal_row, actual_column10]

theorem actual_entry_column11 (a : Fin 97) :
    entryMatrix a (1,1) (1,1) = column11 a := by
  change vertexRow a 1 1 1 1 = column11 a
  rw [←actual_primal_row, actual_column11]

theorem actual_entry_column12 (a : Fin 97) :
    entryMatrix a (1,1) (1,2) = column12 a := by
  change vertexRow a 1 1 1 2 = column12 a
  rw [←actual_primal_row, actual_column12]

theorem actual_entry_column13 (a : Fin 97) :
    entryMatrix a (1,1) (2,1) = column13 a := by
  change vertexRow a 1 2 1 1 = column13 a
  rw [←actual_primal_row, actual_column13]

theorem actual_entry_column14 (a : Fin 97) :
    entryMatrix a (1,1) (2,2) = column14 a := by
  change vertexRow a 1 2 1 2 = column14 a
  rw [←actual_primal_row, actual_column14]

theorem actual_entry_column15 (a : Fin 97) :
    entryMatrix a (1,1) (3,1) = column15 a := by
  change vertexRow a 1 3 1 1 = column15 a
  rw [←actual_primal_row, actual_column15]

theorem actual_entry_column16 (a : Fin 97) :
    entryMatrix a (1,1) (3,2) = column16 a := by
  change vertexRow a 1 3 1 2 = column16 a
  rw [←actual_primal_row, actual_column16]

theorem actual_entry_column17 (a : Fin 97) :
    entryMatrix a (2,2) (0,0) = column17 a := by
  change vertexRow a 2 0 2 0 = column17 a
  rw [←actual_primal_row, actual_column17]

theorem actual_entry_column18 (a : Fin 97) :
    entryMatrix a (2,2) (0,1) = column18 a := by
  change vertexRow a 2 0 2 1 = column18 a
  rw [←actual_primal_row, actual_column18]

theorem actual_entry_column19 (a : Fin 97) :
    entryMatrix a (2,2) (0,2) = column19 a := by
  change vertexRow a 2 0 2 2 = column19 a
  rw [←actual_primal_row, actual_column19]

theorem actual_entry_column20 (a : Fin 97) :
    entryMatrix a (2,2) (1,1) = column20 a := by
  change vertexRow a 2 1 2 1 = column20 a
  rw [←actual_primal_row, actual_column20]

theorem actual_entry_column21 (a : Fin 97) :
    entryMatrix a (2,2) (1,2) = column21 a := by
  change vertexRow a 2 1 2 2 = column21 a
  rw [←actual_primal_row, actual_column21]

theorem actual_entry_column22 (a : Fin 97) :
    entryMatrix a (2,2) (2,0) = column22 a := by
  change vertexRow a 2 2 2 0 = column22 a
  rw [←actual_primal_row, actual_column22]

theorem actual_entry_column23 (a : Fin 97) :
    entryMatrix a (2,2) (2,1) = column23 a := by
  change vertexRow a 2 2 2 1 = column23 a
  rw [←actual_primal_row, actual_column23]

theorem actual_entry_column24 (a : Fin 97) :
    entryMatrix a (2,2) (2,2) = column24 a := by
  change vertexRow a 2 2 2 2 = column24 a
  rw [←actual_primal_row, actual_column24]

theorem actual_entry_column25 (a : Fin 97) :
    entryMatrix a (2,2) (3,1) = column25 a := by
  change vertexRow a 2 3 2 1 = column25 a
  rw [←actual_primal_row, actual_column25]

theorem actual_entry_column26 (a : Fin 97) :
    entryMatrix a (2,2) (3,2) = column26 a := by
  change vertexRow a 2 3 2 2 = column26 a
  rw [←actual_primal_row, actual_column26]

end LowEnergy.ActualCandidateBra
