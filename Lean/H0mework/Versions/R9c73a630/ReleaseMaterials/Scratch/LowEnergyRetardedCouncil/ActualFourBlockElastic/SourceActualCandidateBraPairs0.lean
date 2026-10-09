import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairFold
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairPilot
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairFastPilot
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCandidateBra

theorem actual_pair_row9 (b : Fin 97) :
    leftRow9 (entryMatrix b) = pairRow9 b := by
  exact actual_pair_row9_pilot b

theorem actual_pair_row10 (b : Fin 97) :
    leftRow10 (entryMatrix b) = pairRow10 b := by
  exact actual_pair_row10_pilot b

theorem actual_pair_row11 (b : Fin 97) :
    leftRow11 (entryMatrix b) = pairRow11 b := by
  eval_bra_pair_row 11

theorem actual_pair_row12 (b : Fin 97) :
    leftRow12 (entryMatrix b) = pairRow12 b := by
  eval_bra_pair_row 12

theorem actual_pair_row13 (b : Fin 97) :
    leftRow13 (entryMatrix b) = pairRow13 b := by
  eval_bra_pair_row 13

theorem actual_pair_row14 (b : Fin 97) :
    leftRow14 (entryMatrix b) = pairRow14 b := by
  eval_bra_pair_row 14

theorem actual_pair_row15 (b : Fin 97) :
    leftRow15 (entryMatrix b) = pairRow15 b := by
  eval_bra_pair_row 15

theorem actual_pair_row16 (b : Fin 97) :
    leftRow16 (entryMatrix b) = pairRow16 b := by
  eval_bra_pair_row 16

theorem actual_pair_row19 (b : Fin 97) :
    leftRow19 (entryMatrix b) = pairRow19 b := by
  eval_bra_pair_row 19

theorem actual_pair_row20 (b : Fin 97) :
    leftRow20 (entryMatrix b) = pairRow20 b := by
  eval_bra_pair_row 20

theorem actual_pair_row21 (b : Fin 97) :
    leftRow21 (entryMatrix b) = pairRow21 b := by
  eval_bra_pair_row 21

theorem actual_pair_row22 (b : Fin 97) :
    leftRow22 (entryMatrix b) = pairRow22 b := by
  eval_bra_pair_row 22

theorem actual_pair_row25 (b : Fin 97) :
    leftRow25 (entryMatrix b) = pairRow25 b := by
  eval_bra_pair_row 25

theorem actual_pair_row26 (b : Fin 97) :
    leftRow26 (entryMatrix b) = pairRow26 b := by
  eval_bra_pair_row 26

theorem actual_pair_row27 (b : Fin 97) :
    leftRow27 (entryMatrix b) = pairRow27 b := by
  eval_bra_pair_row 27

theorem actual_pair_row28 (b : Fin 97) :
    leftRow28 (entryMatrix b) = pairRow28 b := by
  eval_bra_pair_row 28

end LowEnergy.ActualCandidateBra
