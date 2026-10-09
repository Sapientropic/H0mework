import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraScalarEntries0
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraScalarEntries1
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraScalarEntries2
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraScalarEntries3
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraScalarEntries4
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraScalarEntries5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open MixedSpectatorCanonical79Data
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open scoped BigOperators Matrix

private theorem scalar_read_map_ite (σ : ℂ →+* ℂ) (j k : Fin 79) (c : ℂ) :
    σ (if j = k then c else 0) = if j = k then σ c else 0 := by
  by_cases h : j = k <;> simp [h]

private theorem scalar_delta_0 (j : Fin 79) :
    currentRow0 j = (if j = (0 : Fin 79) then currentCoefficient1 else 0) + (if j = (37 : Fin 79) then currentCoefficient2 else 0) + (if j = (51 : Fin 79) then currentCoefficient0 else 0) := by
  fin_cases j <;> norm_num [currentRow0,Fin.ext_iff]

theorem scalar_read_0 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow0 j)) = f 0 * σ currentCoefficient1 + f 37 * σ currentCoefficient2 + f 51 * σ currentCoefficient0 := by
  simp_rw [scalar_delta_0]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_1 (j : Fin 79) :
    currentRow1 j = (if j = (1 : Fin 79) then currentCoefficient1 else 0) + (if j = (36 : Fin 79) then currentCoefficient3 else 0) + (if j = (49 : Fin 79) then currentCoefficient0 else 0) := by
  fin_cases j <;> norm_num [currentRow1,Fin.ext_iff]

theorem scalar_read_1 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow1 j)) = f 1 * σ currentCoefficient1 + f 36 * σ currentCoefficient3 + f 49 * σ currentCoefficient0 := by
  simp_rw [scalar_delta_1]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_2 (j : Fin 79) :
    currentRow2 j = (if j = (2 : Fin 79) then currentCoefficient1 else 0) + (if j = (39 : Fin 79) then currentCoefficient2 else 0) := by
  fin_cases j <;> norm_num [currentRow2,Fin.ext_iff]

theorem scalar_read_2 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow2 j)) = f 2 * σ currentCoefficient1 + f 39 * σ currentCoefficient2 := by
  simp_rw [scalar_delta_2]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_3 (j : Fin 79) :
    currentRow3 j = (if j = (3 : Fin 79) then currentCoefficient1 else 0) + (if j = (38 : Fin 79) then currentCoefficient3 else 0) := by
  fin_cases j <;> norm_num [currentRow3,Fin.ext_iff]

theorem scalar_read_3 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow3 j)) = f 3 * σ currentCoefficient1 + f 38 * σ currentCoefficient3 := by
  simp_rw [scalar_delta_3]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_4 (j : Fin 79) :
    currentRow4 j = (if j = (4 : Fin 79) then currentCoefficient1 else 0) + (if j = (40 : Fin 79) then currentCoefficient4 else 0) := by
  fin_cases j <;> norm_num [currentRow4,Fin.ext_iff]

theorem scalar_read_4 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow4 j)) = f 4 * σ currentCoefficient1 + f 40 * σ currentCoefficient4 := by
  simp_rw [scalar_delta_4]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_5 (j : Fin 79) :
    currentRow5 j = (if j = (5 : Fin 79) then currentCoefficient1 else 0) + (if j = (41 : Fin 79) then currentCoefficient4 else 0) := by
  fin_cases j <;> norm_num [currentRow5,Fin.ext_iff]

theorem scalar_read_5 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow5 j)) = f 5 * σ currentCoefficient1 + f 41 * σ currentCoefficient4 := by
  simp_rw [scalar_delta_5]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_6 (j : Fin 79) :
    currentRow6 j = (if j = (6 : Fin 79) then currentCoefficient1 else 0) + (if j = (7 : Fin 79) then currentCoefficient10 else 0) + (if j = (10 : Fin 79) then currentCoefficient11 else 0) + (if j = (11 : Fin 79) then currentCoefficient10 else 0) + (if j = (43 : Fin 79) then currentCoefficient12 else 0) + (if j = (46 : Fin 79) then currentCoefficient13 else 0) + (if j = (47 : Fin 79) then currentCoefficient13 else 0) + (if j = (48 : Fin 79) then currentCoefficient14 else 0) + (if j = (50 : Fin 79) then currentCoefficient8 else 0) + (if j = (53 : Fin 79) then currentCoefficient8 else 0) + (if j = (54 : Fin 79) then currentCoefficient9 else 0) + (if j = (57 : Fin 79) then currentCoefficient5 else 0) + (if j = (58 : Fin 79) then currentCoefficient6 else 0) + (if j = (60 : Fin 79) then currentCoefficient7 else 0) + (if j = (64 : Fin 79) then currentCoefficient6 else 0) + (if j = (66 : Fin 79) then currentCoefficient7 else 0) := by
  fin_cases j <;> norm_num [currentRow6,Fin.ext_iff]

theorem scalar_read_6 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow6 j)) = f 6 * σ currentCoefficient1 + f 7 * σ currentCoefficient10 + f 10 * σ currentCoefficient11 + f 11 * σ currentCoefficient10 + f 43 * σ currentCoefficient12 + f 46 * σ currentCoefficient13 + f 47 * σ currentCoefficient13 + f 48 * σ currentCoefficient14 + f 50 * σ currentCoefficient8 + f 53 * σ currentCoefficient8 + f 54 * σ currentCoefficient9 + f 57 * σ currentCoefficient5 + f 58 * σ currentCoefficient6 + f 60 * σ currentCoefficient7 + f 64 * σ currentCoefficient6 + f 66 * σ currentCoefficient7 := by
  simp_rw [scalar_delta_6]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_7 (j : Fin 79) :
    currentRow7 j = (if j = (6 : Fin 79) then currentCoefficient10 else 0) + (if j = (7 : Fin 79) then currentCoefficient1 else 0) + (if j = (10 : Fin 79) then currentCoefficient11 else 0) + (if j = (11 : Fin 79) then currentCoefficient10 else 0) + (if j = (42 : Fin 79) then currentCoefficient12 else 0) + (if j = (43 : Fin 79) then currentCoefficient4 else 0) + (if j = (46 : Fin 79) then currentCoefficient13 else 0) + (if j = (47 : Fin 79) then currentCoefficient12 else 0) + (if j = (48 : Fin 79) then currentCoefficient14 else 0) + (if j = (50 : Fin 79) then currentCoefficient8 else 0) + (if j = (52 : Fin 79) then currentCoefficient16 else 0) + (if j = (53 : Fin 79) then currentCoefficient8 else 0) + (if j = (54 : Fin 79) then currentCoefficient15 else 0) + (if j = (57 : Fin 79) then currentCoefficient5 else 0) + (if j = (58 : Fin 79) then currentCoefficient17 else 0) + (if j = (66 : Fin 79) then currentCoefficient18 else 0) := by
  fin_cases j <;> norm_num [currentRow7,Fin.ext_iff]

theorem scalar_read_7 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow7 j)) = f 6 * σ currentCoefficient10 + f 7 * σ currentCoefficient1 + f 10 * σ currentCoefficient11 + f 11 * σ currentCoefficient10 + f 42 * σ currentCoefficient12 + f 43 * σ currentCoefficient4 + f 46 * σ currentCoefficient13 + f 47 * σ currentCoefficient12 + f 48 * σ currentCoefficient14 + f 50 * σ currentCoefficient8 + f 52 * σ currentCoefficient16 + f 53 * σ currentCoefficient8 + f 54 * σ currentCoefficient15 + f 57 * σ currentCoefficient5 + f 58 * σ currentCoefficient17 + f 66 * σ currentCoefficient18 := by
  simp_rw [scalar_delta_7]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_10 (j : Fin 79) :
    currentRow10 j = (if j = (6 : Fin 79) then currentCoefficient11 else 0) + (if j = (7 : Fin 79) then currentCoefficient11 else 0) + (if j = (11 : Fin 79) then currentCoefficient21 else 0) + (if j = (42 : Fin 79) then currentCoefficient12 else 0) + (if j = (43 : Fin 79) then currentCoefficient13 else 0) + (if j = (48 : Fin 79) then currentCoefficient22 else 0) + (if j = (50 : Fin 79) then currentCoefficient20 else 0) + (if j = (53 : Fin 79) then currentCoefficient20 else 0) + (if j = (57 : Fin 79) then currentCoefficient19 else 0) + (if j = (58 : Fin 79) then currentCoefficient7 else 0) + (if j = (60 : Fin 79) then currentCoefficient6 else 0) + (if j = (64 : Fin 79) then currentCoefficient7 else 0) + (if j = (66 : Fin 79) then currentCoefficient6 else 0) := by
  fin_cases j <;> norm_num [currentRow10,Fin.ext_iff]

theorem scalar_read_10 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow10 j)) = f 6 * σ currentCoefficient11 + f 7 * σ currentCoefficient11 + f 11 * σ currentCoefficient21 + f 42 * σ currentCoefficient12 + f 43 * σ currentCoefficient13 + f 48 * σ currentCoefficient22 + f 50 * σ currentCoefficient20 + f 53 * σ currentCoefficient20 + f 57 * σ currentCoefficient19 + f 58 * σ currentCoefficient7 + f 60 * σ currentCoefficient6 + f 64 * σ currentCoefficient7 + f 66 * σ currentCoefficient6 := by
  simp_rw [scalar_delta_10]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_11 (j : Fin 79) :
    currentRow11 j = (if j = (6 : Fin 79) then currentCoefficient10 else 0) + (if j = (7 : Fin 79) then currentCoefficient10 else 0) + (if j = (10 : Fin 79) then currentCoefficient21 else 0) + (if j = (11 : Fin 79) then currentCoefficient21 else 0) + (if j = (42 : Fin 79) then currentCoefficient23 else 0) + (if j = (43 : Fin 79) then currentCoefficient12 else 0) + (if j = (46 : Fin 79) then currentCoefficient24 else 0) + (if j = (48 : Fin 79) then currentCoefficient25 else 0) + (if j = (50 : Fin 79) then currentCoefficient26 else 0) + (if j = (52 : Fin 79) then currentCoefficient16 else 0) + (if j = (53 : Fin 79) then currentCoefficient26 else 0) + (if j = (57 : Fin 79) then currentCoefficient27 else 0) + (if j = (58 : Fin 79) then currentCoefficient6 else 0) + (if j = (60 : Fin 79) then currentCoefficient6 else 0) + (if j = (64 : Fin 79) then currentCoefficient7 else 0) + (if j = (66 : Fin 79) then currentCoefficient7 else 0) := by
  fin_cases j <;> norm_num [currentRow11,Fin.ext_iff]

theorem scalar_read_11 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow11 j)) = f 6 * σ currentCoefficient10 + f 7 * σ currentCoefficient10 + f 10 * σ currentCoefficient21 + f 11 * σ currentCoefficient21 + f 42 * σ currentCoefficient23 + f 43 * σ currentCoefficient12 + f 46 * σ currentCoefficient24 + f 48 * σ currentCoefficient25 + f 50 * σ currentCoefficient26 + f 52 * σ currentCoefficient16 + f 53 * σ currentCoefficient26 + f 57 * σ currentCoefficient27 + f 58 * σ currentCoefficient6 + f 60 * σ currentCoefficient6 + f 64 * σ currentCoefficient7 + f 66 * σ currentCoefficient7 := by
  simp_rw [scalar_delta_11]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_12 (j : Fin 79) :
    currentRow12 j = (if j = (12 : Fin 79) then currentCoefficient28 else 0) + (if j = (25 : Fin 79) then currentCoefficient28 else 0) + (if j = (52 : Fin 79) then currentCoefficient29 else 0) := by
  fin_cases j <;> norm_num [currentRow12,Fin.ext_iff]

theorem scalar_read_12 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow12 j)) = f 12 * σ currentCoefficient28 + f 25 * σ currentCoefficient28 + f 52 * σ currentCoefficient29 := by
  simp_rw [scalar_delta_12]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_13 (j : Fin 79) :
    currentRow13 j = (if j = (13 : Fin 79) then currentCoefficient28 else 0) + (if j = (24 : Fin 79) then currentCoefficient30 else 0) + (if j = (50 : Fin 79) then currentCoefficient29 else 0) + (if j = (53 : Fin 79) then currentCoefficient31 else 0) := by
  fin_cases j <;> norm_num [currentRow13,Fin.ext_iff]

theorem scalar_read_13 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow13 j)) = f 13 * σ currentCoefficient28 + f 24 * σ currentCoefficient30 + f 50 * σ currentCoefficient29 + f 53 * σ currentCoefficient31 := by
  simp_rw [scalar_delta_13]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_16 (j : Fin 79) :
    currentRow16 j = (if j = (16 : Fin 79) then currentCoefficient32 else 0) + (if j = (29 : Fin 79) then currentCoefficient33 else 0) := by
  fin_cases j <;> norm_num [currentRow16,Fin.ext_iff]

theorem scalar_read_16 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow16 j)) = f 16 * σ currentCoefficient32 + f 29 * σ currentCoefficient33 := by
  simp_rw [scalar_delta_16]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_17 (j : Fin 79) :
    currentRow17 j = (if j = (17 : Fin 79) then currentCoefficient32 else 0) + (if j = (28 : Fin 79) then currentCoefficient32 else 0) := by
  fin_cases j <;> norm_num [currentRow17,Fin.ext_iff]

theorem scalar_read_17 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow17 j)) = f 17 * σ currentCoefficient32 + f 28 * σ currentCoefficient32 := by
  simp_rw [scalar_delta_17]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]


private theorem scalar_primal_row_0 (j : Fin 79) :
    primalCurrentPoint 0 j = currentRow0 j := rfl

theorem actual_scalar_row_0 (dual : Bool) :
    scalarRow dual 0 = (15650764710741639/356693959451345000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_0]
  rw [scalar_read_0]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_0_0,actual_scalar_entry_0_37,actual_scalar_entry_0_51,actual_scalar_entry_37_0,actual_scalar_entry_51_0,currentCoefficient0,currentCoefficient1,currentCoefficient2,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_1 (j : Fin 79) :
    primalCurrentPoint 1 j = currentRow1 j := rfl

theorem actual_scalar_row_1 (dual : Bool) :
    scalarRow dual 1 = (15650764710741639/356693959451345000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_1]
  rw [scalar_read_1]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_1_1,actual_scalar_entry_1_36,actual_scalar_entry_1_49,actual_scalar_entry_36_1,actual_scalar_entry_49_1,currentCoefficient0,currentCoefficient1,currentCoefficient3,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_2 (j : Fin 79) :
    primalCurrentPoint 2 j = currentRow2 j := rfl

theorem actual_scalar_row_2 (dual : Bool) :
    scalarRow dual 2 = (-13584123/103992025 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_2]
  rw [scalar_read_2]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_2_2,actual_scalar_entry_2_39,actual_scalar_entry_39_2,currentCoefficient1,currentCoefficient2,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_3 (j : Fin 79) :
    primalCurrentPoint 3 j = currentRow3 j := rfl

theorem actual_scalar_row_3 (dual : Bool) :
    scalarRow dual 3 = (-13584123/103992025 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_3]
  rw [scalar_read_3]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_3_3,actual_scalar_entry_3_38,actual_scalar_entry_38_3,currentCoefficient1,currentCoefficient3,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_4 (j : Fin 79) :
    primalCurrentPoint 4 j = currentRow4 j := rfl

theorem actual_scalar_row_4 (dual : Bool) :
    scalarRow dual 4 = (-2075067/20798405 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_4]
  rw [scalar_read_4]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_4_4,actual_scalar_entry_4_40,actual_scalar_entry_40_4,currentCoefficient1,currentCoefficient4,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_5 (j : Fin 79) :
    primalCurrentPoint 5 j = currentRow5 j := rfl

theorem actual_scalar_row_5 (dual : Bool) :
    scalarRow dual 5 = (-2075067/20798405 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_5]
  rw [scalar_read_5]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_5_5,actual_scalar_entry_5_41,actual_scalar_entry_41_5,currentCoefficient1,currentCoefficient4,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_6 (j : Fin 79) :
    primalCurrentPoint 6 j = currentRow6 j := rfl

theorem actual_scalar_row_6 (dual : Bool) :
    scalarRow dual 6 = (-301200223533643473003/5862265223582855075000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_6]
  rw [scalar_read_6]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_6,actual_scalar_entry_6_7,actual_scalar_entry_6_10,actual_scalar_entry_6_11,actual_scalar_entry_6_43,actual_scalar_entry_6_46,actual_scalar_entry_6_47,actual_scalar_entry_6_48,actual_scalar_entry_6_50,actual_scalar_entry_6_53,actual_scalar_entry_6_54,actual_scalar_entry_6_57,actual_scalar_entry_6_58,actual_scalar_entry_6_60,actual_scalar_entry_6_64,actual_scalar_entry_6_66,actual_scalar_entry_7_6,actual_scalar_entry_10_6,actual_scalar_entry_11_6,actual_scalar_entry_43_6,actual_scalar_entry_46_6,actual_scalar_entry_47_6,actual_scalar_entry_48_6,actual_scalar_entry_50_6,actual_scalar_entry_53_6,actual_scalar_entry_54_6,actual_scalar_entry_57_6,actual_scalar_entry_58_6,actual_scalar_entry_60_6,actual_scalar_entry_64_6,actual_scalar_entry_66_6,currentCoefficient1,currentCoefficient5,currentCoefficient6,currentCoefficient7,currentCoefficient8,currentCoefficient9,currentCoefficient10,currentCoefficient11,currentCoefficient12,currentCoefficient13,currentCoefficient14,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_7 (j : Fin 79) :
    primalCurrentPoint 7 j = currentRow7 j := rfl

theorem actual_scalar_row_7 (dual : Bool) :
    scalarRow dual 7 = (-132025298273063428347/5862265223582855075000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_7]
  rw [scalar_read_7]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_7,actual_scalar_entry_7_6,actual_scalar_entry_7_7,actual_scalar_entry_7_10,actual_scalar_entry_7_11,actual_scalar_entry_7_42,actual_scalar_entry_7_43,actual_scalar_entry_7_46,actual_scalar_entry_7_47,actual_scalar_entry_7_48,actual_scalar_entry_7_50,actual_scalar_entry_7_52,actual_scalar_entry_7_53,actual_scalar_entry_7_54,actual_scalar_entry_7_57,actual_scalar_entry_7_58,actual_scalar_entry_7_66,actual_scalar_entry_10_7,actual_scalar_entry_11_7,actual_scalar_entry_42_7,actual_scalar_entry_43_7,actual_scalar_entry_46_7,actual_scalar_entry_47_7,actual_scalar_entry_48_7,actual_scalar_entry_50_7,actual_scalar_entry_52_7,actual_scalar_entry_53_7,actual_scalar_entry_54_7,actual_scalar_entry_57_7,actual_scalar_entry_58_7,actual_scalar_entry_66_7,currentCoefficient1,currentCoefficient4,currentCoefficient5,currentCoefficient8,currentCoefficient10,currentCoefficient11,currentCoefficient12,currentCoefficient13,currentCoefficient14,currentCoefficient15,currentCoefficient16,currentCoefficient17,currentCoefficient18,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_10 (j : Fin 79) :
    primalCurrentPoint 10 j = currentRow10 j := rfl

theorem actual_scalar_row_10 (dual : Bool) :
    scalarRow dual 10 = (27/500 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_10]
  rw [scalar_read_10]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_10,actual_scalar_entry_7_10,actual_scalar_entry_10_6,actual_scalar_entry_10_7,actual_scalar_entry_10_11,actual_scalar_entry_10_42,actual_scalar_entry_10_43,actual_scalar_entry_10_48,actual_scalar_entry_10_50,actual_scalar_entry_10_53,actual_scalar_entry_10_57,actual_scalar_entry_10_58,actual_scalar_entry_10_60,actual_scalar_entry_10_64,actual_scalar_entry_10_66,actual_scalar_entry_11_10,actual_scalar_entry_42_10,actual_scalar_entry_43_10,actual_scalar_entry_48_10,actual_scalar_entry_50_10,actual_scalar_entry_53_10,actual_scalar_entry_57_10,actual_scalar_entry_58_10,actual_scalar_entry_60_10,actual_scalar_entry_64_10,actual_scalar_entry_66_10,currentCoefficient6,currentCoefficient7,currentCoefficient11,currentCoefficient12,currentCoefficient13,currentCoefficient19,currentCoefficient20,currentCoefficient21,currentCoefficient22,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_11 (j : Fin 79) :
    primalCurrentPoint 11 j = currentRow11 j := rfl

theorem actual_scalar_row_11 (dual : Bool) :
    scalarRow dual 11 = (81/500 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_11]
  rw [scalar_read_11]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_11,actual_scalar_entry_7_11,actual_scalar_entry_10_11,actual_scalar_entry_11_6,actual_scalar_entry_11_7,actual_scalar_entry_11_10,actual_scalar_entry_11_11,actual_scalar_entry_11_42,actual_scalar_entry_11_43,actual_scalar_entry_11_46,actual_scalar_entry_11_48,actual_scalar_entry_11_50,actual_scalar_entry_11_52,actual_scalar_entry_11_53,actual_scalar_entry_11_57,actual_scalar_entry_11_58,actual_scalar_entry_11_60,actual_scalar_entry_11_64,actual_scalar_entry_11_66,actual_scalar_entry_42_11,actual_scalar_entry_43_11,actual_scalar_entry_46_11,actual_scalar_entry_48_11,actual_scalar_entry_50_11,actual_scalar_entry_52_11,actual_scalar_entry_53_11,actual_scalar_entry_57_11,actual_scalar_entry_58_11,actual_scalar_entry_60_11,actual_scalar_entry_64_11,actual_scalar_entry_66_11,currentCoefficient6,currentCoefficient7,currentCoefficient10,currentCoefficient12,currentCoefficient16,currentCoefficient21,currentCoefficient23,currentCoefficient24,currentCoefficient25,currentCoefficient26,currentCoefficient27,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_12 (j : Fin 79) :
    primalCurrentPoint 12 j = currentRow12 j := rfl

theorem actual_scalar_row_12 (dual : Bool) :
    scalarRow dual 12 = (2169/775000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_12]
  rw [scalar_read_12]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_12_12,actual_scalar_entry_12_25,actual_scalar_entry_12_52,actual_scalar_entry_25_12,actual_scalar_entry_52_12,currentCoefficient28,currentCoefficient29,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_13 (j : Fin 79) :
    primalCurrentPoint 13 j = currentRow13 j := rfl

theorem actual_scalar_row_13 (dual : Bool) :
    scalarRow dual 13 = (9/1240 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_13]
  rw [scalar_read_13]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_13_13,actual_scalar_entry_13_24,actual_scalar_entry_13_50,actual_scalar_entry_13_53,actual_scalar_entry_24_13,actual_scalar_entry_50_13,actual_scalar_entry_53_13,currentCoefficient28,currentCoefficient29,currentCoefficient30,currentCoefficient31,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_16 (j : Fin 79) :
    primalCurrentPoint 16 j = currentRow16 j := rfl

theorem actual_scalar_row_16 (dual : Bool) :
    scalarRow dual 16 = (108/2671 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_16]
  rw [scalar_read_16]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_16_16,actual_scalar_entry_16_29,actual_scalar_entry_29_16,currentCoefficient32,currentCoefficient33,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_17 (j : Fin 79) :
    primalCurrentPoint 17 j = currentRow17 j := rfl

theorem actual_scalar_row_17 (dual : Bool) :
    scalarRow dual 17 = (108/2671 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_17]
  rw [scalar_read_17]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_17_17,actual_scalar_entry_17_28,actual_scalar_entry_28_17,currentCoefficient32,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring


end LowEnergy.ActualCanonical79Imaginary
