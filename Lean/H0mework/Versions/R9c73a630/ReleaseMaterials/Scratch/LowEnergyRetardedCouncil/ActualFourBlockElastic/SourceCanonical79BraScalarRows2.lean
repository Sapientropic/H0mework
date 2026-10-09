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

private theorem scalar_delta_38 (j : Fin 79) :
    currentRow38 j = (if j = (3 : Fin 79) then currentCoefficient3 else 0) + (if j = (38 : Fin 79) then currentCoefficient30 else 0) := by
  fin_cases j <;> norm_num [currentRow38,Fin.ext_iff]

theorem scalar_read_38 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow38 j)) = f 3 * σ currentCoefficient3 + f 38 * σ currentCoefficient30 := by
  simp_rw [scalar_delta_38]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_39 (j : Fin 79) :
    currentRow39 j = (if j = (2 : Fin 79) then currentCoefficient2 else 0) + (if j = (39 : Fin 79) then currentCoefficient30 else 0) := by
  fin_cases j <;> norm_num [currentRow39,Fin.ext_iff]

theorem scalar_read_39 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow39 j)) = f 2 * σ currentCoefficient2 + f 39 * σ currentCoefficient30 := by
  simp_rw [scalar_delta_39]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_40 (j : Fin 79) :
    currentRow40 j = (if j = (4 : Fin 79) then currentCoefficient4 else 0) + (if j = (40 : Fin 79) then currentCoefficient28 else 0) := by
  fin_cases j <;> norm_num [currentRow40,Fin.ext_iff]

theorem scalar_read_40 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow40 j)) = f 4 * σ currentCoefficient4 + f 40 * σ currentCoefficient28 := by
  simp_rw [scalar_delta_40]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_41 (j : Fin 79) :
    currentRow41 j = (if j = (5 : Fin 79) then currentCoefficient4 else 0) + (if j = (41 : Fin 79) then currentCoefficient28 else 0) := by
  fin_cases j <;> norm_num [currentRow41,Fin.ext_iff]

theorem scalar_read_41 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow41 j)) = f 5 * σ currentCoefficient4 + f 41 * σ currentCoefficient28 := by
  simp_rw [scalar_delta_41]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_42 (j : Fin 79) :
    currentRow42 j = (if j = (7 : Fin 79) then currentCoefficient12 else 0) + (if j = (10 : Fin 79) then currentCoefficient12 else 0) + (if j = (11 : Fin 79) then currentCoefficient23 else 0) + (if j = (42 : Fin 79) then currentCoefficient30 else 0) + (if j = (43 : Fin 79) then currentCoefficient34 else 0) + (if j = (46 : Fin 79) then currentCoefficient34 else 0) + (if j = (47 : Fin 79) then currentCoefficient34 else 0) + (if j = (48 : Fin 79) then currentCoefficient65 else 0) + (if j = (50 : Fin 79) then currentCoefficient66 else 0) + (if j = (53 : Fin 79) then currentCoefficient66 else 0) + (if j = (54 : Fin 79) then currentCoefficient67 else 0) + (if j = (57 : Fin 79) then currentCoefficient68 else 0) + (if j = (58 : Fin 79) then currentCoefficient53 else 0) + (if j = (60 : Fin 79) then currentCoefficient52 else 0) + (if j = (64 : Fin 79) then currentCoefficient53 else 0) + (if j = (66 : Fin 79) then currentCoefficient52 else 0) := by
  fin_cases j <;> norm_num [currentRow42,Fin.ext_iff]

theorem scalar_read_42 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow42 j)) = f 7 * σ currentCoefficient12 + f 10 * σ currentCoefficient12 + f 11 * σ currentCoefficient23 + f 42 * σ currentCoefficient30 + f 43 * σ currentCoefficient34 + f 46 * σ currentCoefficient34 + f 47 * σ currentCoefficient34 + f 48 * σ currentCoefficient65 + f 50 * σ currentCoefficient66 + f 53 * σ currentCoefficient66 + f 54 * σ currentCoefficient67 + f 57 * σ currentCoefficient68 + f 58 * σ currentCoefficient53 + f 60 * σ currentCoefficient52 + f 64 * σ currentCoefficient53 + f 66 * σ currentCoefficient52 := by
  simp_rw [scalar_delta_42]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_43 (j : Fin 79) :
    currentRow43 j = (if j = (6 : Fin 79) then currentCoefficient12 else 0) + (if j = (7 : Fin 79) then currentCoefficient4 else 0) + (if j = (10 : Fin 79) then currentCoefficient13 else 0) + (if j = (11 : Fin 79) then currentCoefficient12 else 0) + (if j = (42 : Fin 79) then currentCoefficient34 else 0) + (if j = (43 : Fin 79) then currentCoefficient28 else 0) + (if j = (46 : Fin 79) then currentCoefficient69 else 0) + (if j = (47 : Fin 79) then currentCoefficient34 else 0) + (if j = (48 : Fin 79) then currentCoefficient70 else 0) + (if j = (50 : Fin 79) then currentCoefficient71 else 0) + (if j = (52 : Fin 79) then currentCoefficient73 else 0) + (if j = (53 : Fin 79) then currentCoefficient71 else 0) + (if j = (54 : Fin 79) then currentCoefficient67 else 0) + (if j = (57 : Fin 79) then currentCoefficient72 else 0) + (if j = (58 : Fin 79) then currentCoefficient74 else 0) + (if j = (66 : Fin 79) then currentCoefficient75 else 0) := by
  fin_cases j <;> norm_num [currentRow43,Fin.ext_iff]

theorem scalar_read_43 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow43 j)) = f 6 * σ currentCoefficient12 + f 7 * σ currentCoefficient4 + f 10 * σ currentCoefficient13 + f 11 * σ currentCoefficient12 + f 42 * σ currentCoefficient34 + f 43 * σ currentCoefficient28 + f 46 * σ currentCoefficient69 + f 47 * σ currentCoefficient34 + f 48 * σ currentCoefficient70 + f 50 * σ currentCoefficient71 + f 52 * σ currentCoefficient73 + f 53 * σ currentCoefficient71 + f 54 * σ currentCoefficient67 + f 57 * σ currentCoefficient72 + f 58 * σ currentCoefficient74 + f 66 * σ currentCoefficient75 := by
  simp_rw [scalar_delta_43]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_46 (j : Fin 79) :
    currentRow46 j = (if j = (6 : Fin 79) then currentCoefficient13 else 0) + (if j = (7 : Fin 79) then currentCoefficient13 else 0) + (if j = (11 : Fin 79) then currentCoefficient24 else 0) + (if j = (42 : Fin 79) then currentCoefficient34 else 0) + (if j = (43 : Fin 79) then currentCoefficient69 else 0) + (if j = (48 : Fin 79) then currentCoefficient78 else 0) + (if j = (50 : Fin 79) then currentCoefficient77 else 0) + (if j = (53 : Fin 79) then currentCoefficient77 else 0) + (if j = (57 : Fin 79) then currentCoefficient76 else 0) + (if j = (58 : Fin 79) then currentCoefficient52 else 0) + (if j = (60 : Fin 79) then currentCoefficient53 else 0) + (if j = (64 : Fin 79) then currentCoefficient52 else 0) + (if j = (66 : Fin 79) then currentCoefficient53 else 0) := by
  fin_cases j <;> norm_num [currentRow46,Fin.ext_iff]

theorem scalar_read_46 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow46 j)) = f 6 * σ currentCoefficient13 + f 7 * σ currentCoefficient13 + f 11 * σ currentCoefficient24 + f 42 * σ currentCoefficient34 + f 43 * σ currentCoefficient69 + f 48 * σ currentCoefficient78 + f 50 * σ currentCoefficient77 + f 53 * σ currentCoefficient77 + f 57 * σ currentCoefficient76 + f 58 * σ currentCoefficient52 + f 60 * σ currentCoefficient53 + f 64 * σ currentCoefficient52 + f 66 * σ currentCoefficient53 := by
  simp_rw [scalar_delta_46]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_47 (j : Fin 79) :
    currentRow47 j = (if j = (6 : Fin 79) then currentCoefficient13 else 0) + (if j = (7 : Fin 79) then currentCoefficient12 else 0) + (if j = (42 : Fin 79) then currentCoefficient34 else 0) + (if j = (43 : Fin 79) then currentCoefficient34 else 0) + (if j = (47 : Fin 79) then currentCoefficient28 else 0) + (if j = (52 : Fin 79) then currentCoefficient73 else 0) + (if j = (54 : Fin 79) then currentCoefficient79 else 0) + (if j = (58 : Fin 79) then currentCoefficient53 else 0) + (if j = (60 : Fin 79) then currentCoefficient53 else 0) + (if j = (64 : Fin 79) then currentCoefficient52 else 0) + (if j = (66 : Fin 79) then currentCoefficient52 else 0) := by
  fin_cases j <;> norm_num [currentRow47,Fin.ext_iff]

theorem scalar_read_47 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow47 j)) = f 6 * σ currentCoefficient13 + f 7 * σ currentCoefficient12 + f 42 * σ currentCoefficient34 + f 43 * σ currentCoefficient34 + f 47 * σ currentCoefficient28 + f 52 * σ currentCoefficient73 + f 54 * σ currentCoefficient79 + f 58 * σ currentCoefficient53 + f 60 * σ currentCoefficient53 + f 64 * σ currentCoefficient52 + f 66 * σ currentCoefficient52 := by
  simp_rw [scalar_delta_47]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_48 (j : Fin 79) :
    currentRow48 j = (if j = (6 : Fin 79) then currentCoefficient14 else 0) + (if j = (7 : Fin 79) then currentCoefficient14 else 0) + (if j = (10 : Fin 79) then currentCoefficient22 else 0) + (if j = (11 : Fin 79) then currentCoefficient25 else 0) + (if j = (42 : Fin 79) then currentCoefficient65 else 0) + (if j = (43 : Fin 79) then currentCoefficient70 else 0) + (if j = (46 : Fin 79) then currentCoefficient78 else 0) + (if j = (48 : Fin 79) then currentCoefficient80 else 0) + (if j = (50 : Fin 79) then currentCoefficient81 else 0) + (if j = (52 : Fin 79) then currentCoefficient82 else 0) + (if j = (53 : Fin 79) then currentCoefficient81 else 0) + (if j = (57 : Fin 79) then currentCoefficient83 else 0) + (if j = (58 : Fin 79) then currentCoefficient84 else 0) + (if j = (60 : Fin 79) then currentCoefficient85 else 0) + (if j = (64 : Fin 79) then currentCoefficient86 else 0) + (if j = (66 : Fin 79) then currentCoefficient87 else 0) := by
  fin_cases j <;> norm_num [currentRow48,Fin.ext_iff]

theorem scalar_read_48 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow48 j)) = f 6 * σ currentCoefficient14 + f 7 * σ currentCoefficient14 + f 10 * σ currentCoefficient22 + f 11 * σ currentCoefficient25 + f 42 * σ currentCoefficient65 + f 43 * σ currentCoefficient70 + f 46 * σ currentCoefficient78 + f 48 * σ currentCoefficient80 + f 50 * σ currentCoefficient81 + f 52 * σ currentCoefficient82 + f 53 * σ currentCoefficient81 + f 57 * σ currentCoefficient83 + f 58 * σ currentCoefficient84 + f 60 * σ currentCoefficient85 + f 64 * σ currentCoefficient86 + f 66 * σ currentCoefficient87 := by
  simp_rw [scalar_delta_48]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_49 (j : Fin 79) :
    currentRow49 j = (if j = (1 : Fin 79) then currentCoefficient0 else 0) + (if j = (36 : Fin 79) then currentCoefficient63 else 0) + (if j = (49 : Fin 79) then currentCoefficient88 else 0) := by
  fin_cases j <;> norm_num [currentRow49,Fin.ext_iff]

theorem scalar_read_49 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow49 j)) = f 1 * σ currentCoefficient0 + f 36 * σ currentCoefficient63 + f 49 * σ currentCoefficient88 := by
  simp_rw [scalar_delta_49]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_50 (j : Fin 79) :
    currentRow50 j = (if j = (6 : Fin 79) then currentCoefficient8 else 0) + (if j = (7 : Fin 79) then currentCoefficient8 else 0) + (if j = (10 : Fin 79) then currentCoefficient89 else 0) + (if j = (11 : Fin 79) then currentCoefficient90 else 0) + (if j = (13 : Fin 79) then currentCoefficient29 else 0) + (if j = (24 : Fin 79) then currentCoefficient31 else 0) + (if j = (42 : Fin 79) then currentCoefficient91 else 0) + (if j = (43 : Fin 79) then currentCoefficient71 else 0) + (if j = (46 : Fin 79) then currentCoefficient92 else 0) + (if j = (48 : Fin 79) then currentCoefficient93 else 0) + (if j = (50 : Fin 79) then currentCoefficient94 else 0) + (if j = (52 : Fin 79) then currentCoefficient95 else 0) + (if j = (53 : Fin 79) then currentCoefficient96 else 0) + (if j = (57 : Fin 79) then currentCoefficient97 else 0) + (if j = (58 : Fin 79) then currentCoefficient98 else 0) + (if j = (60 : Fin 79) then currentCoefficient99 else 0) + (if j = (64 : Fin 79) then currentCoefficient100 else 0) + (if j = (66 : Fin 79) then currentCoefficient101 else 0) := by
  fin_cases j <;> norm_num [currentRow50,Fin.ext_iff]

theorem scalar_read_50 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow50 j)) = f 6 * σ currentCoefficient8 + f 7 * σ currentCoefficient8 + f 10 * σ currentCoefficient89 + f 11 * σ currentCoefficient90 + f 13 * σ currentCoefficient29 + f 24 * σ currentCoefficient31 + f 42 * σ currentCoefficient91 + f 43 * σ currentCoefficient71 + f 46 * σ currentCoefficient92 + f 48 * σ currentCoefficient93 + f 50 * σ currentCoefficient94 + f 52 * σ currentCoefficient95 + f 53 * σ currentCoefficient96 + f 57 * σ currentCoefficient97 + f 58 * σ currentCoefficient98 + f 60 * σ currentCoefficient99 + f 64 * σ currentCoefficient100 + f 66 * σ currentCoefficient101 := by
  simp_rw [scalar_delta_50]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_51 (j : Fin 79) :
    currentRow51 j = (if j = (0 : Fin 79) then currentCoefficient0 else 0) + (if j = (37 : Fin 79) then currentCoefficient64 else 0) + (if j = (51 : Fin 79) then currentCoefficient88 else 0) := by
  fin_cases j <;> norm_num [currentRow51,Fin.ext_iff]

theorem scalar_read_51 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow51 j)) = f 0 * σ currentCoefficient0 + f 37 * σ currentCoefficient64 + f 51 * σ currentCoefficient88 := by
  simp_rw [scalar_delta_51]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_52 (j : Fin 79) :
    currentRow52 j = (if j = (7 : Fin 79) then currentCoefficient102 else 0) + (if j = (11 : Fin 79) then currentCoefficient102 else 0) + (if j = (12 : Fin 79) then currentCoefficient29 else 0) + (if j = (25 : Fin 79) then currentCoefficient29 else 0) + (if j = (43 : Fin 79) then currentCoefficient103 else 0) + (if j = (47 : Fin 79) then currentCoefficient103 else 0) + (if j = (48 : Fin 79) then currentCoefficient104 else 0) + (if j = (50 : Fin 79) then currentCoefficient105 else 0) + (if j = (52 : Fin 79) then currentCoefficient106 else 0) + (if j = (53 : Fin 79) then currentCoefficient105 else 0) + (if j = (54 : Fin 79) then currentCoefficient107 else 0) + (if j = (57 : Fin 79) then currentCoefficient108 else 0) + (if j = (58 : Fin 79) then currentCoefficient109 else 0) + (if j = (66 : Fin 79) then currentCoefficient110 else 0) := by
  fin_cases j <;> norm_num [currentRow52,Fin.ext_iff]

theorem scalar_read_52 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow52 j)) = f 7 * σ currentCoefficient102 + f 11 * σ currentCoefficient102 + f 12 * σ currentCoefficient29 + f 25 * σ currentCoefficient29 + f 43 * σ currentCoefficient103 + f 47 * σ currentCoefficient103 + f 48 * σ currentCoefficient104 + f 50 * σ currentCoefficient105 + f 52 * σ currentCoefficient106 + f 53 * σ currentCoefficient105 + f 54 * σ currentCoefficient107 + f 57 * σ currentCoefficient108 + f 58 * σ currentCoefficient109 + f 66 * σ currentCoefficient110 := by
  simp_rw [scalar_delta_52]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_53 (j : Fin 79) :
    currentRow53 j = (if j = (6 : Fin 79) then currentCoefficient8 else 0) + (if j = (7 : Fin 79) then currentCoefficient8 else 0) + (if j = (10 : Fin 79) then currentCoefficient89 else 0) + (if j = (11 : Fin 79) then currentCoefficient90 else 0) + (if j = (13 : Fin 79) then currentCoefficient31 else 0) + (if j = (24 : Fin 79) then currentCoefficient29 else 0) + (if j = (42 : Fin 79) then currentCoefficient91 else 0) + (if j = (43 : Fin 79) then currentCoefficient71 else 0) + (if j = (46 : Fin 79) then currentCoefficient92 else 0) + (if j = (48 : Fin 79) then currentCoefficient93 else 0) + (if j = (50 : Fin 79) then currentCoefficient96 else 0) + (if j = (52 : Fin 79) then currentCoefficient95 else 0) + (if j = (53 : Fin 79) then currentCoefficient94 else 0) + (if j = (57 : Fin 79) then currentCoefficient97 else 0) + (if j = (58 : Fin 79) then currentCoefficient98 else 0) + (if j = (60 : Fin 79) then currentCoefficient99 else 0) + (if j = (64 : Fin 79) then currentCoefficient100 else 0) + (if j = (66 : Fin 79) then currentCoefficient101 else 0) := by
  fin_cases j <;> norm_num [currentRow53,Fin.ext_iff]

theorem scalar_read_53 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow53 j)) = f 6 * σ currentCoefficient8 + f 7 * σ currentCoefficient8 + f 10 * σ currentCoefficient89 + f 11 * σ currentCoefficient90 + f 13 * σ currentCoefficient31 + f 24 * σ currentCoefficient29 + f 42 * σ currentCoefficient91 + f 43 * σ currentCoefficient71 + f 46 * σ currentCoefficient92 + f 48 * σ currentCoefficient93 + f 50 * σ currentCoefficient96 + f 52 * σ currentCoefficient95 + f 53 * σ currentCoefficient94 + f 57 * σ currentCoefficient97 + f 58 * σ currentCoefficient98 + f 60 * σ currentCoefficient99 + f 64 * σ currentCoefficient100 + f 66 * σ currentCoefficient101 := by
  simp_rw [scalar_delta_53]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]


private theorem scalar_primal_row_38 (j : Fin 79) :
    primalCurrentPoint 38 j = currentRow38 j := rfl

theorem actual_scalar_row_38 (dual : Bool) :
    scalarRow dual 38 = (38418123987/1388813493875 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_38]
  rw [scalar_read_38]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_3_38,actual_scalar_entry_38_3,actual_scalar_entry_38_38,currentCoefficient3,currentCoefficient30,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_39 (j : Fin 79) :
    primalCurrentPoint 39 j = currentRow39 j := rfl

theorem actual_scalar_row_39 (dual : Bool) :
    scalarRow dual 39 = (38418123987/1388813493875 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_39]
  rw [scalar_read_39]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_2_39,actual_scalar_entry_39_2,actual_scalar_entry_39_39,currentCoefficient2,currentCoefficient30,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_40 (j : Fin 79) :
    primalCurrentPoint 40 j = currentRow40 j := rfl

theorem actual_scalar_row_40 (dual : Bool) :
    scalarRow dual 40 = (4435239753/1388813493875 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_40]
  rw [scalar_read_40]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_4_40,actual_scalar_entry_40_4,actual_scalar_entry_40_40,currentCoefficient4,currentCoefficient28,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_41 (j : Fin 79) :
    primalCurrentPoint 41 j = currentRow41 j := rfl

theorem actual_scalar_row_41 (dual : Bool) :
    scalarRow dual 41 = (4435239753/1388813493875 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_41]
  rw [scalar_read_41]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_5_41,actual_scalar_entry_41_5,actual_scalar_entry_41_41,currentCoefficient4,currentCoefficient28,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_42 (j : Fin 79) :
    primalCurrentPoint 42 j = currentRow42 j := rfl

theorem actual_scalar_row_42 (dual : Bool) :
    scalarRow dual 42 = (-53937990545022/1682142101458495 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_42]
  rw [scalar_read_42]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_7_42,actual_scalar_entry_10_42,actual_scalar_entry_11_42,actual_scalar_entry_42_7,actual_scalar_entry_42_10,actual_scalar_entry_42_11,actual_scalar_entry_42_42,actual_scalar_entry_42_43,actual_scalar_entry_42_46,actual_scalar_entry_42_47,actual_scalar_entry_42_48,actual_scalar_entry_42_50,actual_scalar_entry_42_53,actual_scalar_entry_42_54,actual_scalar_entry_42_57,actual_scalar_entry_42_58,actual_scalar_entry_42_60,actual_scalar_entry_42_64,actual_scalar_entry_42_66,actual_scalar_entry_43_42,actual_scalar_entry_46_42,actual_scalar_entry_47_42,actual_scalar_entry_48_42,actual_scalar_entry_50_42,actual_scalar_entry_53_42,actual_scalar_entry_54_42,actual_scalar_entry_57_42,actual_scalar_entry_58_42,actual_scalar_entry_60_42,actual_scalar_entry_64_42,actual_scalar_entry_66_42,currentCoefficient12,currentCoefficient23,currentCoefficient30,currentCoefficient34,currentCoefficient52,currentCoefficient53,currentCoefficient65,currentCoefficient66,currentCoefficient67,currentCoefficient68,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_43 (j : Fin 79) :
    primalCurrentPoint 43 j = currentRow43 j := rfl

theorem actual_scalar_row_43 (dual : Bool) :
    scalarRow dual 43 = (154935472028241/6728568405833980 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_43]
  rw [scalar_read_43]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_43,actual_scalar_entry_7_43,actual_scalar_entry_10_43,actual_scalar_entry_11_43,actual_scalar_entry_42_43,actual_scalar_entry_43_6,actual_scalar_entry_43_7,actual_scalar_entry_43_10,actual_scalar_entry_43_11,actual_scalar_entry_43_42,actual_scalar_entry_43_43,actual_scalar_entry_43_46,actual_scalar_entry_43_47,actual_scalar_entry_43_48,actual_scalar_entry_43_50,actual_scalar_entry_43_52,actual_scalar_entry_43_53,actual_scalar_entry_43_54,actual_scalar_entry_43_57,actual_scalar_entry_43_58,actual_scalar_entry_43_66,actual_scalar_entry_46_43,actual_scalar_entry_47_43,actual_scalar_entry_48_43,actual_scalar_entry_50_43,actual_scalar_entry_52_43,actual_scalar_entry_53_43,actual_scalar_entry_54_43,actual_scalar_entry_57_43,actual_scalar_entry_58_43,actual_scalar_entry_66_43,currentCoefficient4,currentCoefficient12,currentCoefficient13,currentCoefficient28,currentCoefficient34,currentCoefficient67,currentCoefficient69,currentCoefficient70,currentCoefficient71,currentCoefficient72,currentCoefficient73,currentCoefficient74,currentCoefficient75,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_46 (j : Fin 79) :
    primalCurrentPoint 46 j = currentRow46 j := rfl

theorem actual_scalar_row_46 (dual : Bool) :
    scalarRow dual 46 = (0 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_46]
  rw [scalar_read_46]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_46,actual_scalar_entry_7_46,actual_scalar_entry_11_46,actual_scalar_entry_42_46,actual_scalar_entry_43_46,actual_scalar_entry_46_6,actual_scalar_entry_46_7,actual_scalar_entry_46_11,actual_scalar_entry_46_42,actual_scalar_entry_46_43,actual_scalar_entry_46_48,actual_scalar_entry_46_50,actual_scalar_entry_46_53,actual_scalar_entry_46_57,actual_scalar_entry_46_58,actual_scalar_entry_46_60,actual_scalar_entry_46_64,actual_scalar_entry_46_66,actual_scalar_entry_48_46,actual_scalar_entry_50_46,actual_scalar_entry_53_46,actual_scalar_entry_57_46,actual_scalar_entry_58_46,actual_scalar_entry_60_46,actual_scalar_entry_64_46,actual_scalar_entry_66_46,currentCoefficient13,currentCoefficient24,currentCoefficient34,currentCoefficient52,currentCoefficient53,currentCoefficient69,currentCoefficient76,currentCoefficient77,currentCoefficient78,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_47 (j : Fin 79) :
    primalCurrentPoint 47 j = currentRow47 j := rfl

theorem actual_scalar_row_47 (dual : Bool) :
    scalarRow dual 47 = (-42969843/6603303734 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_47]
  rw [scalar_read_47]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_47,actual_scalar_entry_7_47,actual_scalar_entry_42_47,actual_scalar_entry_43_47,actual_scalar_entry_47_6,actual_scalar_entry_47_7,actual_scalar_entry_47_42,actual_scalar_entry_47_43,actual_scalar_entry_47_47,actual_scalar_entry_47_52,actual_scalar_entry_47_54,actual_scalar_entry_47_58,actual_scalar_entry_47_60,actual_scalar_entry_47_64,actual_scalar_entry_47_66,actual_scalar_entry_52_47,actual_scalar_entry_54_47,actual_scalar_entry_58_47,actual_scalar_entry_60_47,actual_scalar_entry_64_47,actual_scalar_entry_66_47,currentCoefficient12,currentCoefficient13,currentCoefficient28,currentCoefficient34,currentCoefficient52,currentCoefficient53,currentCoefficient73,currentCoefficient79,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_48 (j : Fin 79) :
    primalCurrentPoint 48 j = currentRow48 j := rfl

theorem actual_scalar_row_48 (dual : Bool) :
    scalarRow dual 48 = (1144953/10812500 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_48]
  rw [scalar_read_48]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_48,actual_scalar_entry_7_48,actual_scalar_entry_10_48,actual_scalar_entry_11_48,actual_scalar_entry_42_48,actual_scalar_entry_43_48,actual_scalar_entry_46_48,actual_scalar_entry_48_6,actual_scalar_entry_48_7,actual_scalar_entry_48_10,actual_scalar_entry_48_11,actual_scalar_entry_48_42,actual_scalar_entry_48_43,actual_scalar_entry_48_46,actual_scalar_entry_48_48,actual_scalar_entry_48_50,actual_scalar_entry_48_52,actual_scalar_entry_48_53,actual_scalar_entry_48_57,actual_scalar_entry_48_58,actual_scalar_entry_48_60,actual_scalar_entry_48_64,actual_scalar_entry_48_66,actual_scalar_entry_50_48,actual_scalar_entry_52_48,actual_scalar_entry_53_48,actual_scalar_entry_57_48,actual_scalar_entry_58_48,actual_scalar_entry_60_48,actual_scalar_entry_64_48,actual_scalar_entry_66_48,currentCoefficient14,currentCoefficient22,currentCoefficient25,currentCoefficient65,currentCoefficient70,currentCoefficient78,currentCoefficient80,currentCoefficient81,currentCoefficient82,currentCoefficient83,currentCoefficient84,currentCoefficient85,currentCoefficient86,currentCoefficient87,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_49 (j : Fin 79) :
    primalCurrentPoint 49 j = currentRow49 j := rfl

theorem actual_scalar_row_49 (dual : Bool) :
    scalarRow dual 49 = (8307/205000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_49]
  rw [scalar_read_49]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_1_49,actual_scalar_entry_36_49,actual_scalar_entry_49_1,actual_scalar_entry_49_36,actual_scalar_entry_49_49,currentCoefficient0,currentCoefficient63,currentCoefficient88,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_50 (j : Fin 79) :
    primalCurrentPoint 50 j = currentRow50 j := rfl

theorem actual_scalar_row_50 (dual : Bool) :
    scalarRow dual 50 = (13407/1937500 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_50]
  rw [scalar_read_50]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_50,actual_scalar_entry_7_50,actual_scalar_entry_10_50,actual_scalar_entry_11_50,actual_scalar_entry_13_50,actual_scalar_entry_24_50,actual_scalar_entry_42_50,actual_scalar_entry_43_50,actual_scalar_entry_46_50,actual_scalar_entry_48_50,actual_scalar_entry_50_6,actual_scalar_entry_50_7,actual_scalar_entry_50_10,actual_scalar_entry_50_11,actual_scalar_entry_50_13,actual_scalar_entry_50_24,actual_scalar_entry_50_42,actual_scalar_entry_50_43,actual_scalar_entry_50_46,actual_scalar_entry_50_48,actual_scalar_entry_50_50,actual_scalar_entry_50_52,actual_scalar_entry_50_53,actual_scalar_entry_50_57,actual_scalar_entry_50_58,actual_scalar_entry_50_60,actual_scalar_entry_50_64,actual_scalar_entry_50_66,actual_scalar_entry_52_50,actual_scalar_entry_53_50,actual_scalar_entry_57_50,actual_scalar_entry_58_50,actual_scalar_entry_60_50,actual_scalar_entry_64_50,actual_scalar_entry_66_50,currentCoefficient8,currentCoefficient29,currentCoefficient31,currentCoefficient71,currentCoefficient89,currentCoefficient90,currentCoefficient91,currentCoefficient92,currentCoefficient93,currentCoefficient94,currentCoefficient95,currentCoefficient96,currentCoefficient97,currentCoefficient98,currentCoefficient99,currentCoefficient100,currentCoefficient101,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_51 (j : Fin 79) :
    primalCurrentPoint 51 j = currentRow51 j := rfl

theorem actual_scalar_row_51 (dual : Bool) :
    scalarRow dual 51 = (8307/205000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_51]
  rw [scalar_read_51]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_0_51,actual_scalar_entry_37_51,actual_scalar_entry_51_0,actual_scalar_entry_51_37,actual_scalar_entry_51_51,currentCoefficient0,currentCoefficient64,currentCoefficient88,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_52 (j : Fin 79) :
    primalCurrentPoint 52 j = currentRow52 j := rfl

theorem actual_scalar_row_52 (dual : Bool) :
    scalarRow dual 52 = (23301/3293750 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_52]
  rw [scalar_read_52]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_7_52,actual_scalar_entry_11_52,actual_scalar_entry_12_52,actual_scalar_entry_25_52,actual_scalar_entry_43_52,actual_scalar_entry_47_52,actual_scalar_entry_48_52,actual_scalar_entry_50_52,actual_scalar_entry_52_7,actual_scalar_entry_52_11,actual_scalar_entry_52_12,actual_scalar_entry_52_25,actual_scalar_entry_52_43,actual_scalar_entry_52_47,actual_scalar_entry_52_48,actual_scalar_entry_52_50,actual_scalar_entry_52_52,actual_scalar_entry_52_53,actual_scalar_entry_52_54,actual_scalar_entry_52_57,actual_scalar_entry_52_58,actual_scalar_entry_52_66,actual_scalar_entry_53_52,actual_scalar_entry_54_52,actual_scalar_entry_57_52,actual_scalar_entry_58_52,actual_scalar_entry_66_52,currentCoefficient29,currentCoefficient102,currentCoefficient103,currentCoefficient104,currentCoefficient105,currentCoefficient106,currentCoefficient107,currentCoefficient108,currentCoefficient109,currentCoefficient110,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_53 (j : Fin 79) :
    primalCurrentPoint 53 j = currentRow53 j := rfl

theorem actual_scalar_row_53 (dual : Bool) :
    scalarRow dual 53 = (13407/1937500 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_53]
  rw [scalar_read_53]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_53,actual_scalar_entry_7_53,actual_scalar_entry_10_53,actual_scalar_entry_11_53,actual_scalar_entry_13_53,actual_scalar_entry_24_53,actual_scalar_entry_42_53,actual_scalar_entry_43_53,actual_scalar_entry_46_53,actual_scalar_entry_48_53,actual_scalar_entry_50_53,actual_scalar_entry_52_53,actual_scalar_entry_53_6,actual_scalar_entry_53_7,actual_scalar_entry_53_10,actual_scalar_entry_53_11,actual_scalar_entry_53_13,actual_scalar_entry_53_24,actual_scalar_entry_53_42,actual_scalar_entry_53_43,actual_scalar_entry_53_46,actual_scalar_entry_53_48,actual_scalar_entry_53_50,actual_scalar_entry_53_52,actual_scalar_entry_53_53,actual_scalar_entry_53_57,actual_scalar_entry_53_58,actual_scalar_entry_53_60,actual_scalar_entry_53_64,actual_scalar_entry_53_66,actual_scalar_entry_57_53,actual_scalar_entry_58_53,actual_scalar_entry_60_53,actual_scalar_entry_64_53,actual_scalar_entry_66_53,currentCoefficient8,currentCoefficient29,currentCoefficient31,currentCoefficient71,currentCoefficient89,currentCoefficient90,currentCoefficient91,currentCoefficient92,currentCoefficient93,currentCoefficient94,currentCoefficient95,currentCoefficient96,currentCoefficient97,currentCoefficient98,currentCoefficient99,currentCoefficient100,currentCoefficient101,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring


end LowEnergy.ActualCanonical79Imaginary
