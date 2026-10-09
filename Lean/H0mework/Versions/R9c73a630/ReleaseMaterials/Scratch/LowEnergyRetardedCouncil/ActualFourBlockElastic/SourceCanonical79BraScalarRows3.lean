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

private theorem scalar_delta_54 (j : Fin 79) :
    currentRow54 j = (if j = (6 : Fin 79) then currentCoefficient9 else 0) + (if j = (7 : Fin 79) then currentCoefficient15 else 0) + (if j = (42 : Fin 79) then currentCoefficient67 else 0) + (if j = (43 : Fin 79) then currentCoefficient67 else 0) + (if j = (47 : Fin 79) then currentCoefficient79 else 0) + (if j = (52 : Fin 79) then currentCoefficient111 else 0) + (if j = (54 : Fin 79) then currentCoefficient88 else 0) + (if j = (58 : Fin 79) then currentCoefficient86 else 0) + (if j = (60 : Fin 79) then currentCoefficient86 else 0) + (if j = (64 : Fin 79) then currentCoefficient85 else 0) + (if j = (66 : Fin 79) then currentCoefficient85 else 0) := by
  fin_cases j <;> norm_num [currentRow54,Fin.ext_iff]

theorem scalar_read_54 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow54 j)) = f 6 * σ currentCoefficient9 + f 7 * σ currentCoefficient15 + f 42 * σ currentCoefficient67 + f 43 * σ currentCoefficient67 + f 47 * σ currentCoefficient79 + f 52 * σ currentCoefficient111 + f 54 * σ currentCoefficient88 + f 58 * σ currentCoefficient86 + f 60 * σ currentCoefficient86 + f 64 * σ currentCoefficient85 + f 66 * σ currentCoefficient85 := by
  simp_rw [scalar_delta_54]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_55 (j : Fin 79) :
    currentRow55 j = (if j = (18 : Fin 79) then currentCoefficient112 else 0) + (if j = (19 : Fin 79) then currentCoefficient113 else 0) + (if j = (22 : Fin 79) then currentCoefficient114 else 0) + (if j = (23 : Fin 79) then currentCoefficient115 else 0) + (if j = (30 : Fin 79) then currentCoefficient116 else 0) + (if j = (31 : Fin 79) then currentCoefficient117 else 0) + (if j = (34 : Fin 79) then currentCoefficient118 else 0) + (if j = (35 : Fin 79) then currentCoefficient62 else 0) + (if j = (55 : Fin 79) then currentCoefficient106 else 0) + (if j = (56 : Fin 79) then currentCoefficient119 else 0) + (if j = (61 : Fin 79) then currentCoefficient120 else 0) + (if j = (63 : Fin 79) then currentCoefficient120 else 0) + (if j = (67 : Fin 79) then currentCoefficient121 else 0) + (if j = (71 : Fin 79) then currentCoefficient122 else 0) + (if j = (73 : Fin 79) then currentCoefficient123 else 0) + (if j = (77 : Fin 79) then currentCoefficient123 else 0) := by
  fin_cases j <;> norm_num [currentRow55,Fin.ext_iff]

theorem scalar_read_55 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow55 j)) = f 18 * σ currentCoefficient112 + f 19 * σ currentCoefficient113 + f 22 * σ currentCoefficient114 + f 23 * σ currentCoefficient115 + f 30 * σ currentCoefficient116 + f 31 * σ currentCoefficient117 + f 34 * σ currentCoefficient118 + f 35 * σ currentCoefficient62 + f 55 * σ currentCoefficient106 + f 56 * σ currentCoefficient119 + f 61 * σ currentCoefficient120 + f 63 * σ currentCoefficient120 + f 67 * σ currentCoefficient121 + f 71 * σ currentCoefficient122 + f 73 * σ currentCoefficient123 + f 77 * σ currentCoefficient123 := by
  simp_rw [scalar_delta_55]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_56 (j : Fin 79) :
    currentRow56 j = (if j = (18 : Fin 79) then currentCoefficient124 else 0) + (if j = (19 : Fin 79) then currentCoefficient125 else 0) + (if j = (22 : Fin 79) then currentCoefficient126 else 0) + (if j = (23 : Fin 79) then currentCoefficient57 else 0) + (if j = (30 : Fin 79) then currentCoefficient112 else 0) + (if j = (31 : Fin 79) then currentCoefficient113 else 0) + (if j = (34 : Fin 79) then currentCoefficient114 else 0) + (if j = (35 : Fin 79) then currentCoefficient115 else 0) + (if j = (55 : Fin 79) then currentCoefficient127 else 0) + (if j = (56 : Fin 79) then currentCoefficient106 else 0) + (if j = (61 : Fin 79) then currentCoefficient123 else 0) + (if j = (63 : Fin 79) then currentCoefficient123 else 0) + (if j = (67 : Fin 79) then currentCoefficient122 else 0) + (if j = (71 : Fin 79) then currentCoefficient120 else 0) + (if j = (73 : Fin 79) then currentCoefficient121 else 0) + (if j = (77 : Fin 79) then currentCoefficient121 else 0) := by
  fin_cases j <;> norm_num [currentRow56,Fin.ext_iff]

theorem scalar_read_56 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow56 j)) = f 18 * σ currentCoefficient124 + f 19 * σ currentCoefficient125 + f 22 * σ currentCoefficient126 + f 23 * σ currentCoefficient57 + f 30 * σ currentCoefficient112 + f 31 * σ currentCoefficient113 + f 34 * σ currentCoefficient114 + f 35 * σ currentCoefficient115 + f 55 * σ currentCoefficient127 + f 56 * σ currentCoefficient106 + f 61 * σ currentCoefficient123 + f 63 * σ currentCoefficient123 + f 67 * σ currentCoefficient122 + f 71 * σ currentCoefficient120 + f 73 * σ currentCoefficient121 + f 77 * σ currentCoefficient121 := by
  simp_rw [scalar_delta_56]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_57 (j : Fin 79) :
    currentRow57 j = (if j = (6 : Fin 79) then currentCoefficient5 else 0) + (if j = (7 : Fin 79) then currentCoefficient5 else 0) + (if j = (10 : Fin 79) then currentCoefficient128 else 0) + (if j = (11 : Fin 79) then currentCoefficient129 else 0) + (if j = (42 : Fin 79) then currentCoefficient130 else 0) + (if j = (43 : Fin 79) then currentCoefficient72 else 0) + (if j = (46 : Fin 79) then currentCoefficient131 else 0) + (if j = (48 : Fin 79) then currentCoefficient132 else 0) + (if j = (50 : Fin 79) then currentCoefficient133 else 0) + (if j = (52 : Fin 79) then currentCoefficient134 else 0) + (if j = (53 : Fin 79) then currentCoefficient133 else 0) + (if j = (57 : Fin 79) then currentCoefficient94 else 0) + (if j = (58 : Fin 79) then currentCoefficient135 else 0) + (if j = (60 : Fin 79) then currentCoefficient136 else 0) + (if j = (64 : Fin 79) then currentCoefficient137 else 0) + (if j = (66 : Fin 79) then currentCoefficient138 else 0) := by
  fin_cases j <;> norm_num [currentRow57,Fin.ext_iff]

theorem scalar_read_57 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow57 j)) = f 6 * σ currentCoefficient5 + f 7 * σ currentCoefficient5 + f 10 * σ currentCoefficient128 + f 11 * σ currentCoefficient129 + f 42 * σ currentCoefficient130 + f 43 * σ currentCoefficient72 + f 46 * σ currentCoefficient131 + f 48 * σ currentCoefficient132 + f 50 * σ currentCoefficient133 + f 52 * σ currentCoefficient134 + f 53 * σ currentCoefficient133 + f 57 * σ currentCoefficient94 + f 58 * σ currentCoefficient135 + f 60 * σ currentCoefficient136 + f 64 * σ currentCoefficient137 + f 66 * σ currentCoefficient138 := by
  simp_rw [scalar_delta_57]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_58 (j : Fin 79) :
    currentRow58 j = (if j = (6 : Fin 79) then currentCoefficient6 else 0) + (if j = (7 : Fin 79) then currentCoefficient17 else 0) + (if j = (10 : Fin 79) then currentCoefficient7 else 0) + (if j = (11 : Fin 79) then currentCoefficient6 else 0) + (if j = (42 : Fin 79) then currentCoefficient53 else 0) + (if j = (43 : Fin 79) then currentCoefficient74 else 0) + (if j = (46 : Fin 79) then currentCoefficient52 else 0) + (if j = (47 : Fin 79) then currentCoefficient53 else 0) + (if j = (48 : Fin 79) then currentCoefficient84 else 0) + (if j = (50 : Fin 79) then currentCoefficient98 else 0) + (if j = (52 : Fin 79) then currentCoefficient110 else 0) + (if j = (53 : Fin 79) then currentCoefficient98 else 0) + (if j = (54 : Fin 79) then currentCoefficient86 else 0) + (if j = (57 : Fin 79) then currentCoefficient135 else 0) + (if j = (58 : Fin 79) then currentCoefficient139 else 0) + (if j = (66 : Fin 79) then currentCoefficient140 else 0) := by
  fin_cases j <;> norm_num [currentRow58,Fin.ext_iff]

theorem scalar_read_58 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow58 j)) = f 6 * σ currentCoefficient6 + f 7 * σ currentCoefficient17 + f 10 * σ currentCoefficient7 + f 11 * σ currentCoefficient6 + f 42 * σ currentCoefficient53 + f 43 * σ currentCoefficient74 + f 46 * σ currentCoefficient52 + f 47 * σ currentCoefficient53 + f 48 * σ currentCoefficient84 + f 50 * σ currentCoefficient98 + f 52 * σ currentCoefficient110 + f 53 * σ currentCoefficient98 + f 54 * σ currentCoefficient86 + f 57 * σ currentCoefficient135 + f 58 * σ currentCoefficient139 + f 66 * σ currentCoefficient140 := by
  simp_rw [scalar_delta_58]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_60 (j : Fin 79) :
    currentRow60 j = (if j = (6 : Fin 79) then currentCoefficient7 else 0) + (if j = (10 : Fin 79) then currentCoefficient6 else 0) + (if j = (11 : Fin 79) then currentCoefficient6 else 0) + (if j = (42 : Fin 79) then currentCoefficient52 else 0) + (if j = (46 : Fin 79) then currentCoefficient53 else 0) + (if j = (47 : Fin 79) then currentCoefficient53 else 0) + (if j = (48 : Fin 79) then currentCoefficient85 else 0) + (if j = (50 : Fin 79) then currentCoefficient141 else 0) + (if j = (53 : Fin 79) then currentCoefficient141 else 0) + (if j = (54 : Fin 79) then currentCoefficient86 else 0) + (if j = (57 : Fin 79) then currentCoefficient137 else 0) := by
  fin_cases j <;> norm_num [currentRow60,Fin.ext_iff]

theorem scalar_read_60 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow60 j)) = f 6 * σ currentCoefficient7 + f 10 * σ currentCoefficient6 + f 11 * σ currentCoefficient6 + f 42 * σ currentCoefficient52 + f 46 * σ currentCoefficient53 + f 47 * σ currentCoefficient53 + f 48 * σ currentCoefficient85 + f 50 * σ currentCoefficient141 + f 53 * σ currentCoefficient141 + f 54 * σ currentCoefficient86 + f 57 * σ currentCoefficient137 := by
  simp_rw [scalar_delta_60]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_61 (j : Fin 79) :
    currentRow61 j = (if j = (18 : Fin 79) then currentCoefficient38 else 0) + (if j = (19 : Fin 79) then currentCoefficient47 else 0) + (if j = (22 : Fin 79) then currentCoefficient52 else 0) + (if j = (30 : Fin 79) then currentCoefficient41 else 0) + (if j = (31 : Fin 79) then currentCoefficient41 else 0) + (if j = (34 : Fin 79) then currentCoefficient55 else 0) + (if j = (35 : Fin 79) then currentCoefficient55 else 0) + (if j = (55 : Fin 79) then currentCoefficient120 else 0) + (if j = (56 : Fin 79) then currentCoefficient122 else 0) + (if j = (61 : Fin 79) then currentCoefficient142 else 0) + (if j = (63 : Fin 79) then currentCoefficient142 else 0) + (if j = (67 : Fin 79) then currentCoefficient143 else 0) := by
  fin_cases j <;> norm_num [currentRow61,Fin.ext_iff]

theorem scalar_read_61 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow61 j)) = f 18 * σ currentCoefficient38 + f 19 * σ currentCoefficient47 + f 22 * σ currentCoefficient52 + f 30 * σ currentCoefficient41 + f 31 * σ currentCoefficient41 + f 34 * σ currentCoefficient55 + f 35 * σ currentCoefficient55 + f 55 * σ currentCoefficient120 + f 56 * σ currentCoefficient122 + f 61 * σ currentCoefficient142 + f 63 * σ currentCoefficient142 + f 67 * σ currentCoefficient143 := by
  simp_rw [scalar_delta_61]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_63 (j : Fin 79) :
    currentRow63 j = (if j = (18 : Fin 79) then currentCoefficient38 else 0) + (if j = (19 : Fin 79) then currentCoefficient47 else 0) + (if j = (22 : Fin 79) then currentCoefficient52 else 0) + (if j = (30 : Fin 79) then currentCoefficient41 else 0) + (if j = (31 : Fin 79) then currentCoefficient41 else 0) + (if j = (34 : Fin 79) then currentCoefficient55 else 0) + (if j = (35 : Fin 79) then currentCoefficient55 else 0) + (if j = (55 : Fin 79) then currentCoefficient120 else 0) + (if j = (56 : Fin 79) then currentCoefficient122 else 0) + (if j = (61 : Fin 79) then currentCoefficient142 else 0) + (if j = (63 : Fin 79) then currentCoefficient142 else 0) + (if j = (67 : Fin 79) then currentCoefficient143 else 0) := by
  fin_cases j <;> norm_num [currentRow63,Fin.ext_iff]

theorem scalar_read_63 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow63 j)) = f 18 * σ currentCoefficient38 + f 19 * σ currentCoefficient47 + f 22 * σ currentCoefficient52 + f 30 * σ currentCoefficient41 + f 31 * σ currentCoefficient41 + f 34 * σ currentCoefficient55 + f 35 * σ currentCoefficient55 + f 55 * σ currentCoefficient120 + f 56 * σ currentCoefficient122 + f 61 * σ currentCoefficient142 + f 63 * σ currentCoefficient142 + f 67 * σ currentCoefficient143 := by
  simp_rw [scalar_delta_63]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_64 (j : Fin 79) :
    currentRow64 j = (if j = (6 : Fin 79) then currentCoefficient6 else 0) + (if j = (10 : Fin 79) then currentCoefficient7 else 0) + (if j = (11 : Fin 79) then currentCoefficient7 else 0) + (if j = (42 : Fin 79) then currentCoefficient53 else 0) + (if j = (46 : Fin 79) then currentCoefficient52 else 0) + (if j = (47 : Fin 79) then currentCoefficient52 else 0) + (if j = (48 : Fin 79) then currentCoefficient86 else 0) + (if j = (50 : Fin 79) then currentCoefficient144 else 0) + (if j = (53 : Fin 79) then currentCoefficient144 else 0) + (if j = (54 : Fin 79) then currentCoefficient85 else 0) + (if j = (57 : Fin 79) then currentCoefficient136 else 0) := by
  fin_cases j <;> norm_num [currentRow64,Fin.ext_iff]

theorem scalar_read_64 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow64 j)) = f 6 * σ currentCoefficient6 + f 10 * σ currentCoefficient7 + f 11 * σ currentCoefficient7 + f 42 * σ currentCoefficient53 + f 46 * σ currentCoefficient52 + f 47 * σ currentCoefficient52 + f 48 * σ currentCoefficient86 + f 50 * σ currentCoefficient144 + f 53 * σ currentCoefficient144 + f 54 * σ currentCoefficient85 + f 57 * σ currentCoefficient136 := by
  simp_rw [scalar_delta_64]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_66 (j : Fin 79) :
    currentRow66 j = (if j = (6 : Fin 79) then currentCoefficient7 else 0) + (if j = (7 : Fin 79) then currentCoefficient18 else 0) + (if j = (10 : Fin 79) then currentCoefficient6 else 0) + (if j = (11 : Fin 79) then currentCoefficient7 else 0) + (if j = (42 : Fin 79) then currentCoefficient52 else 0) + (if j = (43 : Fin 79) then currentCoefficient75 else 0) + (if j = (46 : Fin 79) then currentCoefficient53 else 0) + (if j = (47 : Fin 79) then currentCoefficient52 else 0) + (if j = (48 : Fin 79) then currentCoefficient87 else 0) + (if j = (50 : Fin 79) then currentCoefficient101 else 0) + (if j = (52 : Fin 79) then currentCoefficient109 else 0) + (if j = (53 : Fin 79) then currentCoefficient101 else 0) + (if j = (54 : Fin 79) then currentCoefficient85 else 0) + (if j = (57 : Fin 79) then currentCoefficient138 else 0) + (if j = (58 : Fin 79) then currentCoefficient140 else 0) + (if j = (66 : Fin 79) then currentCoefficient139 else 0) := by
  fin_cases j <;> norm_num [currentRow66,Fin.ext_iff]

theorem scalar_read_66 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow66 j)) = f 6 * σ currentCoefficient7 + f 7 * σ currentCoefficient18 + f 10 * σ currentCoefficient6 + f 11 * σ currentCoefficient7 + f 42 * σ currentCoefficient52 + f 43 * σ currentCoefficient75 + f 46 * σ currentCoefficient53 + f 47 * σ currentCoefficient52 + f 48 * σ currentCoefficient87 + f 50 * σ currentCoefficient101 + f 52 * σ currentCoefficient109 + f 53 * σ currentCoefficient101 + f 54 * σ currentCoefficient85 + f 57 * σ currentCoefficient138 + f 58 * σ currentCoefficient140 + f 66 * σ currentCoefficient139 := by
  simp_rw [scalar_delta_66]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_67 (j : Fin 79) :
    currentRow67 j = (if j = (18 : Fin 79) then currentCoefficient39 else 0) + (if j = (19 : Fin 79) then currentCoefficient48 else 0) + (if j = (22 : Fin 79) then currentCoefficient53 else 0) + (if j = (30 : Fin 79) then currentCoefficient40 else 0) + (if j = (31 : Fin 79) then currentCoefficient40 else 0) + (if j = (34 : Fin 79) then currentCoefficient54 else 0) + (if j = (35 : Fin 79) then currentCoefficient54 else 0) + (if j = (55 : Fin 79) then currentCoefficient121 else 0) + (if j = (56 : Fin 79) then currentCoefficient123 else 0) + (if j = (61 : Fin 79) then currentCoefficient143 else 0) + (if j = (63 : Fin 79) then currentCoefficient143 else 0) + (if j = (67 : Fin 79) then currentCoefficient142 else 0) := by
  fin_cases j <;> norm_num [currentRow67,Fin.ext_iff]

theorem scalar_read_67 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow67 j)) = f 18 * σ currentCoefficient39 + f 19 * σ currentCoefficient48 + f 22 * σ currentCoefficient53 + f 30 * σ currentCoefficient40 + f 31 * σ currentCoefficient40 + f 34 * σ currentCoefficient54 + f 35 * σ currentCoefficient54 + f 55 * σ currentCoefficient121 + f 56 * σ currentCoefficient123 + f 61 * σ currentCoefficient143 + f 63 * σ currentCoefficient143 + f 67 * σ currentCoefficient142 := by
  simp_rw [scalar_delta_67]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_71 (j : Fin 79) :
    currentRow71 j = (if j = (18 : Fin 79) then currentCoefficient40 else 0) + (if j = (19 : Fin 79) then currentCoefficient40 else 0) + (if j = (22 : Fin 79) then currentCoefficient54 else 0) + (if j = (23 : Fin 79) then currentCoefficient54 else 0) + (if j = (30 : Fin 79) then currentCoefficient38 else 0) + (if j = (31 : Fin 79) then currentCoefficient47 else 0) + (if j = (34 : Fin 79) then currentCoefficient52 else 0) + (if j = (55 : Fin 79) then currentCoefficient123 else 0) + (if j = (56 : Fin 79) then currentCoefficient120 else 0) + (if j = (71 : Fin 79) then currentCoefficient142 else 0) + (if j = (73 : Fin 79) then currentCoefficient143 else 0) + (if j = (77 : Fin 79) then currentCoefficient143 else 0) := by
  fin_cases j <;> norm_num [currentRow71,Fin.ext_iff]

theorem scalar_read_71 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow71 j)) = f 18 * σ currentCoefficient40 + f 19 * σ currentCoefficient40 + f 22 * σ currentCoefficient54 + f 23 * σ currentCoefficient54 + f 30 * σ currentCoefficient38 + f 31 * σ currentCoefficient47 + f 34 * σ currentCoefficient52 + f 55 * σ currentCoefficient123 + f 56 * σ currentCoefficient120 + f 71 * σ currentCoefficient142 + f 73 * σ currentCoefficient143 + f 77 * σ currentCoefficient143 := by
  simp_rw [scalar_delta_71]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_73 (j : Fin 79) :
    currentRow73 j = (if j = (18 : Fin 79) then currentCoefficient41 else 0) + (if j = (19 : Fin 79) then currentCoefficient41 else 0) + (if j = (22 : Fin 79) then currentCoefficient55 else 0) + (if j = (23 : Fin 79) then currentCoefficient55 else 0) + (if j = (30 : Fin 79) then currentCoefficient39 else 0) + (if j = (31 : Fin 79) then currentCoefficient48 else 0) + (if j = (34 : Fin 79) then currentCoefficient53 else 0) + (if j = (55 : Fin 79) then currentCoefficient122 else 0) + (if j = (56 : Fin 79) then currentCoefficient121 else 0) + (if j = (71 : Fin 79) then currentCoefficient143 else 0) + (if j = (73 : Fin 79) then currentCoefficient142 else 0) + (if j = (77 : Fin 79) then currentCoefficient142 else 0) := by
  fin_cases j <;> norm_num [currentRow73,Fin.ext_iff]

theorem scalar_read_73 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow73 j)) = f 18 * σ currentCoefficient41 + f 19 * σ currentCoefficient41 + f 22 * σ currentCoefficient55 + f 23 * σ currentCoefficient55 + f 30 * σ currentCoefficient39 + f 31 * σ currentCoefficient48 + f 34 * σ currentCoefficient53 + f 55 * σ currentCoefficient122 + f 56 * σ currentCoefficient121 + f 71 * σ currentCoefficient143 + f 73 * σ currentCoefficient142 + f 77 * σ currentCoefficient142 := by
  simp_rw [scalar_delta_73]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_77 (j : Fin 79) :
    currentRow77 j = (if j = (18 : Fin 79) then currentCoefficient41 else 0) + (if j = (19 : Fin 79) then currentCoefficient41 else 0) + (if j = (22 : Fin 79) then currentCoefficient55 else 0) + (if j = (23 : Fin 79) then currentCoefficient55 else 0) + (if j = (30 : Fin 79) then currentCoefficient39 else 0) + (if j = (31 : Fin 79) then currentCoefficient48 else 0) + (if j = (34 : Fin 79) then currentCoefficient53 else 0) + (if j = (55 : Fin 79) then currentCoefficient122 else 0) + (if j = (56 : Fin 79) then currentCoefficient121 else 0) + (if j = (71 : Fin 79) then currentCoefficient143 else 0) + (if j = (73 : Fin 79) then currentCoefficient142 else 0) + (if j = (77 : Fin 79) then currentCoefficient142 else 0) := by
  fin_cases j <;> norm_num [currentRow77,Fin.ext_iff]

theorem scalar_read_77 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow77 j)) = f 18 * σ currentCoefficient41 + f 19 * σ currentCoefficient41 + f 22 * σ currentCoefficient55 + f 23 * σ currentCoefficient55 + f 30 * σ currentCoefficient39 + f 31 * σ currentCoefficient48 + f 34 * σ currentCoefficient53 + f 55 * σ currentCoefficient122 + f 56 * σ currentCoefficient121 + f 71 * σ currentCoefficient143 + f 73 * σ currentCoefficient142 + f 77 * σ currentCoefficient142 := by
  simp_rw [scalar_delta_77]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]


private theorem scalar_primal_row_54 (j : Fin 79) :
    primalCurrentPoint 54 j = currentRow54 j := rfl

theorem actual_scalar_row_54 (dual : Bool) :
    scalarRow dual 54 = (3834/25625 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_54]
  rw [scalar_read_54]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_54,actual_scalar_entry_7_54,actual_scalar_entry_42_54,actual_scalar_entry_43_54,actual_scalar_entry_47_54,actual_scalar_entry_52_54,actual_scalar_entry_54_6,actual_scalar_entry_54_7,actual_scalar_entry_54_42,actual_scalar_entry_54_43,actual_scalar_entry_54_47,actual_scalar_entry_54_52,actual_scalar_entry_54_54,actual_scalar_entry_54_58,actual_scalar_entry_54_60,actual_scalar_entry_54_64,actual_scalar_entry_54_66,actual_scalar_entry_58_54,actual_scalar_entry_60_54,actual_scalar_entry_64_54,actual_scalar_entry_66_54,currentCoefficient9,currentCoefficient15,currentCoefficient67,currentCoefficient79,currentCoefficient85,currentCoefficient86,currentCoefficient88,currentCoefficient111,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_55 (j : Fin 79) :
    primalCurrentPoint 55 j = currentRow55 j := rfl

theorem actual_scalar_row_55 (dual : Bool) :
    scalarRow dual 55 = (23301/6587500 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_55]
  rw [scalar_read_55]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_55,actual_scalar_entry_19_55,actual_scalar_entry_22_55,actual_scalar_entry_23_55,actual_scalar_entry_30_55,actual_scalar_entry_31_55,actual_scalar_entry_34_55,actual_scalar_entry_35_55,actual_scalar_entry_55_18,actual_scalar_entry_55_19,actual_scalar_entry_55_22,actual_scalar_entry_55_23,actual_scalar_entry_55_30,actual_scalar_entry_55_31,actual_scalar_entry_55_34,actual_scalar_entry_55_35,actual_scalar_entry_55_55,actual_scalar_entry_55_56,actual_scalar_entry_55_61,actual_scalar_entry_55_63,actual_scalar_entry_55_67,actual_scalar_entry_55_71,actual_scalar_entry_55_73,actual_scalar_entry_55_77,actual_scalar_entry_56_55,actual_scalar_entry_61_55,actual_scalar_entry_63_55,actual_scalar_entry_67_55,actual_scalar_entry_71_55,actual_scalar_entry_73_55,actual_scalar_entry_77_55,currentCoefficient62,currentCoefficient106,currentCoefficient112,currentCoefficient113,currentCoefficient114,currentCoefficient115,currentCoefficient116,currentCoefficient117,currentCoefficient118,currentCoefficient119,currentCoefficient120,currentCoefficient121,currentCoefficient122,currentCoefficient123,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_56 (j : Fin 79) :
    primalCurrentPoint 56 j = currentRow56 j := rfl

theorem actual_scalar_row_56 (dual : Bool) :
    scalarRow dual 56 = (23301/6587500 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_56]
  rw [scalar_read_56]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_56,actual_scalar_entry_19_56,actual_scalar_entry_22_56,actual_scalar_entry_23_56,actual_scalar_entry_30_56,actual_scalar_entry_31_56,actual_scalar_entry_34_56,actual_scalar_entry_35_56,actual_scalar_entry_55_56,actual_scalar_entry_56_18,actual_scalar_entry_56_19,actual_scalar_entry_56_22,actual_scalar_entry_56_23,actual_scalar_entry_56_30,actual_scalar_entry_56_31,actual_scalar_entry_56_34,actual_scalar_entry_56_35,actual_scalar_entry_56_55,actual_scalar_entry_56_56,actual_scalar_entry_56_61,actual_scalar_entry_56_63,actual_scalar_entry_56_67,actual_scalar_entry_56_71,actual_scalar_entry_56_73,actual_scalar_entry_56_77,actual_scalar_entry_61_56,actual_scalar_entry_63_56,actual_scalar_entry_67_56,actual_scalar_entry_71_56,actual_scalar_entry_73_56,actual_scalar_entry_77_56,currentCoefficient57,currentCoefficient106,currentCoefficient112,currentCoefficient113,currentCoefficient114,currentCoefficient115,currentCoefficient120,currentCoefficient121,currentCoefficient122,currentCoefficient123,currentCoefficient124,currentCoefficient125,currentCoefficient126,currentCoefficient127,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_57 (j : Fin 79) :
    primalCurrentPoint 57 j = currentRow57 j := rfl

theorem actual_scalar_row_57 (dual : Bool) :
    scalarRow dual 57 = (-16017/968750 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_57]
  rw [scalar_read_57]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_57,actual_scalar_entry_7_57,actual_scalar_entry_10_57,actual_scalar_entry_11_57,actual_scalar_entry_42_57,actual_scalar_entry_43_57,actual_scalar_entry_46_57,actual_scalar_entry_48_57,actual_scalar_entry_50_57,actual_scalar_entry_52_57,actual_scalar_entry_53_57,actual_scalar_entry_57_6,actual_scalar_entry_57_7,actual_scalar_entry_57_10,actual_scalar_entry_57_11,actual_scalar_entry_57_42,actual_scalar_entry_57_43,actual_scalar_entry_57_46,actual_scalar_entry_57_48,actual_scalar_entry_57_50,actual_scalar_entry_57_52,actual_scalar_entry_57_53,actual_scalar_entry_57_57,actual_scalar_entry_57_58,actual_scalar_entry_57_60,actual_scalar_entry_57_64,actual_scalar_entry_57_66,actual_scalar_entry_58_57,actual_scalar_entry_60_57,actual_scalar_entry_64_57,actual_scalar_entry_66_57,currentCoefficient5,currentCoefficient72,currentCoefficient94,currentCoefficient128,currentCoefficient129,currentCoefficient130,currentCoefficient131,currentCoefficient132,currentCoefficient133,currentCoefficient134,currentCoefficient135,currentCoefficient136,currentCoefficient137,currentCoefficient138,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_58 (j : Fin 79) :
    primalCurrentPoint 58 j = currentRow58 j := rfl

theorem actual_scalar_row_58 (dual : Bool) :
    scalarRow dual 58 = (1518632850854277/6768386327350000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_58]
  rw [scalar_read_58]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_58,actual_scalar_entry_7_58,actual_scalar_entry_10_58,actual_scalar_entry_11_58,actual_scalar_entry_42_58,actual_scalar_entry_43_58,actual_scalar_entry_46_58,actual_scalar_entry_47_58,actual_scalar_entry_48_58,actual_scalar_entry_50_58,actual_scalar_entry_52_58,actual_scalar_entry_53_58,actual_scalar_entry_54_58,actual_scalar_entry_57_58,actual_scalar_entry_58_6,actual_scalar_entry_58_7,actual_scalar_entry_58_10,actual_scalar_entry_58_11,actual_scalar_entry_58_42,actual_scalar_entry_58_43,actual_scalar_entry_58_46,actual_scalar_entry_58_47,actual_scalar_entry_58_48,actual_scalar_entry_58_50,actual_scalar_entry_58_52,actual_scalar_entry_58_53,actual_scalar_entry_58_54,actual_scalar_entry_58_57,actual_scalar_entry_58_58,actual_scalar_entry_58_66,actual_scalar_entry_66_58,currentCoefficient6,currentCoefficient7,currentCoefficient17,currentCoefficient52,currentCoefficient53,currentCoefficient74,currentCoefficient84,currentCoefficient86,currentCoefficient98,currentCoefficient110,currentCoefficient135,currentCoefficient139,currentCoefficient140,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_60 (j : Fin 79) :
    primalCurrentPoint 60 j = currentRow60 j := rfl

theorem actual_scalar_row_60 (dual : Bool) :
    scalarRow dual 60 = (306197519224239/6768386327350000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_60]
  rw [scalar_read_60]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_60,actual_scalar_entry_10_60,actual_scalar_entry_11_60,actual_scalar_entry_42_60,actual_scalar_entry_46_60,actual_scalar_entry_47_60,actual_scalar_entry_48_60,actual_scalar_entry_50_60,actual_scalar_entry_53_60,actual_scalar_entry_54_60,actual_scalar_entry_57_60,actual_scalar_entry_60_6,actual_scalar_entry_60_10,actual_scalar_entry_60_11,actual_scalar_entry_60_42,actual_scalar_entry_60_46,actual_scalar_entry_60_47,actual_scalar_entry_60_48,actual_scalar_entry_60_50,actual_scalar_entry_60_53,actual_scalar_entry_60_54,actual_scalar_entry_60_57,currentCoefficient6,currentCoefficient7,currentCoefficient52,currentCoefficient53,currentCoefficient85,currentCoefficient86,currentCoefficient137,currentCoefficient141,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_61 (j : Fin 79) :
    primalCurrentPoint 61 j = currentRow61 j := rfl

theorem actual_scalar_row_61 (dual : Bool) :
    scalarRow dual 61 = (7030536703911/33841931636750 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_61]
  rw [scalar_read_61]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_61,actual_scalar_entry_19_61,actual_scalar_entry_22_61,actual_scalar_entry_30_61,actual_scalar_entry_31_61,actual_scalar_entry_34_61,actual_scalar_entry_35_61,actual_scalar_entry_55_61,actual_scalar_entry_56_61,actual_scalar_entry_61_18,actual_scalar_entry_61_19,actual_scalar_entry_61_22,actual_scalar_entry_61_30,actual_scalar_entry_61_31,actual_scalar_entry_61_34,actual_scalar_entry_61_35,actual_scalar_entry_61_55,actual_scalar_entry_61_56,actual_scalar_entry_61_61,actual_scalar_entry_61_63,actual_scalar_entry_61_67,actual_scalar_entry_63_61,actual_scalar_entry_67_61,currentCoefficient38,currentCoefficient41,currentCoefficient47,currentCoefficient52,currentCoefficient55,currentCoefficient120,currentCoefficient122,currentCoefficient142,currentCoefficient143,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_63 (j : Fin 79) :
    primalCurrentPoint 63 j = currentRow63 j := rfl

theorem actual_scalar_row_63 (dual : Bool) :
    scalarRow dual 63 = (29117323902519/135367726547000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_63]
  rw [scalar_read_63]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_63,actual_scalar_entry_19_63,actual_scalar_entry_22_63,actual_scalar_entry_30_63,actual_scalar_entry_31_63,actual_scalar_entry_34_63,actual_scalar_entry_35_63,actual_scalar_entry_55_63,actual_scalar_entry_56_63,actual_scalar_entry_61_63,actual_scalar_entry_63_18,actual_scalar_entry_63_19,actual_scalar_entry_63_22,actual_scalar_entry_63_30,actual_scalar_entry_63_31,actual_scalar_entry_63_34,actual_scalar_entry_63_35,actual_scalar_entry_63_55,actual_scalar_entry_63_56,actual_scalar_entry_63_61,actual_scalar_entry_63_63,actual_scalar_entry_63_67,actual_scalar_entry_67_63,currentCoefficient38,currentCoefficient41,currentCoefficient47,currentCoefficient52,currentCoefficient55,currentCoefficient120,currentCoefficient122,currentCoefficient142,currentCoefficient143,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_64 (j : Fin 79) :
    primalCurrentPoint 64 j = currentRow64 j := rfl

theorem actual_scalar_row_64 (dual : Bool) :
    scalarRow dual 64 = (-88506405025461/6768386327350000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_64]
  rw [scalar_read_64]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_64,actual_scalar_entry_10_64,actual_scalar_entry_11_64,actual_scalar_entry_42_64,actual_scalar_entry_46_64,actual_scalar_entry_47_64,actual_scalar_entry_48_64,actual_scalar_entry_50_64,actual_scalar_entry_53_64,actual_scalar_entry_54_64,actual_scalar_entry_57_64,actual_scalar_entry_64_6,actual_scalar_entry_64_10,actual_scalar_entry_64_11,actual_scalar_entry_64_42,actual_scalar_entry_64_46,actual_scalar_entry_64_47,actual_scalar_entry_64_48,actual_scalar_entry_64_50,actual_scalar_entry_64_53,actual_scalar_entry_64_54,actual_scalar_entry_64_57,currentCoefficient6,currentCoefficient7,currentCoefficient52,currentCoefficient53,currentCoefficient85,currentCoefficient86,currentCoefficient136,currentCoefficient144,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_66 (j : Fin 79) :
    primalCurrentPoint 66 j = currentRow66 j := rfl

theorem actual_scalar_row_66 (dual : Bool) :
    scalarRow dual 66 = (1486075050531477/6768386327350000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_66]
  rw [scalar_read_66]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_6_66,actual_scalar_entry_7_66,actual_scalar_entry_10_66,actual_scalar_entry_11_66,actual_scalar_entry_42_66,actual_scalar_entry_43_66,actual_scalar_entry_46_66,actual_scalar_entry_47_66,actual_scalar_entry_48_66,actual_scalar_entry_50_66,actual_scalar_entry_52_66,actual_scalar_entry_53_66,actual_scalar_entry_54_66,actual_scalar_entry_57_66,actual_scalar_entry_58_66,actual_scalar_entry_66_6,actual_scalar_entry_66_7,actual_scalar_entry_66_10,actual_scalar_entry_66_11,actual_scalar_entry_66_42,actual_scalar_entry_66_43,actual_scalar_entry_66_46,actual_scalar_entry_66_47,actual_scalar_entry_66_48,actual_scalar_entry_66_50,actual_scalar_entry_66_52,actual_scalar_entry_66_53,actual_scalar_entry_66_54,actual_scalar_entry_66_57,actual_scalar_entry_66_58,actual_scalar_entry_66_66,currentCoefficient6,currentCoefficient7,currentCoefficient18,currentCoefficient52,currentCoefficient53,currentCoefficient75,currentCoefficient85,currentCoefficient87,currentCoefficient101,currentCoefficient109,currentCoefficient138,currentCoefficient139,currentCoefficient140,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_67 (j : Fin 79) :
    primalCurrentPoint 67 j = currentRow67 j := rfl

theorem actual_scalar_row_67 (dual : Bool) :
    scalarRow dual 67 = (12834886509/3301651867000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_67]
  rw [scalar_read_67]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_67,actual_scalar_entry_19_67,actual_scalar_entry_22_67,actual_scalar_entry_30_67,actual_scalar_entry_31_67,actual_scalar_entry_34_67,actual_scalar_entry_35_67,actual_scalar_entry_55_67,actual_scalar_entry_56_67,actual_scalar_entry_61_67,actual_scalar_entry_63_67,actual_scalar_entry_67_18,actual_scalar_entry_67_19,actual_scalar_entry_67_22,actual_scalar_entry_67_30,actual_scalar_entry_67_31,actual_scalar_entry_67_34,actual_scalar_entry_67_35,actual_scalar_entry_67_55,actual_scalar_entry_67_56,actual_scalar_entry_67_61,actual_scalar_entry_67_63,actual_scalar_entry_67_67,currentCoefficient39,currentCoefficient40,currentCoefficient48,currentCoefficient53,currentCoefficient54,currentCoefficient121,currentCoefficient123,currentCoefficient142,currentCoefficient143,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_71 (j : Fin 79) :
    primalCurrentPoint 71 j = currentRow71 j := rfl

theorem actual_scalar_row_71 (dual : Bool) :
    scalarRow dual 71 = (7030536703911/33841931636750 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_71]
  rw [scalar_read_71]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_71,actual_scalar_entry_19_71,actual_scalar_entry_22_71,actual_scalar_entry_23_71,actual_scalar_entry_30_71,actual_scalar_entry_31_71,actual_scalar_entry_34_71,actual_scalar_entry_55_71,actual_scalar_entry_56_71,actual_scalar_entry_71_18,actual_scalar_entry_71_19,actual_scalar_entry_71_22,actual_scalar_entry_71_23,actual_scalar_entry_71_30,actual_scalar_entry_71_31,actual_scalar_entry_71_34,actual_scalar_entry_71_55,actual_scalar_entry_71_56,actual_scalar_entry_71_71,actual_scalar_entry_71_73,actual_scalar_entry_71_77,actual_scalar_entry_73_71,actual_scalar_entry_77_71,currentCoefficient38,currentCoefficient40,currentCoefficient47,currentCoefficient52,currentCoefficient54,currentCoefficient120,currentCoefficient123,currentCoefficient142,currentCoefficient143,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_73 (j : Fin 79) :
    primalCurrentPoint 73 j = currentRow73 j := rfl

theorem actual_scalar_row_73 (dual : Bool) :
    scalarRow dual 73 = (29117323902519/135367726547000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_73]
  rw [scalar_read_73]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_73,actual_scalar_entry_19_73,actual_scalar_entry_22_73,actual_scalar_entry_23_73,actual_scalar_entry_30_73,actual_scalar_entry_31_73,actual_scalar_entry_34_73,actual_scalar_entry_55_73,actual_scalar_entry_56_73,actual_scalar_entry_71_73,actual_scalar_entry_73_18,actual_scalar_entry_73_19,actual_scalar_entry_73_22,actual_scalar_entry_73_23,actual_scalar_entry_73_30,actual_scalar_entry_73_31,actual_scalar_entry_73_34,actual_scalar_entry_73_55,actual_scalar_entry_73_56,actual_scalar_entry_73_71,actual_scalar_entry_73_73,actual_scalar_entry_73_77,actual_scalar_entry_77_73,currentCoefficient39,currentCoefficient41,currentCoefficient48,currentCoefficient53,currentCoefficient55,currentCoefficient121,currentCoefficient122,currentCoefficient142,currentCoefficient143,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_77 (j : Fin 79) :
    primalCurrentPoint 77 j = currentRow77 j := rfl

theorem actual_scalar_row_77 (dual : Bool) :
    scalarRow dual 77 = (12834886509/3301651867000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_77]
  rw [scalar_read_77]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_77,actual_scalar_entry_19_77,actual_scalar_entry_22_77,actual_scalar_entry_23_77,actual_scalar_entry_30_77,actual_scalar_entry_31_77,actual_scalar_entry_34_77,actual_scalar_entry_55_77,actual_scalar_entry_56_77,actual_scalar_entry_71_77,actual_scalar_entry_73_77,actual_scalar_entry_77_18,actual_scalar_entry_77_19,actual_scalar_entry_77_22,actual_scalar_entry_77_23,actual_scalar_entry_77_30,actual_scalar_entry_77_31,actual_scalar_entry_77_34,actual_scalar_entry_77_55,actual_scalar_entry_77_56,actual_scalar_entry_77_71,actual_scalar_entry_77_73,actual_scalar_entry_77_77,currentCoefficient39,currentCoefficient41,currentCoefficient48,currentCoefficient53,currentCoefficient55,currentCoefficient121,currentCoefficient122,currentCoefficient142,currentCoefficient143,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring


end LowEnergy.ActualCanonical79Imaginary
