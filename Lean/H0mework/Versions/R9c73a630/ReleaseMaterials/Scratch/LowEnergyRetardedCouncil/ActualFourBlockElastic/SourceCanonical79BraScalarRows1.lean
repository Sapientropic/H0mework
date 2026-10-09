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

private theorem scalar_delta_18 (j : Fin 79) :
    currentRow18 j = (if j = (19 : Fin 79) then currentCoefficient34 else 0) + (if j = (23 : Fin 79) then currentCoefficient34 else 0) + (if j = (31 : Fin 79) then currentCoefficient37 else 0) + (if j = (35 : Fin 79) then currentCoefficient37 else 0) + (if j = (55 : Fin 79) then currentCoefficient35 else 0) + (if j = (56 : Fin 79) then currentCoefficient36 else 0) + (if j = (61 : Fin 79) then currentCoefficient38 else 0) + (if j = (63 : Fin 79) then currentCoefficient38 else 0) + (if j = (67 : Fin 79) then currentCoefficient39 else 0) + (if j = (71 : Fin 79) then currentCoefficient40 else 0) + (if j = (73 : Fin 79) then currentCoefficient41 else 0) + (if j = (77 : Fin 79) then currentCoefficient41 else 0) := by
  fin_cases j <;> norm_num [currentRow18,Fin.ext_iff]

theorem scalar_read_18 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow18 j)) = f 19 * σ currentCoefficient34 + f 23 * σ currentCoefficient34 + f 31 * σ currentCoefficient37 + f 35 * σ currentCoefficient37 + f 55 * σ currentCoefficient35 + f 56 * σ currentCoefficient36 + f 61 * σ currentCoefficient38 + f 63 * σ currentCoefficient38 + f 67 * σ currentCoefficient39 + f 71 * σ currentCoefficient40 + f 73 * σ currentCoefficient41 + f 77 * σ currentCoefficient41 := by
  simp_rw [scalar_delta_18]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_19 (j : Fin 79) :
    currentRow19 j = (if j = (18 : Fin 79) then currentCoefficient34 else 0) + (if j = (19 : Fin 79) then currentCoefficient32 else 0) + (if j = (22 : Fin 79) then currentCoefficient30 else 0) + (if j = (23 : Fin 79) then currentCoefficient34 else 0) + (if j = (30 : Fin 79) then currentCoefficient42 else 0) + (if j = (34 : Fin 79) then currentCoefficient43 else 0) + (if j = (35 : Fin 79) then currentCoefficient44 else 0) + (if j = (55 : Fin 79) then currentCoefficient45 else 0) + (if j = (56 : Fin 79) then currentCoefficient46 else 0) + (if j = (61 : Fin 79) then currentCoefficient47 else 0) + (if j = (63 : Fin 79) then currentCoefficient47 else 0) + (if j = (67 : Fin 79) then currentCoefficient48 else 0) + (if j = (71 : Fin 79) then currentCoefficient40 else 0) + (if j = (73 : Fin 79) then currentCoefficient41 else 0) + (if j = (77 : Fin 79) then currentCoefficient41 else 0) := by
  fin_cases j <;> norm_num [currentRow19,Fin.ext_iff]

theorem scalar_read_19 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow19 j)) = f 18 * σ currentCoefficient34 + f 19 * σ currentCoefficient32 + f 22 * σ currentCoefficient30 + f 23 * σ currentCoefficient34 + f 30 * σ currentCoefficient42 + f 34 * σ currentCoefficient43 + f 35 * σ currentCoefficient44 + f 55 * σ currentCoefficient45 + f 56 * σ currentCoefficient46 + f 61 * σ currentCoefficient47 + f 63 * σ currentCoefficient47 + f 67 * σ currentCoefficient48 + f 71 * σ currentCoefficient40 + f 73 * σ currentCoefficient41 + f 77 * σ currentCoefficient41 := by
  simp_rw [scalar_delta_19]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_22 (j : Fin 79) :
    currentRow22 j = (if j = (19 : Fin 79) then currentCoefficient30 else 0) + (if j = (23 : Fin 79) then currentCoefficient30 else 0) + (if j = (31 : Fin 79) then currentCoefficient51 else 0) + (if j = (35 : Fin 79) then currentCoefficient51 else 0) + (if j = (55 : Fin 79) then currentCoefficient49 else 0) + (if j = (56 : Fin 79) then currentCoefficient50 else 0) + (if j = (61 : Fin 79) then currentCoefficient52 else 0) + (if j = (63 : Fin 79) then currentCoefficient52 else 0) + (if j = (67 : Fin 79) then currentCoefficient53 else 0) + (if j = (71 : Fin 79) then currentCoefficient54 else 0) + (if j = (73 : Fin 79) then currentCoefficient55 else 0) + (if j = (77 : Fin 79) then currentCoefficient55 else 0) := by
  fin_cases j <;> norm_num [currentRow22,Fin.ext_iff]

theorem scalar_read_22 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow22 j)) = f 19 * σ currentCoefficient30 + f 23 * σ currentCoefficient30 + f 31 * σ currentCoefficient51 + f 35 * σ currentCoefficient51 + f 55 * σ currentCoefficient49 + f 56 * σ currentCoefficient50 + f 61 * σ currentCoefficient52 + f 63 * σ currentCoefficient52 + f 67 * σ currentCoefficient53 + f 71 * σ currentCoefficient54 + f 73 * σ currentCoefficient55 + f 77 * σ currentCoefficient55 := by
  simp_rw [scalar_delta_22]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_23 (j : Fin 79) :
    currentRow23 j = (if j = (18 : Fin 79) then currentCoefficient34 else 0) + (if j = (19 : Fin 79) then currentCoefficient34 else 0) + (if j = (22 : Fin 79) then currentCoefficient30 else 0) + (if j = (23 : Fin 79) then currentCoefficient30 else 0) + (if j = (30 : Fin 79) then currentCoefficient42 else 0) + (if j = (31 : Fin 79) then currentCoefficient58 else 0) + (if j = (34 : Fin 79) then currentCoefficient43 else 0) + (if j = (55 : Fin 79) then currentCoefficient56 else 0) + (if j = (56 : Fin 79) then currentCoefficient57 else 0) + (if j = (71 : Fin 79) then currentCoefficient54 else 0) + (if j = (73 : Fin 79) then currentCoefficient55 else 0) + (if j = (77 : Fin 79) then currentCoefficient55 else 0) := by
  fin_cases j <;> norm_num [currentRow23,Fin.ext_iff]

theorem scalar_read_23 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow23 j)) = f 18 * σ currentCoefficient34 + f 19 * σ currentCoefficient34 + f 22 * σ currentCoefficient30 + f 23 * σ currentCoefficient30 + f 30 * σ currentCoefficient42 + f 31 * σ currentCoefficient58 + f 34 * σ currentCoefficient43 + f 55 * σ currentCoefficient56 + f 56 * σ currentCoefficient57 + f 71 * σ currentCoefficient54 + f 73 * σ currentCoefficient55 + f 77 * σ currentCoefficient55 := by
  simp_rw [scalar_delta_23]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_24 (j : Fin 79) :
    currentRow24 j = (if j = (13 : Fin 79) then currentCoefficient30 else 0) + (if j = (24 : Fin 79) then currentCoefficient28 else 0) + (if j = (50 : Fin 79) then currentCoefficient31 else 0) + (if j = (53 : Fin 79) then currentCoefficient29 else 0) := by
  fin_cases j <;> norm_num [currentRow24,Fin.ext_iff]

theorem scalar_read_24 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow24 j)) = f 13 * σ currentCoefficient30 + f 24 * σ currentCoefficient28 + f 50 * σ currentCoefficient31 + f 53 * σ currentCoefficient29 := by
  simp_rw [scalar_delta_24]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_25 (j : Fin 79) :
    currentRow25 j = (if j = (12 : Fin 79) then currentCoefficient28 else 0) + (if j = (25 : Fin 79) then currentCoefficient28 else 0) + (if j = (52 : Fin 79) then currentCoefficient29 else 0) := by
  fin_cases j <;> norm_num [currentRow25,Fin.ext_iff]

theorem scalar_read_25 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow25 j)) = f 12 * σ currentCoefficient28 + f 25 * σ currentCoefficient28 + f 52 * σ currentCoefficient29 := by
  simp_rw [scalar_delta_25]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_28 (j : Fin 79) :
    currentRow28 j = (if j = (17 : Fin 79) then currentCoefficient32 else 0) + (if j = (28 : Fin 79) then currentCoefficient32 else 0) := by
  fin_cases j <;> norm_num [currentRow28,Fin.ext_iff]

theorem scalar_read_28 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow28 j)) = f 17 * σ currentCoefficient32 + f 28 * σ currentCoefficient32 := by
  simp_rw [scalar_delta_28]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_29 (j : Fin 79) :
    currentRow29 j = (if j = (16 : Fin 79) then currentCoefficient33 else 0) + (if j = (29 : Fin 79) then currentCoefficient32 else 0) := by
  fin_cases j <;> norm_num [currentRow29,Fin.ext_iff]

theorem scalar_read_29 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow29 j)) = f 16 * σ currentCoefficient33 + f 29 * σ currentCoefficient32 := by
  simp_rw [scalar_delta_29]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_30 (j : Fin 79) :
    currentRow30 j = (if j = (19 : Fin 79) then currentCoefficient42 else 0) + (if j = (23 : Fin 79) then currentCoefficient42 else 0) + (if j = (31 : Fin 79) then currentCoefficient34 else 0) + (if j = (35 : Fin 79) then currentCoefficient34 else 0) + (if j = (55 : Fin 79) then currentCoefficient59 else 0) + (if j = (56 : Fin 79) then currentCoefficient35 else 0) + (if j = (61 : Fin 79) then currentCoefficient41 else 0) + (if j = (63 : Fin 79) then currentCoefficient41 else 0) + (if j = (67 : Fin 79) then currentCoefficient40 else 0) + (if j = (71 : Fin 79) then currentCoefficient38 else 0) + (if j = (73 : Fin 79) then currentCoefficient39 else 0) + (if j = (77 : Fin 79) then currentCoefficient39 else 0) := by
  fin_cases j <;> norm_num [currentRow30,Fin.ext_iff]

theorem scalar_read_30 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow30 j)) = f 19 * σ currentCoefficient42 + f 23 * σ currentCoefficient42 + f 31 * σ currentCoefficient34 + f 35 * σ currentCoefficient34 + f 55 * σ currentCoefficient59 + f 56 * σ currentCoefficient35 + f 61 * σ currentCoefficient41 + f 63 * σ currentCoefficient41 + f 67 * σ currentCoefficient40 + f 71 * σ currentCoefficient38 + f 73 * σ currentCoefficient39 + f 77 * σ currentCoefficient39 := by
  simp_rw [scalar_delta_30]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_31 (j : Fin 79) :
    currentRow31 j = (if j = (18 : Fin 79) then currentCoefficient37 else 0) + (if j = (22 : Fin 79) then currentCoefficient51 else 0) + (if j = (23 : Fin 79) then currentCoefficient58 else 0) + (if j = (30 : Fin 79) then currentCoefficient34 else 0) + (if j = (31 : Fin 79) then currentCoefficient32 else 0) + (if j = (34 : Fin 79) then currentCoefficient30 else 0) + (if j = (35 : Fin 79) then currentCoefficient34 else 0) + (if j = (55 : Fin 79) then currentCoefficient60 else 0) + (if j = (56 : Fin 79) then currentCoefficient45 else 0) + (if j = (61 : Fin 79) then currentCoefficient41 else 0) + (if j = (63 : Fin 79) then currentCoefficient41 else 0) + (if j = (67 : Fin 79) then currentCoefficient40 else 0) + (if j = (71 : Fin 79) then currentCoefficient47 else 0) + (if j = (73 : Fin 79) then currentCoefficient48 else 0) + (if j = (77 : Fin 79) then currentCoefficient48 else 0) := by
  fin_cases j <;> norm_num [currentRow31,Fin.ext_iff]

theorem scalar_read_31 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow31 j)) = f 18 * σ currentCoefficient37 + f 22 * σ currentCoefficient51 + f 23 * σ currentCoefficient58 + f 30 * σ currentCoefficient34 + f 31 * σ currentCoefficient32 + f 34 * σ currentCoefficient30 + f 35 * σ currentCoefficient34 + f 55 * σ currentCoefficient60 + f 56 * σ currentCoefficient45 + f 61 * σ currentCoefficient41 + f 63 * σ currentCoefficient41 + f 67 * σ currentCoefficient40 + f 71 * σ currentCoefficient47 + f 73 * σ currentCoefficient48 + f 77 * σ currentCoefficient48 := by
  simp_rw [scalar_delta_31]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_34 (j : Fin 79) :
    currentRow34 j = (if j = (19 : Fin 79) then currentCoefficient43 else 0) + (if j = (23 : Fin 79) then currentCoefficient43 else 0) + (if j = (31 : Fin 79) then currentCoefficient30 else 0) + (if j = (35 : Fin 79) then currentCoefficient30 else 0) + (if j = (55 : Fin 79) then currentCoefficient61 else 0) + (if j = (56 : Fin 79) then currentCoefficient49 else 0) + (if j = (61 : Fin 79) then currentCoefficient55 else 0) + (if j = (63 : Fin 79) then currentCoefficient55 else 0) + (if j = (67 : Fin 79) then currentCoefficient54 else 0) + (if j = (71 : Fin 79) then currentCoefficient52 else 0) + (if j = (73 : Fin 79) then currentCoefficient53 else 0) + (if j = (77 : Fin 79) then currentCoefficient53 else 0) := by
  fin_cases j <;> norm_num [currentRow34,Fin.ext_iff]

theorem scalar_read_34 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow34 j)) = f 19 * σ currentCoefficient43 + f 23 * σ currentCoefficient43 + f 31 * σ currentCoefficient30 + f 35 * σ currentCoefficient30 + f 55 * σ currentCoefficient61 + f 56 * σ currentCoefficient49 + f 61 * σ currentCoefficient55 + f 63 * σ currentCoefficient55 + f 67 * σ currentCoefficient54 + f 71 * σ currentCoefficient52 + f 73 * σ currentCoefficient53 + f 77 * σ currentCoefficient53 := by
  simp_rw [scalar_delta_34]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_35 (j : Fin 79) :
    currentRow35 j = (if j = (18 : Fin 79) then currentCoefficient37 else 0) + (if j = (19 : Fin 79) then currentCoefficient44 else 0) + (if j = (22 : Fin 79) then currentCoefficient51 else 0) + (if j = (30 : Fin 79) then currentCoefficient34 else 0) + (if j = (31 : Fin 79) then currentCoefficient34 else 0) + (if j = (34 : Fin 79) then currentCoefficient30 else 0) + (if j = (35 : Fin 79) then currentCoefficient30 else 0) + (if j = (55 : Fin 79) then currentCoefficient62 else 0) + (if j = (56 : Fin 79) then currentCoefficient56 else 0) + (if j = (61 : Fin 79) then currentCoefficient55 else 0) + (if j = (63 : Fin 79) then currentCoefficient55 else 0) + (if j = (67 : Fin 79) then currentCoefficient54 else 0) := by
  fin_cases j <;> norm_num [currentRow35,Fin.ext_iff]

theorem scalar_read_35 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow35 j)) = f 18 * σ currentCoefficient37 + f 19 * σ currentCoefficient44 + f 22 * σ currentCoefficient51 + f 30 * σ currentCoefficient34 + f 31 * σ currentCoefficient34 + f 34 * σ currentCoefficient30 + f 35 * σ currentCoefficient30 + f 55 * σ currentCoefficient62 + f 56 * σ currentCoefficient56 + f 61 * σ currentCoefficient55 + f 63 * σ currentCoefficient55 + f 67 * σ currentCoefficient54 := by
  simp_rw [scalar_delta_35]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_36 (j : Fin 79) :
    currentRow36 j = (if j = (1 : Fin 79) then currentCoefficient3 else 0) + (if j = (36 : Fin 79) then currentCoefficient30 else 0) + (if j = (49 : Fin 79) then currentCoefficient63 else 0) := by
  fin_cases j <;> norm_num [currentRow36,Fin.ext_iff]

theorem scalar_read_36 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow36 j)) = f 1 * σ currentCoefficient3 + f 36 * σ currentCoefficient30 + f 49 * σ currentCoefficient63 := by
  simp_rw [scalar_delta_36]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]

private theorem scalar_delta_37 (j : Fin 79) :
    currentRow37 j = (if j = (0 : Fin 79) then currentCoefficient2 else 0) + (if j = (37 : Fin 79) then currentCoefficient30 else 0) + (if j = (51 : Fin 79) then currentCoefficient64 else 0) := by
  fin_cases j <;> norm_num [currentRow37,Fin.ext_iff]

theorem scalar_read_37 (f : Fin 79 → ℂ) (σ : ℂ →+* ℂ) :
    (∑j : Fin 79,f j * σ (currentRow37 j)) = f 0 * σ currentCoefficient2 + f 37 * σ currentCoefficient30 + f 51 * σ currentCoefficient64 := by
  simp_rw [scalar_delta_37]
  simp only [map_add,scalar_read_map_ite]
  simp [mul_add,mul_ite,Finset.sum_add_distrib]


private theorem scalar_primal_row_18 (j : Fin 79) :
    primalCurrentPoint 18 j = currentRow18 j := rfl

theorem actual_scalar_row_18 (dual : Bool) :
    scalarRow dual 18 = (-15699977499658851/173997053390900000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_18]
  rw [scalar_read_18]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_19,actual_scalar_entry_18_23,actual_scalar_entry_18_31,actual_scalar_entry_18_35,actual_scalar_entry_18_55,actual_scalar_entry_18_56,actual_scalar_entry_18_61,actual_scalar_entry_18_63,actual_scalar_entry_18_67,actual_scalar_entry_18_71,actual_scalar_entry_18_73,actual_scalar_entry_18_77,actual_scalar_entry_19_18,actual_scalar_entry_23_18,actual_scalar_entry_31_18,actual_scalar_entry_35_18,actual_scalar_entry_55_18,actual_scalar_entry_56_18,actual_scalar_entry_61_18,actual_scalar_entry_63_18,actual_scalar_entry_67_18,actual_scalar_entry_71_18,actual_scalar_entry_73_18,actual_scalar_entry_77_18,currentCoefficient34,currentCoefficient35,currentCoefficient36,currentCoefficient37,currentCoefficient38,currentCoefficient39,currentCoefficient40,currentCoefficient41,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_19 (j : Fin 79) :
    primalCurrentPoint 19 j = currentRow19 j := rfl

theorem actual_scalar_row_19 (dual : Bool) :
    scalarRow dual 19 = (1412174414989630953/7133879189026900000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_19]
  rw [scalar_read_19]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_19,actual_scalar_entry_19_18,actual_scalar_entry_19_19,actual_scalar_entry_19_22,actual_scalar_entry_19_23,actual_scalar_entry_19_30,actual_scalar_entry_19_34,actual_scalar_entry_19_35,actual_scalar_entry_19_55,actual_scalar_entry_19_56,actual_scalar_entry_19_61,actual_scalar_entry_19_63,actual_scalar_entry_19_67,actual_scalar_entry_19_71,actual_scalar_entry_19_73,actual_scalar_entry_19_77,actual_scalar_entry_22_19,actual_scalar_entry_23_19,actual_scalar_entry_30_19,actual_scalar_entry_34_19,actual_scalar_entry_35_19,actual_scalar_entry_55_19,actual_scalar_entry_56_19,actual_scalar_entry_61_19,actual_scalar_entry_63_19,actual_scalar_entry_67_19,actual_scalar_entry_71_19,actual_scalar_entry_73_19,actual_scalar_entry_77_19,currentCoefficient30,currentCoefficient32,currentCoefficient34,currentCoefficient40,currentCoefficient41,currentCoefficient42,currentCoefficient43,currentCoefficient44,currentCoefficient45,currentCoefficient46,currentCoefficient47,currentCoefficient48,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_22 (j : Fin 79) :
    primalCurrentPoint 22 j = currentRow22 j := rfl

theorem actual_scalar_row_22 (dual : Bool) :
    scalarRow dual 22 = (-15332625/3301651867 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_22]
  rw [scalar_read_22]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_19_22,actual_scalar_entry_22_19,actual_scalar_entry_22_23,actual_scalar_entry_22_31,actual_scalar_entry_22_35,actual_scalar_entry_22_55,actual_scalar_entry_22_56,actual_scalar_entry_22_61,actual_scalar_entry_22_63,actual_scalar_entry_22_67,actual_scalar_entry_22_71,actual_scalar_entry_22_73,actual_scalar_entry_22_77,actual_scalar_entry_23_22,actual_scalar_entry_31_22,actual_scalar_entry_35_22,actual_scalar_entry_55_22,actual_scalar_entry_56_22,actual_scalar_entry_61_22,actual_scalar_entry_63_22,actual_scalar_entry_67_22,actual_scalar_entry_71_22,actual_scalar_entry_73_22,actual_scalar_entry_77_22,currentCoefficient30,currentCoefficient49,currentCoefficient50,currentCoefficient51,currentCoefficient52,currentCoefficient53,currentCoefficient54,currentCoefficient55,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_23 (j : Fin 79) :
    primalCurrentPoint 23 j = currentRow23 j := rfl

theorem actual_scalar_row_23 (dual : Bool) :
    scalarRow dual 23 = (-175882887/6603303734 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_23]
  rw [scalar_read_23]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_23,actual_scalar_entry_19_23,actual_scalar_entry_22_23,actual_scalar_entry_23_18,actual_scalar_entry_23_19,actual_scalar_entry_23_22,actual_scalar_entry_23_23,actual_scalar_entry_23_30,actual_scalar_entry_23_31,actual_scalar_entry_23_34,actual_scalar_entry_23_55,actual_scalar_entry_23_56,actual_scalar_entry_23_71,actual_scalar_entry_23_73,actual_scalar_entry_23_77,actual_scalar_entry_30_23,actual_scalar_entry_31_23,actual_scalar_entry_34_23,actual_scalar_entry_55_23,actual_scalar_entry_56_23,actual_scalar_entry_71_23,actual_scalar_entry_73_23,actual_scalar_entry_77_23,currentCoefficient30,currentCoefficient34,currentCoefficient42,currentCoefficient43,currentCoefficient54,currentCoefficient55,currentCoefficient56,currentCoefficient57,currentCoefficient58,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_24 (j : Fin 79) :
    primalCurrentPoint 24 j = currentRow24 j := rfl

theorem actual_scalar_row_24 (dual : Bool) :
    scalarRow dual 24 = (9/1240 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_24]
  rw [scalar_read_24]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_13_24,actual_scalar_entry_24_13,actual_scalar_entry_24_24,actual_scalar_entry_24_50,actual_scalar_entry_24_53,actual_scalar_entry_50_24,actual_scalar_entry_53_24,currentCoefficient28,currentCoefficient29,currentCoefficient30,currentCoefficient31,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_25 (j : Fin 79) :
    primalCurrentPoint 25 j = currentRow25 j := rfl

theorem actual_scalar_row_25 (dual : Bool) :
    scalarRow dual 25 = (9081/775000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_25]
  rw [scalar_read_25]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_12_25,actual_scalar_entry_25_12,actual_scalar_entry_25_25,actual_scalar_entry_25_52,actual_scalar_entry_52_25,currentCoefficient28,currentCoefficient29,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_28 (j : Fin 79) :
    primalCurrentPoint 28 j = currentRow28 j := rfl

theorem actual_scalar_row_28 (dual : Bool) :
    scalarRow dual 28 = (108/2671 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_28]
  rw [scalar_read_28]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_17_28,actual_scalar_entry_28_17,actual_scalar_entry_28_28,currentCoefficient32,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_29 (j : Fin 79) :
    primalCurrentPoint 29 j = currentRow29 j := rfl

theorem actual_scalar_row_29 (dual : Bool) :
    scalarRow dual 29 = (108/2671 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_29]
  rw [scalar_read_29]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_16_29,actual_scalar_entry_29_16,actual_scalar_entry_29_29,currentCoefficient32,currentCoefficient33,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_30 (j : Fin 79) :
    primalCurrentPoint 30 j = currentRow30 j := rfl

theorem actual_scalar_row_30 (dual : Bool) :
    scalarRow dual 30 = (-15699977499658851/173997053390900000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_30]
  rw [scalar_read_30]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_19_30,actual_scalar_entry_23_30,actual_scalar_entry_30_19,actual_scalar_entry_30_23,actual_scalar_entry_30_31,actual_scalar_entry_30_35,actual_scalar_entry_30_55,actual_scalar_entry_30_56,actual_scalar_entry_30_61,actual_scalar_entry_30_63,actual_scalar_entry_30_67,actual_scalar_entry_30_71,actual_scalar_entry_30_73,actual_scalar_entry_30_77,actual_scalar_entry_31_30,actual_scalar_entry_35_30,actual_scalar_entry_55_30,actual_scalar_entry_56_30,actual_scalar_entry_61_30,actual_scalar_entry_63_30,actual_scalar_entry_67_30,actual_scalar_entry_71_30,actual_scalar_entry_73_30,actual_scalar_entry_77_30,currentCoefficient34,currentCoefficient35,currentCoefficient38,currentCoefficient39,currentCoefficient40,currentCoefficient41,currentCoefficient42,currentCoefficient59,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_31 (j : Fin 79) :
    primalCurrentPoint 31 j = currentRow31 j := rfl

theorem actual_scalar_row_31 (dual : Bool) :
    scalarRow dual 31 = (1412174414989630953/7133879189026900000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_31]
  rw [scalar_read_31]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_31,actual_scalar_entry_22_31,actual_scalar_entry_23_31,actual_scalar_entry_30_31,actual_scalar_entry_31_18,actual_scalar_entry_31_22,actual_scalar_entry_31_23,actual_scalar_entry_31_30,actual_scalar_entry_31_31,actual_scalar_entry_31_34,actual_scalar_entry_31_35,actual_scalar_entry_31_55,actual_scalar_entry_31_56,actual_scalar_entry_31_61,actual_scalar_entry_31_63,actual_scalar_entry_31_67,actual_scalar_entry_31_71,actual_scalar_entry_31_73,actual_scalar_entry_31_77,actual_scalar_entry_34_31,actual_scalar_entry_35_31,actual_scalar_entry_55_31,actual_scalar_entry_56_31,actual_scalar_entry_61_31,actual_scalar_entry_63_31,actual_scalar_entry_67_31,actual_scalar_entry_71_31,actual_scalar_entry_73_31,actual_scalar_entry_77_31,currentCoefficient30,currentCoefficient32,currentCoefficient34,currentCoefficient37,currentCoefficient40,currentCoefficient41,currentCoefficient45,currentCoefficient47,currentCoefficient48,currentCoefficient51,currentCoefficient58,currentCoefficient60,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_34 (j : Fin 79) :
    primalCurrentPoint 34 j = currentRow34 j := rfl

theorem actual_scalar_row_34 (dual : Bool) :
    scalarRow dual 34 = (-15332625/3301651867 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_34]
  rw [scalar_read_34]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_19_34,actual_scalar_entry_23_34,actual_scalar_entry_31_34,actual_scalar_entry_34_19,actual_scalar_entry_34_23,actual_scalar_entry_34_31,actual_scalar_entry_34_35,actual_scalar_entry_34_55,actual_scalar_entry_34_56,actual_scalar_entry_34_61,actual_scalar_entry_34_63,actual_scalar_entry_34_67,actual_scalar_entry_34_71,actual_scalar_entry_34_73,actual_scalar_entry_34_77,actual_scalar_entry_35_34,actual_scalar_entry_55_34,actual_scalar_entry_56_34,actual_scalar_entry_61_34,actual_scalar_entry_63_34,actual_scalar_entry_67_34,actual_scalar_entry_71_34,actual_scalar_entry_73_34,actual_scalar_entry_77_34,currentCoefficient30,currentCoefficient43,currentCoefficient49,currentCoefficient52,currentCoefficient53,currentCoefficient54,currentCoefficient55,currentCoefficient61,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_35 (j : Fin 79) :
    primalCurrentPoint 35 j = currentRow35 j := rfl

theorem actual_scalar_row_35 (dual : Bool) :
    scalarRow dual 35 = (-175882887/6603303734 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_35]
  rw [scalar_read_35]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_18_35,actual_scalar_entry_19_35,actual_scalar_entry_22_35,actual_scalar_entry_30_35,actual_scalar_entry_31_35,actual_scalar_entry_34_35,actual_scalar_entry_35_18,actual_scalar_entry_35_19,actual_scalar_entry_35_22,actual_scalar_entry_35_30,actual_scalar_entry_35_31,actual_scalar_entry_35_34,actual_scalar_entry_35_35,actual_scalar_entry_35_55,actual_scalar_entry_35_56,actual_scalar_entry_35_61,actual_scalar_entry_35_63,actual_scalar_entry_35_67,actual_scalar_entry_55_35,actual_scalar_entry_56_35,actual_scalar_entry_61_35,actual_scalar_entry_63_35,actual_scalar_entry_67_35,currentCoefficient30,currentCoefficient34,currentCoefficient37,currentCoefficient44,currentCoefficient51,currentCoefficient54,currentCoefficient55,currentCoefficient56,currentCoefficient62,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_36 (j : Fin 79) :
    primalCurrentPoint 36 j = currentRow36 j := rfl

theorem actual_scalar_row_36 (dual : Bool) :
    scalarRow dual 36 = (1800259882262973/209819976147850000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_36]
  rw [scalar_read_36]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_1_36,actual_scalar_entry_36_1,actual_scalar_entry_36_36,actual_scalar_entry_36_49,actual_scalar_entry_49_36,currentCoefficient3,currentCoefficient30,currentCoefficient63,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

private theorem scalar_primal_row_37 (j : Fin 79) :
    primalCurrentPoint 37 j = currentRow37 j := rfl

theorem actual_scalar_row_37 (dual : Bool) :
    scalarRow dual 37 = (1800259882262973/209819976147850000 : ℂ)/(lapse : ℂ) := by
  unfold scalarRow
  simp only [scalar_primal_row_37]
  rw [scalar_read_37]
  cases dual <;> norm_num [scalarBranch,scalarInverse,actual_scalar_entry_0_37,actual_scalar_entry_37_0,actual_scalar_entry_37_37,actual_scalar_entry_37_51,actual_scalar_entry_51_37,currentCoefficient2,currentCoefficient30,currentCoefficient64,scalar_star_nat,scalar_star_ofNat]
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring


end LowEnergy.ActualCanonical79Imaginary
