import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79SourceSparseData
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

private theorem schema0 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 0 a = if a = 9 then v 0 else 0 := by
  fin_cases a <;> rfl

private theorem fields0 (s : Fin 8) :
    sourceField 0 s = (![9,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights0 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 0 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row0 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 0 a = sourceSparseRow v 0 a := by
  rw [schema0]
  simp only [sourceSparseRow,fields0,weights0,Fin.sum_univ_succ]
  simp [eq_comm]

end LowEnergy.ActualCanonical79Imaginary
