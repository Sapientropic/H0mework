import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79SourceSparsePilot
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

private def schemaRow16 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 25 => v 0
  | _ => 0

private theorem schema16 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 16 a = schemaRow16 v a := by
  fin_cases a <;> rfl

private theorem fields16 (s : Fin 8) :
    sourceField 16 s = (![25,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights16 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 16 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row16 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 16 a = sourceSparseRow v 16 a := by
  rw [schema16]
  simp only [sourceSparseRow,fields16,weights16,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow16]

private def schemaRow17 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 26 => v 0
  | _ => 0

private theorem schema17 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 17 a = schemaRow17 v a := by
  fin_cases a <;> rfl

private theorem fields17 (s : Fin 8) :
    sourceField 17 s = (![26,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights17 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 17 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row17 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 17 a = sourceSparseRow v 17 a := by
  rw [schema17]
  simp only [sourceSparseRow,fields17,weights17,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow17]

private def schemaRow18 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 27 => v 0
  | _ => 0

private theorem schema18 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 18 a = schemaRow18 v a := by
  fin_cases a <;> rfl

private theorem fields18 (s : Fin 8) :
    sourceField 18 s = (![27,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights18 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 18 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row18 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 18 a = sourceSparseRow v 18 a := by
  rw [schema18]
  simp only [sourceSparseRow,fields18,weights18,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow18]

private def schemaRow19 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 28 => v 0
  | _ => 0

private theorem schema19 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 19 a = schemaRow19 v a := by
  fin_cases a <;> rfl

private theorem fields19 (s : Fin 8) :
    sourceField 19 s = (![28,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights19 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 19 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row19 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 19 a = sourceSparseRow v 19 a := by
  rw [schema19]
  simp only [sourceSparseRow,fields19,weights19,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow19]

private def schemaRow20 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 29 => v 0
  | _ => 0

private theorem schema20 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 20 a = schemaRow20 v a := by
  fin_cases a <;> rfl

private theorem fields20 (s : Fin 8) :
    sourceField 20 s = (![29,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights20 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 20 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row20 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 20 a = sourceSparseRow v 20 a := by
  rw [schema20]
  simp only [sourceSparseRow,fields20,weights20,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow20]

private def schemaRow21 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 30 => v 0
  | _ => 0

private theorem schema21 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 21 a = schemaRow21 v a := by
  fin_cases a <;> rfl

private theorem fields21 (s : Fin 8) :
    sourceField 21 s = (![30,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights21 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 21 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row21 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 21 a = sourceSparseRow v 21 a := by
  rw [schema21]
  simp only [sourceSparseRow,fields21,weights21,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow21]

private def schemaRow22 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 31 => v 0
  | _ => 0

private theorem schema22 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 22 a = schemaRow22 v a := by
  fin_cases a <;> rfl

private theorem fields22 (s : Fin 8) :
    sourceField 22 s = (![31,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights22 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 22 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row22 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 22 a = sourceSparseRow v 22 a := by
  rw [schema22]
  simp only [sourceSparseRow,fields22,weights22,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow22]

private def schemaRow23 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 32 => v 0
  | _ => 0

private theorem schema23 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 23 a = schemaRow23 v a := by
  fin_cases a <;> rfl

private theorem fields23 (s : Fin 8) :
    sourceField 23 s = (![32,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights23 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 23 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row23 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 23 a = sourceSparseRow v 23 a := by
  rw [schema23]
  simp only [sourceSparseRow,fields23,weights23,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow23]

private def schemaRow24 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 33 => v 0
  | _ => 0

private theorem schema24 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 24 a = schemaRow24 v a := by
  fin_cases a <;> rfl

private theorem fields24 (s : Fin 8) :
    sourceField 24 s = (![33,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights24 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 24 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row24 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 24 a = sourceSparseRow v 24 a := by
  rw [schema24]
  simp only [sourceSparseRow,fields24,weights24,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow24]

private def schemaRow25 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 34 => v 0
  | _ => 0

private theorem schema25 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 25 a = schemaRow25 v a := by
  fin_cases a <;> rfl

private theorem fields25 (s : Fin 8) :
    sourceField 25 s = (![34,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights25 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 25 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row25 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 25 a = sourceSparseRow v 25 a := by
  rw [schema25]
  simp only [sourceSparseRow,fields25,weights25,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow25]

private def schemaRow26 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 35 => v 0
  | _ => 0

private theorem schema26 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 26 a = schemaRow26 v a := by
  fin_cases a <;> rfl

private theorem fields26 (s : Fin 8) :
    sourceField 26 s = (![35,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights26 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 26 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row26 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 26 a = sourceSparseRow v 26 a := by
  rw [schema26]
  simp only [sourceSparseRow,fields26,weights26,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow26]

private def schemaRow27 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 36 => v 0
  | _ => 0

private theorem schema27 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 27 a = schemaRow27 v a := by
  fin_cases a <;> rfl

private theorem fields27 (s : Fin 8) :
    sourceField 27 s = (![36,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights27 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 27 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row27 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 27 a = sourceSparseRow v 27 a := by
  rw [schema27]
  simp only [sourceSparseRow,fields27,weights27,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow27]

private def schemaRow28 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 37 => v 0
  | _ => 0

private theorem schema28 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 28 a = schemaRow28 v a := by
  fin_cases a <;> rfl

private theorem fields28 (s : Fin 8) :
    sourceField 28 s = (![37,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights28 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 28 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row28 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 28 a = sourceSparseRow v 28 a := by
  rw [schema28]
  simp only [sourceSparseRow,fields28,weights28,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow28]

private def schemaRow29 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 38 => v 0
  | _ => 0

private theorem schema29 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 29 a = schemaRow29 v a := by
  fin_cases a <;> rfl

private theorem fields29 (s : Fin 8) :
    sourceField 29 s = (![38,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights29 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 29 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row29 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 29 a = sourceSparseRow v 29 a := by
  rw [schema29]
  simp only [sourceSparseRow,fields29,weights29,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow29]

private def schemaRow30 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 39 => v 0
  | _ => 0

private theorem schema30 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 30 a = schemaRow30 v a := by
  fin_cases a <;> rfl

private theorem fields30 (s : Fin 8) :
    sourceField 30 s = (![39,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights30 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 30 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row30 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 30 a = sourceSparseRow v 30 a := by
  rw [schema30]
  simp only [sourceSparseRow,fields30,weights30,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow30]

private def schemaRow31 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 40 => v 0
  | _ => 0

private theorem schema31 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 31 a = schemaRow31 v a := by
  fin_cases a <;> rfl

private theorem fields31 (s : Fin 8) :
    sourceField 31 s = (![40,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights31 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 31 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row31 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 31 a = sourceSparseRow v 31 a := by
  rw [schema31]
  simp only [sourceSparseRow,fields31,weights31,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow31]

end LowEnergy.ActualCanonical79Imaginary
