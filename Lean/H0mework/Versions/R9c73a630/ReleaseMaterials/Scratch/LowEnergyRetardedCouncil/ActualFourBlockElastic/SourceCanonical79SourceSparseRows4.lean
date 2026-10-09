import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79SourceSparsePilot
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

private def schemaRow64 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 78 => v 15
  | 80 => v 14
  | 82 => v 14
  | 85 => v 13
  | 89 => v 14
  | 96 => v 14
  | _ => 0

private theorem schema64 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 64 a = schemaRow64 v a := by
  fin_cases a <;> rfl

private theorem fields64 (s : Fin 8) :
    sourceField 64 s = (![78,80,82,85,89,96,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights64 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 64 s = ![v 15,v 14,v 14,v 13,v 14,v 14,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row64 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 64 a = sourceSparseRow v 64 a := by
  rw [schema64]
  simp only [sourceSparseRow,fields64,weights64,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow64]

private def schemaRow65 (_v : Fin 16 → ℂ) (_a : Fin 97) : ℂ :=
  0

private theorem schema65 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 65 a = schemaRow65 v a := by
  fin_cases a <;> rfl

private theorem fields65 (s : Fin 8) :
    sourceField 65 s = (![0,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights65 (_v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight _v 65 s = ![0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row65 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 65 a = sourceSparseRow v 65 a := by
  rw [schema65]
  simp only [sourceSparseRow,fields65,weights65,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow65]

private def schemaRow66 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 78 => v 15
  | 80 => v 14
  | 82 => v 13
  | 85 => v 13
  | 89 => v 13
  | 96 => v 13
  | _ => 0

private theorem schema66 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 66 a = schemaRow66 v a := by
  fin_cases a <;> rfl

private theorem fields66 (s : Fin 8) :
    sourceField 66 s = (![78,80,82,85,89,96,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights66 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 66 s = ![v 15,v 14,v 13,v 13,v 13,v 13,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row66 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 66 a = sourceSparseRow v 66 a := by
  rw [schema66]
  simp only [sourceSparseRow,fields66,weights66,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow66]

private def schemaRow67 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 76 => v 15
  | 87 => v 14
  | 92 => v 13
  | _ => 0

private theorem schema67 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 67 a = schemaRow67 v a := by
  fin_cases a <;> rfl

private theorem fields67 (s : Fin 8) :
    sourceField 67 s = (![76,87,92,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights67 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 67 s = ![v 15,v 14,v 13,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row67 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 67 a = sourceSparseRow v 67 a := by
  rw [schema67]
  simp only [sourceSparseRow,fields67,weights67,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow67]

private def schemaRow68 (_v : Fin 16 → ℂ) (_a : Fin 97) : ℂ :=
  0

private theorem schema68 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 68 a = schemaRow68 v a := by
  fin_cases a <;> rfl

private theorem fields68 (s : Fin 8) :
    sourceField 68 s = (![0,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights68 (_v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight _v 68 s = ![0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row68 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 68 a = sourceSparseRow v 68 a := by
  rw [schema68]
  simp only [sourceSparseRow,fields68,weights68,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow68]

private def schemaRow69 (_v : Fin 16 → ℂ) (_a : Fin 97) : ℂ :=
  0

private theorem schema69 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 69 a = schemaRow69 v a := by
  fin_cases a <;> rfl

private theorem fields69 (s : Fin 8) :
    sourceField 69 s = (![0,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights69 (_v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight _v 69 s = ![0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row69 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 69 a = sourceSparseRow v 69 a := by
  rw [schema69]
  simp only [sourceSparseRow,fields69,weights69,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow69]

private def schemaRow70 (_v : Fin 16 → ℂ) (_a : Fin 97) : ℂ :=
  0

private theorem schema70 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 70 a = schemaRow70 v a := by
  fin_cases a <;> rfl

private theorem fields70 (s : Fin 8) :
    sourceField 70 s = (![0,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights70 (_v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight _v 70 s = ![0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row70 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 70 a = sourceSparseRow v 70 a := by
  rw [schema70]
  simp only [sourceSparseRow,fields70,weights70,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow70]

private def schemaRow71 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 77 => v 12
  | 81 => v 14
  | 91 => v 13
  | _ => 0

private theorem schema71 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 71 a = schemaRow71 v a := by
  fin_cases a <;> rfl

private theorem fields71 (s : Fin 8) :
    sourceField 71 s = (![77,81,91,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights71 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 71 s = ![v 12,v 14,v 13,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row71 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 71 a = sourceSparseRow v 71 a := by
  rw [schema71]
  simp only [sourceSparseRow,fields71,weights71,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow71]

private def schemaRow72 (_v : Fin 16 → ℂ) (_a : Fin 97) : ℂ :=
  0

private theorem schema72 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 72 a = schemaRow72 v a := by
  fin_cases a <;> rfl

private theorem fields72 (s : Fin 8) :
    sourceField 72 s = (![0,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights72 (_v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight _v 72 s = ![0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row72 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 72 a = sourceSparseRow v 72 a := by
  rw [schema72]
  simp only [sourceSparseRow,fields72,weights72,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow72]

private def schemaRow73 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 77 => v 15
  | 81 => v 13
  | 91 => v 14
  | _ => 0

private theorem schema73 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 73 a = schemaRow73 v a := by
  fin_cases a <;> rfl

private theorem fields73 (s : Fin 8) :
    sourceField 73 s = (![77,81,91,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights73 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 73 s = ![v 15,v 13,v 14,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row73 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 73 a = sourceSparseRow v 73 a := by
  rw [schema73]
  simp only [sourceSparseRow,fields73,weights73,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow73]

private def schemaRow74 (_v : Fin 16 → ℂ) (_a : Fin 97) : ℂ :=
  0

private theorem schema74 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 74 a = schemaRow74 v a := by
  fin_cases a <;> rfl

private theorem fields74 (s : Fin 8) :
    sourceField 74 s = (![0,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights74 (_v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight _v 74 s = ![0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row74 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 74 a = sourceSparseRow v 74 a := by
  rw [schema74]
  simp only [sourceSparseRow,fields74,weights74,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow74]

private def schemaRow75 (_v : Fin 16 → ℂ) (_a : Fin 97) : ℂ :=
  0

private theorem schema75 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 75 a = schemaRow75 v a := by
  fin_cases a <;> rfl

private theorem fields75 (s : Fin 8) :
    sourceField 75 s = (![0,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights75 (_v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight _v 75 s = ![0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row75 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 75 a = sourceSparseRow v 75 a := by
  rw [schema75]
  simp only [sourceSparseRow,fields75,weights75,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow75]

private def schemaRow76 (_v : Fin 16 → ℂ) (_a : Fin 97) : ℂ :=
  0

private theorem schema76 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 76 a = schemaRow76 v a := by
  fin_cases a <;> rfl

private theorem fields76 (s : Fin 8) :
    sourceField 76 s = (![0,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights76 (_v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight _v 76 s = ![0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row76 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 76 a = sourceSparseRow v 76 a := by
  rw [schema76]
  simp only [sourceSparseRow,fields76,weights76,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow76]

private def schemaRow77 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 77 => v 15
  | 81 => v 13
  | 91 => v 14
  | _ => 0

private theorem schema77 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 77 a = schemaRow77 v a := by
  fin_cases a <;> rfl

private theorem fields77 (s : Fin 8) :
    sourceField 77 s = (![77,81,91,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights77 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 77 s = ![v 15,v 13,v 14,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row77 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 77 a = sourceSparseRow v 77 a := by
  rw [schema77]
  simp only [sourceSparseRow,fields77,weights77,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow77]

private def schemaRow78 (_v : Fin 16 → ℂ) (_a : Fin 97) : ℂ :=
  0

private theorem schema78 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 78 a = schemaRow78 v a := by
  fin_cases a <;> rfl

private theorem fields78 (s : Fin 8) :
    sourceField 78 s = (![0,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights78 (_v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight _v 78 s = ![0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row78 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 78 a = sourceSparseRow v 78 a := by
  rw [schema78]
  simp only [sourceSparseRow,fields78,weights78,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow78]

end LowEnergy.ActualCanonical79Imaginary
