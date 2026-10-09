import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79SourceSparsePilot
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

private def schemaRow1 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 10 => v 0
  | _ => 0

private theorem schema1 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 1 a = schemaRow1 v a := by
  fin_cases a <;> rfl

private theorem fields1 (s : Fin 8) :
    sourceField 1 s = (![10,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights1 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 1 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row1 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 1 a = sourceSparseRow v 1 a := by
  rw [schema1]
  simp only [sourceSparseRow,fields1,weights1,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow1]

private def schemaRow2 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 11 => v 0
  | _ => 0

private theorem schema2 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 2 a = schemaRow2 v a := by
  fin_cases a <;> rfl

private theorem fields2 (s : Fin 8) :
    sourceField 2 s = (![11,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights2 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 2 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row2 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 2 a = sourceSparseRow v 2 a := by
  rw [schema2]
  simp only [sourceSparseRow,fields2,weights2,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow2]

private def schemaRow3 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 12 => v 0
  | _ => 0

private theorem schema3 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 3 a = schemaRow3 v a := by
  fin_cases a <;> rfl

private theorem fields3 (s : Fin 8) :
    sourceField 3 s = (![12,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights3 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 3 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row3 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 3 a = sourceSparseRow v 3 a := by
  rw [schema3]
  simp only [sourceSparseRow,fields3,weights3,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow3]

private def schemaRow4 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 13 => v 0
  | _ => 0

private theorem schema4 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 4 a = schemaRow4 v a := by
  fin_cases a <;> rfl

private theorem fields4 (s : Fin 8) :
    sourceField 4 s = (![13,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights4 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 4 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row4 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 4 a = sourceSparseRow v 4 a := by
  rw [schema4]
  simp only [sourceSparseRow,fields4,weights4,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow4]

private def schemaRow5 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 14 => v 0
  | _ => 0

private theorem schema5 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 5 a = schemaRow5 v a := by
  fin_cases a <;> rfl

private theorem fields5 (s : Fin 8) :
    sourceField 5 s = (![14,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights5 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 5 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row5 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 5 a = sourceSparseRow v 5 a := by
  rw [schema5]
  simp only [sourceSparseRow,fields5,weights5,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow5]

private def schemaRow6 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 15 => v 0
  | _ => 0

private theorem schema6 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 6 a = schemaRow6 v a := by
  fin_cases a <;> rfl

private theorem fields6 (s : Fin 8) :
    sourceField 6 s = (![15,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights6 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 6 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row6 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 6 a = sourceSparseRow v 6 a := by
  rw [schema6]
  simp only [sourceSparseRow,fields6,weights6,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow6]

private def schemaRow7 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 16 => v 0
  | _ => 0

private theorem schema7 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 7 a = schemaRow7 v a := by
  fin_cases a <;> rfl

private theorem fields7 (s : Fin 8) :
    sourceField 7 s = (![16,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights7 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 7 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row7 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 7 a = sourceSparseRow v 7 a := by
  rw [schema7]
  simp only [sourceSparseRow,fields7,weights7,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow7]

private def schemaRow8 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 17 => v 0
  | _ => 0

private theorem schema8 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 8 a = schemaRow8 v a := by
  fin_cases a <;> rfl

private theorem fields8 (s : Fin 8) :
    sourceField 8 s = (![17,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights8 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 8 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row8 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 8 a = sourceSparseRow v 8 a := by
  rw [schema8]
  simp only [sourceSparseRow,fields8,weights8,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow8]

private def schemaRow9 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 18 => v 0
  | _ => 0

private theorem schema9 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 9 a = schemaRow9 v a := by
  fin_cases a <;> rfl

private theorem fields9 (s : Fin 8) :
    sourceField 9 s = (![18,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights9 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 9 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row9 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 9 a = sourceSparseRow v 9 a := by
  rw [schema9]
  simp only [sourceSparseRow,fields9,weights9,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow9]

private def schemaRow10 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 19 => v 0
  | _ => 0

private theorem schema10 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 10 a = schemaRow10 v a := by
  fin_cases a <;> rfl

private theorem fields10 (s : Fin 8) :
    sourceField 10 s = (![19,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights10 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 10 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row10 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 10 a = sourceSparseRow v 10 a := by
  rw [schema10]
  simp only [sourceSparseRow,fields10,weights10,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow10]

private def schemaRow11 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 20 => v 0
  | _ => 0

private theorem schema11 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 11 a = schemaRow11 v a := by
  fin_cases a <;> rfl

private theorem fields11 (s : Fin 8) :
    sourceField 11 s = (![20,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights11 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 11 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row11 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 11 a = sourceSparseRow v 11 a := by
  rw [schema11]
  simp only [sourceSparseRow,fields11,weights11,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow11]

private def schemaRow12 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 21 => v 0
  | _ => 0

private theorem schema12 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 12 a = schemaRow12 v a := by
  fin_cases a <;> rfl

private theorem fields12 (s : Fin 8) :
    sourceField 12 s = (![21,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights12 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 12 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row12 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 12 a = sourceSparseRow v 12 a := by
  rw [schema12]
  simp only [sourceSparseRow,fields12,weights12,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow12]

private def schemaRow13 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 22 => v 0
  | _ => 0

private theorem schema13 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 13 a = schemaRow13 v a := by
  fin_cases a <;> rfl

private theorem fields13 (s : Fin 8) :
    sourceField 13 s = (![22,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights13 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 13 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row13 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 13 a = sourceSparseRow v 13 a := by
  rw [schema13]
  simp only [sourceSparseRow,fields13,weights13,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow13]

private def schemaRow14 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 23 => v 0
  | _ => 0

private theorem schema14 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 14 a = schemaRow14 v a := by
  fin_cases a <;> rfl

private theorem fields14 (s : Fin 8) :
    sourceField 14 s = (![23,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights14 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 14 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row14 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 14 a = sourceSparseRow v 14 a := by
  rw [schema14]
  simp only [sourceSparseRow,fields14,weights14,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow14]

private def schemaRow15 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 24 => v 0
  | _ => 0

private theorem schema15 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 15 a = schemaRow15 v a := by
  fin_cases a <;> rfl

private theorem fields15 (s : Fin 8) :
    sourceField 15 s = (![24,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights15 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 15 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row15 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 15 a = sourceSparseRow v 15 a := by
  rw [schema15]
  simp only [sourceSparseRow,fields15,weights15,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow15]

end LowEnergy.ActualCanonical79Imaginary
