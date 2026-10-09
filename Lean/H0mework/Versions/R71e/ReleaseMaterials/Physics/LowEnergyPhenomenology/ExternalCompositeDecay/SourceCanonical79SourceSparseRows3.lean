import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79SourceSparsePilot
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

private def schemaRow48 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 57 => v 0
  | 75 => v 1
  | _ => 0

private theorem schema48 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 48 a = schemaRow48 v a := by
  fin_cases a <;> rfl

private theorem fields48 (s : Fin 8) :
    sourceField 48 s = (![57,75,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights48 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 48 s = ![v 0,v 1,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row48 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 48 a = sourceSparseRow v 48 a := by
  rw [schema48]
  simp only [sourceSparseRow,fields48,weights48,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow48]

private def schemaRow49 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 61 => v 0
  | 76 => v 2
  | 77 => v 3
  | 81 => v 4
  | 91 => v 4
  | _ => 0

private theorem schema49 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 49 a = schemaRow49 v a := by
  fin_cases a <;> rfl

private theorem fields49 (s : Fin 8) :
    sourceField 49 s = (![61,76,77,81,91,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights49 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 49 s = ![v 0,v 2,v 3,v 4,v 4,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row49 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 49 a = sourceSparseRow v 49 a := by
  rw [schema49]
  simp only [sourceSparseRow,fields49,weights49,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow49]

private def schemaRow50 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 62 => v 0
  | 79 => v 5
  | 82 => v 2
  | 83 => v 1
  | _ => 0

private theorem schema50 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 50 a = schemaRow50 v a := by
  fin_cases a <;> rfl

private theorem fields50 (s : Fin 8) :
    sourceField 50 s = (![62,79,82,83,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights50 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 50 s = ![v 0,v 5,v 2,v 1,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row50 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 50 a = sourceSparseRow v 50 a := by
  rw [schema50]
  simp only [sourceSparseRow,fields50,weights50,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow50]

private def schemaRow51 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 65 => v 0
  | 76 => v 6
  | 77 => v 2
  | 87 => v 4
  | 92 => v 4
  | _ => 0

private theorem schema51 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 51 a = schemaRow51 v a := by
  fin_cases a <;> rfl

private theorem fields51 (s : Fin 8) :
    sourceField 51 s = (![65,76,77,87,92,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights51 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 51 s = ![v 0,v 6,v 2,v 4,v 4,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row51 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 51 a = sourceSparseRow v 51 a := by
  rw [schema51]
  simp only [sourceSparseRow,fields51,weights51,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow51]

private def schemaRow52 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 66 => v 0
  | 78 => v 7
  | 80 => v 8
  | 82 => v 6
  | 83 => v 2
  | 85 => v 8
  | 89 => v 3
  | 96 => v 6
  | _ => 0

private theorem schema52 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 52 a = schemaRow52 v a := by
  fin_cases a <;> rfl

private theorem fields52 (s : Fin 8) :
    sourceField 52 s = (![66,78,80,82,83,85,89,96] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights52 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 52 s = ![v 0,v 7,v 8,v 6,v 2,v 8,v 3,v 6] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row52 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 52 a = sourceSparseRow v 52 a := by
  rw [schema52]
  simp only [sourceSparseRow,fields52,weights52,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow52]

private def schemaRow53 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 67 => v 0
  | 86 => v 5
  | 88 => v 9
  | 89 => v 2
  | _ => 0

private theorem schema53 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 53 a = schemaRow53 v a := by
  fin_cases a <;> rfl

private theorem fields53 (s : Fin 8) :
    sourceField 53 s = (![67,86,88,89,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights53 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 53 s = ![v 0,v 5,v 9,v 2,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row53 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 53 a = sourceSparseRow v 53 a := by
  rw [schema53]
  simp only [sourceSparseRow,fields53,weights53,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow53]

private def schemaRow54 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 69 => v 0
  | 78 => v 2
  | 93 => v 10
  | _ => 0

private theorem schema54 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 54 a = schemaRow54 v a := by
  fin_cases a <;> rfl

private theorem fields54 (s : Fin 8) :
    sourceField 54 s = (![69,78,93,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights54 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 54 s = ![v 0,v 2,v 10,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row54 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 54 a = sourceSparseRow v 54 a := by
  rw [schema54]
  simp only [sourceSparseRow,fields54,weights54,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow54]

private def schemaRow55 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 70 => v 0
  | 77 => v 11
  | 81 => v 8
  | 84 => v 2
  | 91 => v 8
  | 95 => v 1
  | _ => 0

private theorem schema55 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 55 a = schemaRow55 v a := by
  fin_cases a <;> rfl

private theorem fields55 (s : Fin 8) :
    sourceField 55 s = (![70,77,81,84,91,95,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights55 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 55 s = ![v 0,v 11,v 8,v 2,v 8,v 1,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row55 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 55 a = sourceSparseRow v 55 a := by
  rw [schema55]
  simp only [sourceSparseRow,fields55,weights55,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow55]

private def schemaRow56 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 71 => v 0
  | 76 => v 7
  | 87 => v 8
  | 90 => v 2
  | 92 => v 8
  | 94 => v 9
  | _ => 0

private theorem schema56 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 56 a = schemaRow56 v a := by
  fin_cases a <;> rfl

private theorem fields56 (s : Fin 8) :
    sourceField 56 s = (![71,76,87,90,92,94,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights56 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 56 s = ![v 0,v 7,v 8,v 2,v 8,v 9,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row56 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 56 a = sourceSparseRow v 56 a := by
  rw [schema56]
  simp only [sourceSparseRow,fields56,weights56,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow56]

private def schemaRow57 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 72 => v 0
  | 93 => v 5
  | 96 => v 2
  | _ => 0

private theorem schema57 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 57 a = schemaRow57 v a := by
  fin_cases a <;> rfl

private theorem fields57 (s : Fin 8) :
    sourceField 57 s = (![72,93,96,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights57 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 57 s = ![v 0,v 5,v 2,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row57 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 57 a = sourceSparseRow v 57 a := by
  rw [schema57]
  simp only [sourceSparseRow,fields57,weights57,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow57]

private def schemaRow58 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 78 => v 12
  | 80 => v 13
  | 82 => v 14
  | 85 => v 14
  | 89 => v 14
  | 96 => v 14
  | _ => 0

private theorem schema58 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 58 a = schemaRow58 v a := by
  fin_cases a <;> rfl

private theorem fields58 (s : Fin 8) :
    sourceField 58 s = (![78,80,82,85,89,96,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights58 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 58 s = ![v 12,v 13,v 14,v 14,v 14,v 14,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row58 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 58 a = sourceSparseRow v 58 a := by
  rw [schema58]
  simp only [sourceSparseRow,fields58,weights58,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow58]

private def schemaRow59 (_v : Fin 16 → ℂ) (_a : Fin 97) : ℂ :=
  0

private theorem schema59 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 59 a = schemaRow59 v a := by
  fin_cases a <;> rfl

private theorem fields59 (s : Fin 8) :
    sourceField 59 s = (![0,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights59 (_v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight _v 59 s = ![0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row59 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 59 a = sourceSparseRow v 59 a := by
  rw [schema59]
  simp only [sourceSparseRow,fields59,weights59,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow59]

private def schemaRow60 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 78 => v 12
  | 80 => v 13
  | 82 => v 13
  | 85 => v 14
  | 89 => v 13
  | 96 => v 13
  | _ => 0

private theorem schema60 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 60 a = schemaRow60 v a := by
  fin_cases a <;> rfl

private theorem fields60 (s : Fin 8) :
    sourceField 60 s = (![78,80,82,85,89,96,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights60 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 60 s = ![v 12,v 13,v 13,v 14,v 13,v 13,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row60 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 60 a = sourceSparseRow v 60 a := by
  rw [schema60]
  simp only [sourceSparseRow,fields60,weights60,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow60]

private def schemaRow61 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 76 => v 12
  | 87 => v 13
  | 92 => v 14
  | _ => 0

private theorem schema61 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 61 a = schemaRow61 v a := by
  fin_cases a <;> rfl

private theorem fields61 (s : Fin 8) :
    sourceField 61 s = (![76,87,92,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights61 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 61 s = ![v 12,v 13,v 14,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row61 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 61 a = sourceSparseRow v 61 a := by
  rw [schema61]
  simp only [sourceSparseRow,fields61,weights61,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow61]

private def schemaRow62 (_v : Fin 16 → ℂ) (_a : Fin 97) : ℂ :=
  0

private theorem schema62 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 62 a = schemaRow62 v a := by
  fin_cases a <;> rfl

private theorem fields62 (s : Fin 8) :
    sourceField 62 s = (![0,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights62 (_v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight _v 62 s = ![0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row62 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 62 a = sourceSparseRow v 62 a := by
  rw [schema62]
  simp only [sourceSparseRow,fields62,weights62,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow62]

private def schemaRow63 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 76 => v 12
  | 87 => v 13
  | 92 => v 14
  | _ => 0

private theorem schema63 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 63 a = schemaRow63 v a := by
  fin_cases a <;> rfl

private theorem fields63 (s : Fin 8) :
    sourceField 63 s = (![76,87,92,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights63 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 63 s = ![v 12,v 13,v 14,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row63 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 63 a = sourceSparseRow v 63 a := by
  rw [schema63]
  simp only [sourceSparseRow,fields63,weights63,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow63]

end LowEnergy.ActualCanonical79Imaginary
