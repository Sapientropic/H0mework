import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79SourceSparsePilot
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

private def schemaRow32 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 41 => v 0
  | _ => 0

private theorem schema32 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 32 a = schemaRow32 v a := by
  fin_cases a <;> rfl

private theorem fields32 (s : Fin 8) :
    sourceField 32 s = (![41,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights32 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 32 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row32 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 32 a = sourceSparseRow v 32 a := by
  rw [schema32]
  simp only [sourceSparseRow,fields32,weights32,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow32]

private def schemaRow33 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 42 => v 0
  | _ => 0

private theorem schema33 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 33 a = schemaRow33 v a := by
  fin_cases a <;> rfl

private theorem fields33 (s : Fin 8) :
    sourceField 33 s = (![42,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights33 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 33 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row33 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 33 a = sourceSparseRow v 33 a := by
  rw [schema33]
  simp only [sourceSparseRow,fields33,weights33,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow33]

private def schemaRow34 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 43 => v 0
  | _ => 0

private theorem schema34 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 34 a = schemaRow34 v a := by
  fin_cases a <;> rfl

private theorem fields34 (s : Fin 8) :
    sourceField 34 s = (![43,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights34 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 34 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row34 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 34 a = sourceSparseRow v 34 a := by
  rw [schema34]
  simp only [sourceSparseRow,fields34,weights34,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow34]

private def schemaRow35 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 44 => v 0
  | _ => 0

private theorem schema35 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 35 a = schemaRow35 v a := by
  fin_cases a <;> rfl

private theorem fields35 (s : Fin 8) :
    sourceField 35 s = (![44,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights35 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 35 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row35 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 35 a = sourceSparseRow v 35 a := by
  rw [schema35]
  simp only [sourceSparseRow,fields35,weights35,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow35]

private def schemaRow36 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 45 => v 0
  | _ => 0

private theorem schema36 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 36 a = schemaRow36 v a := by
  fin_cases a <;> rfl

private theorem fields36 (s : Fin 8) :
    sourceField 36 s = (![45,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights36 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 36 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row36 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 36 a = sourceSparseRow v 36 a := by
  rw [schema36]
  simp only [sourceSparseRow,fields36,weights36,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow36]

private def schemaRow37 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 46 => v 0
  | _ => 0

private theorem schema37 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 37 a = schemaRow37 v a := by
  fin_cases a <;> rfl

private theorem fields37 (s : Fin 8) :
    sourceField 37 s = (![46,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights37 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 37 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row37 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 37 a = sourceSparseRow v 37 a := by
  rw [schema37]
  simp only [sourceSparseRow,fields37,weights37,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow37]

private def schemaRow38 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 47 => v 0
  | _ => 0

private theorem schema38 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 38 a = schemaRow38 v a := by
  fin_cases a <;> rfl

private theorem fields38 (s : Fin 8) :
    sourceField 38 s = (![47,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights38 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 38 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row38 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 38 a = sourceSparseRow v 38 a := by
  rw [schema38]
  simp only [sourceSparseRow,fields38,weights38,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow38]

private def schemaRow39 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 48 => v 0
  | _ => 0

private theorem schema39 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 39 a = schemaRow39 v a := by
  fin_cases a <;> rfl

private theorem fields39 (s : Fin 8) :
    sourceField 39 s = (![48,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights39 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 39 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row39 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 39 a = sourceSparseRow v 39 a := by
  rw [schema39]
  simp only [sourceSparseRow,fields39,weights39,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow39]

private def schemaRow40 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 49 => v 0
  | _ => 0

private theorem schema40 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 40 a = schemaRow40 v a := by
  fin_cases a <;> rfl

private theorem fields40 (s : Fin 8) :
    sourceField 40 s = (![49,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights40 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 40 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row40 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 40 a = sourceSparseRow v 40 a := by
  rw [schema40]
  simp only [sourceSparseRow,fields40,weights40,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow40]

private def schemaRow41 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 50 => v 0
  | _ => 0

private theorem schema41 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 41 a = schemaRow41 v a := by
  fin_cases a <;> rfl

private theorem fields41 (s : Fin 8) :
    sourceField 41 s = (![50,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights41 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 41 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row41 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 41 a = sourceSparseRow v 41 a := by
  rw [schema41]
  simp only [sourceSparseRow,fields41,weights41,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow41]

private def schemaRow42 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 51 => v 0
  | _ => 0

private theorem schema42 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 42 a = schemaRow42 v a := by
  fin_cases a <;> rfl

private theorem fields42 (s : Fin 8) :
    sourceField 42 s = (![51,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights42 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 42 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row42 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 42 a = sourceSparseRow v 42 a := by
  rw [schema42]
  simp only [sourceSparseRow,fields42,weights42,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow42]

private def schemaRow43 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 52 => v 0
  | _ => 0

private theorem schema43 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 43 a = schemaRow43 v a := by
  fin_cases a <;> rfl

private theorem fields43 (s : Fin 8) :
    sourceField 43 s = (![52,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights43 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 43 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row43 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 43 a = sourceSparseRow v 43 a := by
  rw [schema43]
  simp only [sourceSparseRow,fields43,weights43,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow43]

private def schemaRow44 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 53 => v 0
  | _ => 0

private theorem schema44 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 44 a = schemaRow44 v a := by
  fin_cases a <;> rfl

private theorem fields44 (s : Fin 8) :
    sourceField 44 s = (![53,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights44 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 44 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row44 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 44 a = sourceSparseRow v 44 a := by
  rw [schema44]
  simp only [sourceSparseRow,fields44,weights44,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow44]

private def schemaRow45 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 54 => v 0
  | _ => 0

private theorem schema45 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 45 a = schemaRow45 v a := by
  fin_cases a <;> rfl

private theorem fields45 (s : Fin 8) :
    sourceField 45 s = (![54,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights45 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 45 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row45 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 45 a = sourceSparseRow v 45 a := by
  rw [schema45]
  simp only [sourceSparseRow,fields45,weights45,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow45]

private def schemaRow46 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 55 => v 0
  | _ => 0

private theorem schema46 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 46 a = schemaRow46 v a := by
  fin_cases a <;> rfl

private theorem fields46 (s : Fin 8) :
    sourceField 46 s = (![55,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights46 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 46 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row46 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 46 a = sourceSparseRow v 46 a := by
  rw [schema46]
  simp only [sourceSparseRow,fields46,weights46,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow46]

private def schemaRow47 (v : Fin 16 → ℂ) (a : Fin 97) : ℂ :=
  match a.val with
  | 56 => v 0
  | _ => 0

private theorem schema47 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 47 a = schemaRow47 v a := by
  fin_cases a <;> rfl

private theorem fields47 (s : Fin 8) :
    sourceField 47 s = (![56,0,0,0,0,0,0,0] : Fin 8 → Fin 97) s := by
  fin_cases s <;> rfl

private theorem weights47 (v : Fin 16 → ℂ) (s : Fin 8) :
    sourceWeight v 47 s = ![v 0,0,0,0,0,0,0,0] s := by
  fin_cases s <;> rfl

theorem actual_source_sparse_row47 (v : Fin 16 → ℂ) (a : Fin 97) :
    sourceSchema v 47 a = sourceSparseRow v 47 a := by
  rw [schema47]
  simp only [sourceSparseRow,fields47,weights47,Fin.sum_univ_succ]
  fin_cases a <;> simp [schemaRow47]

end LowEnergy.ActualCanonical79Imaginary
