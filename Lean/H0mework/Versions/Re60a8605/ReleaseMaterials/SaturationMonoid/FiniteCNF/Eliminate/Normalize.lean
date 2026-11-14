import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.EmptyCube
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Alias

/-! Shared source normalization preserves the original clauses at every assignment. -/

namespace SaturationMonoid.ComplexityProjection.SATSource.Eliminate

def normalize {n : Nat} (formula : CNFFormula n) : CNFFormula n :=
  ((SATJoint.dropTautologies formula).map List.dedup).dedup

theorem dedup_eval {n : Nat} (clause : CNFClause n) (assignment : Nat → Bool) :
    CNFClause.eval clause.dedup assignment = CNFClause.eval clause assignment := by
  apply Bool.eq_iff_iff.mpr
  simp [CNFClause.eval, List.any_eq_true]

theorem formula_dedup_eval {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval formula.dedup assignment = CNFFormula.eval formula assignment := by
  apply Bool.eq_iff_iff.mpr
  simp [CNFFormula.eval, List.all_eq_true]

theorem normalize_eval {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (normalize formula) assignment = CNFFormula.eval formula assignment := by
  rw [normalize, formula_dedup_eval, CNFFormula.eval, List.all_map]
  simp only [Function.comp_def, dedup_eval]
  exact SATJoint.dropTautologies_eval formula assignment

theorem normalize_sat {n : Nat} (formula : CNFFormula n) :
    CNFSatisfiable (normalize formula) ↔ CNFSatisfiable formula := by
  simp only [CNFSatisfiable, normalize_eval]

theorem normalize_length_le {n : Nat} (formula : CNFFormula n) :
    (normalize formula).length ≤ formula.length := by
  exact (List.dedup_sublist _).length_le.trans
    (by simpa only [List.length_map] using SATJoint.dropTautologies_length_le formula)

def literalKey {n : Nat} (lit : CNFLiteral n) : Fin n × Bool := (lit.var, lit.positive)

theorem literalKey_injective {n : Nat} : Function.Injective (@literalKey n) := by
  intro a b h
  cases a
  cases b
  simpa [literalKey] using h

theorem dedup_length_bound {n : Nat} (clause : CNFClause n) : clause.dedup.length ≤ 2 * n := by
  have hd : (clause.dedup.map literalKey).Nodup :=
    (List.nodup_dedup clause).map literalKey_injective
  have hb := hd.length_le_card
  simpa [Nat.mul_comm] using hb

theorem normalize_clause_bound {n : Nat} (formula : CNFFormula n)
    (clause : CNFClause n) (h : clause ∈ normalize formula) : clause.length ≤ 2 * n := by
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp h)
  exact dedup_length_bound original

theorem normalize_active_subset {n : Nat} (formula : CNFFormula n) :
    Alias.activeVars (normalize formula) ⊆ Alias.activeVars formula := by
  intro v hv
  obtain ⟨clause, hc, lit, hl, he⟩ := (Alias.mem_activeVars _ _).mp hv
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
  have ho' : original ∈ formula := (List.mem_filter.mp ho).1
  exact (Alias.mem_activeVars _ _).mpr ⟨original, ho', lit, List.mem_dedup.mp hl, he⟩

end SaturationMonoid.ComplexityProjection.SATSource.Eliminate
