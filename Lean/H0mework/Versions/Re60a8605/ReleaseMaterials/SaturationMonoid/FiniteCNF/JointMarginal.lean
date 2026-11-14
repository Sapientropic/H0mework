import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Joint
import Mathlib.Data.List.Dedup
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
Actual fibre integration for the signed clause source.  A retired coordinate is
integrated into the integer coefficient and replaced by a fixed singleton.
Retirement is generated from the last occurrence in the original clause list.
-/

namespace SaturationMonoid.ComplexityProjection.SATJoint

open scoped BigOperators

def forgetCube {n : ℕ} (v : Fin n) (c : Cube n) : Cube n :=
  Function.update c v {false}

def forgetTerm {n : ℕ} (v : Fin n) (t : ℤ × Cube n) : ℤ × Cube n :=
  (t.1 * ((t.2 v).card : ℤ), forgetCube v t.2)

def forgetTerms {n : ℕ} (v : Fin n) (terms : Terms n) : Terms n :=
  terms.map (forgetTerm v)

theorem forgetCube_mass {n : ℕ} (v : Fin n) (c : Cube n) :
    ((c v).card : ℤ) * cubeMass (forgetCube v c) = cubeMass c := by
  have hc : (fun i => ((forgetCube v c i).card : ℤ)) =
      Function.update (fun i => ((c i).card : ℤ)) v 1 := by
    funext i
    by_cases h : i = v <;> simp [forgetCube, h, Function.update_of_ne]
  simp only [cubeMass, hc]
  rw [Finset.prod_update_of_mem (Finset.mem_univ v)]
  simpa only [one_mul, Finset.erase_eq] using
    Finset.mul_prod_erase Finset.univ (fun i => ((c i).card : ℤ))
    (Finset.mem_univ v)

theorem forgetTerms_mass {n : ℕ} (v : Fin n) (terms : Terms n) :
    termsMass (forgetTerms v terms) = termsMass terms := by
  induction terms with
  | nil => simp [forgetTerms, termsMass]
  | cons t terms ih =>
      simp only [forgetTerms, termsMass, List.map_cons, List.map_map,
        List.sum_cons, forgetTerm] at *
      rw [ih, mul_assoc, forgetCube_mass]

def Absent {n : ℕ} (v : Fin n) (formula : CNFFormula n) : Prop :=
  ∀ clause ∈ formula, ∀ lit ∈ clause, lit.var ≠ v

instance {n : ℕ} (v : Fin n) (formula : CNFFormula n) :
    Decidable (Absent v formula) :=
  inferInstanceAs (Decidable (∀ clause ∈ formula, ∀ lit ∈ clause, lit.var ≠ v))

theorem clauseCube_univ_of_absent {n : ℕ} (v : Fin n) (clause : CNFClause n)
    (h : ∀ lit ∈ clause, lit.var ≠ v) : clauseCube clause v = Finset.univ := by
  apply Finset.ext
  intro b
  simp only [clauseCube, Finset.mem_filter, Finset.mem_univ, true_and,
    iff_true]
  intro lit hlit hv
  exact False.elim (h lit hlit hv)

theorem forgetCube_join {n : ℕ} (v : Fin n) (a b : Cube n)
    (hb : b v = Finset.univ) :
    forgetCube v (joinCube a b) = joinCube (forgetCube v a) b := by
  funext i
  by_cases h : i = v
  · subst i
    simp [forgetCube, joinCube, hb]
  · simp [forgetCube, joinCube, Function.update_of_ne h]

theorem forgetTerm_join {n : ℕ} (v : Fin n) (t : ℤ × Cube n) (b : Cube n)
    (hb : b v = Finset.univ) :
    forgetTerm v (-t.1, joinCube t.2 b) =
      (-(forgetTerm v t).1, joinCube (forgetTerm v t).2 b) := by
  have he : joinCube t.2 b v = t.2 v := by
    simp only [joinCube, hb, Finset.inter_univ]
  simp only [forgetTerm, he, neg_mul, forgetCube_join v t.2 b hb]

theorem forgetTerms_clauseStep {n : ℕ} (v : Fin n) (clause : CNFClause n)
    (terms : Terms n) (h : ∀ lit ∈ clause, lit.var ≠ v) :
    forgetTerms v (clauseStep clause terms) =
      clauseStep clause (forgetTerms v terms) := by
  simp only [forgetTerms, clauseStep, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  exact forgetTerm_join v t (clauseCube clause) (clauseCube_univ_of_absent v clause h)

def applyFormula {n : ℕ} : CNFFormula n → Terms n → Terms n
  | [], terms => terms
  | clause :: rest, terms => applyFormula rest (clauseStep clause terms)

def formulaMass {n : ℕ} (formula : CNFFormula n) (terms : Terms n) : ℤ :=
  termsMass (applyFormula formula terms)

theorem applyFormula_at {n : ℕ} (formula : CNFFormula n) (terms : Terms n)
    (x : Assignment n) :
    termsAt (applyFormula formula terms) x = termsAt terms x *
      (if CNFFormula.eval formula (extendAssignment x) then 1 else 0) := by
  induction formula generalizing terms with
  | nil => simp [applyFormula, CNFFormula.eval]
  | cons clause rest ih =>
      rw [applyFormula, ih, clauseStep_at, indicator_clause]
      simp only [CNFFormula.eval, List.all_cons]
      by_cases hc : CNFClause.eval clause (extendAssignment x) = true <;>
        by_cases hr : rest.all (fun c => CNFClause.eval c (extendAssignment x)) = true <;>
          simp_all

theorem formulaMass_collect {n : ℕ} (formula : CNFFormula n) (terms : Terms n) :
    formulaMass formula (collectTerms terms) = formulaMass formula terms := by
  simp only [formulaMass, termsMass_eq_sum, applyFormula_at, collectTerms_at]

theorem applyFormula_forget {n : ℕ} (v : Fin n) (formula : CNFFormula n)
    (terms : Terms n) (h : Absent v formula) :
    applyFormula formula (forgetTerms v terms) =
      forgetTerms v (applyFormula formula terms) := by
  induction formula generalizing terms with
  | nil => rfl
  | cons clause rest ih =>
      have hc : ∀ lit ∈ clause, lit.var ≠ v := h clause (by simp)
      have hr : Absent v rest := by
        intro c hc l hl
        exact h c (by simp [hc]) l hl
      simp only [applyFormula]
      rw [← forgetTerms_clauseStep v clause terms hc, ih _ hr]

theorem formulaMass_forget {n : ℕ} (v : Fin n) (formula : CNFFormula n)
    (terms : Terms n) (h : Absent v formula) :
    formulaMass formula (forgetTerms v terms) = formulaMass formula terms := by
  rw [formulaMass, applyFormula_forget v formula terms h, forgetTerms_mass]
  rfl

def retireTerms {n : ℕ} : List (Fin n) → Terms n → Terms n
  | [], terms => terms
  | v :: rest, terms => retireTerms rest (collectTerms (forgetTerms v terms))

theorem retireTerms_preserves {n : ℕ} (vars : List (Fin n))
    (formula : CNFFormula n) (terms : Terms n)
    (h : ∀ v ∈ vars, Absent v formula) :
    formulaMass formula (retireTerms vars terms) = formulaMass formula terms := by
  induction vars generalizing terms with
  | nil => rfl
  | cons v vars ih =>
      rw [retireTerms, ih _ (by intro w hw; exact h w (by simp [hw]))]
      rw [formulaMass_collect, formulaMass_forget v formula terms (h v (by simp))]

def retireAfter {n : ℕ} (clause : CNFClause n) (rest : CNFFormula n) : List (Fin n) :=
  (clause.map CNFLiteral.var).dedup.filter fun v => decide (Absent v rest)

theorem retireAfter_absent {n : ℕ} (clause : CNFClause n) (rest : CNFFormula n)
    (v : Fin n) (h : v ∈ retireAfter clause rest) : Absent v rest := by
  exact of_decide_eq_true (List.mem_filter.mp h).2

def marginalRun {n : ℕ} : CNFFormula n → Terms n → Terms n
  | [], terms => terms
  | clause :: rest, terms => marginalRun rest
      (retireTerms (retireAfter clause rest) (collectTerms (clauseStep clause terms)))

def marginalReadout {n : ℕ} (formula : CNFFormula n) : ℤ :=
  termsMass (marginalRun formula [(1, topCube n)])

theorem marginalRun_mass {n : ℕ} (formula : CNFFormula n) (terms : Terms n) :
    termsMass (marginalRun formula terms) = formulaMass formula terms := by
  induction formula generalizing terms with
  | nil => rfl
  | cons clause rest ih =>
      rw [marginalRun, ih, retireTerms_preserves _ rest _ (retireAfter_absent clause rest),
        formulaMass_collect]
      rfl

theorem marginalReadout_eq_count {n : ℕ} (formula : CNFFormula n) :
    marginalReadout formula =
      ((Finset.univ.filter fun x : Assignment n =>
        CNFFormula.eval formula (extendAssignment x) = true).card : ℤ) := by
  rw [marginalReadout, marginalRun_mass]
  simp only [formulaMass, termsMass_eq_sum]
  simp only [applyFormula_at]
  simp only [termsAt,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, indicator_top,
    mul_one, add_zero, one_mul, Finset.sum_boole]

end SaturationMonoid.ComplexityProjection.SATJoint
