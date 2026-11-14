import H0mework.Computation.SelfReduction.P687
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
An executable clause-joint source calculation over the original CNF syntax.
The state consists of signed Boolean cylinders.  A cylinder is integrated by
its coordinate cardinalities, and multiplication intersects those coordinates.
This is subordinate mathematics; it does not install a new runtime authority.
-/

namespace SaturationMonoid.ComplexityProjection.SATJoint

open scoped BigOperators

abbrev Assignment (n : ℕ) := Fin n → Bool
abbrev Cube (n : ℕ) := Fin n → Finset Bool

def extendAssignment {n : ℕ} (x : Assignment n) : ℕ → Bool :=
  fun i => if h : i < n then x ⟨i, h⟩ else false

@[simp] theorem extendAssignment_fin {n : ℕ} (x : Assignment n) (i : Fin n) :
    extendAssignment x i.val = x i := by
  simp [extendAssignment]

def Fits {n : ℕ} (c : Cube n) (x : Assignment n) : Prop :=
  ∀ i, x i ∈ c i

instance {n : ℕ} (c : Cube n) (x : Assignment n) : Decidable (Fits c x) :=
  inferInstanceAs (Decidable (∀ i, x i ∈ c i))

def cubeIndicator {n : ℕ} (c : Cube n) (x : Assignment n) : ℤ :=
  if Fits c x then 1 else 0

def cubeMass {n : ℕ} (c : Cube n) : ℤ :=
  ∏ i, ((c i).card : ℤ)

def topCube (n : ℕ) : Cube n := fun _ => Finset.univ

def joinCube {n : ℕ} (a b : Cube n) : Cube n := fun i => a i ∩ b i

def clauseCube {n : ℕ} (clause : CNFClause n) : Cube n :=
  fun i => Finset.univ.filter fun b =>
    ∀ lit ∈ clause, lit.var = i → b ≠ lit.positive

@[simp] theorem fits_top {n : ℕ} (x : Assignment n) : Fits (topCube n) x := by
  simp [Fits, topCube]

@[simp] theorem fits_join {n : ℕ} (a b : Cube n) (x : Assignment n) :
    Fits (joinCube a b) x ↔ Fits a x ∧ Fits b x := by
  simp only [Fits, joinCube, Finset.mem_inter]
  exact forall_and

@[simp] theorem indicator_top {n : ℕ} (x : Assignment n) :
    cubeIndicator (topCube n) x = 1 := by simp [cubeIndicator]

theorem indicator_join {n : ℕ} (a b : Cube n) (x : Assignment n) :
    cubeIndicator (joinCube a b) x = cubeIndicator a x * cubeIndicator b x := by
  by_cases ha : Fits a x <;> by_cases hb : Fits b x <;>
    simp [cubeIndicator, fits_join, ha, hb]

theorem cubeMass_eq_sum {n : ℕ} (c : Cube n) :
    cubeMass c = ∑ x : Assignment n, cubeIndicator c x := by
  have hf : (Finset.univ.filter fun x : Assignment n => Fits c x) =
      Fintype.piFinset c := by
    apply Finset.ext
    intro x
    exact (Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x))).trans
      Fintype.mem_piFinset.symm
  rw [cubeMass]
  simp only [cubeIndicator, Finset.sum_boole]
  rw [hf, Fintype.card_piFinset, Nat.cast_prod]

theorem fits_clause {n : ℕ} (clause : CNFClause n) (x : Assignment n) :
    Fits (clauseCube clause) x ↔
      CNFClause.eval clause (extendAssignment x) = false := by
  simp only [Fits, clauseCube, Finset.mem_filter, Finset.mem_univ, true_and,
    CNFClause.eval, List.any_eq_false]
  constructor
  · intro h lit hlit
    have hn := h lit.var lit hlit rfl
    cases hp : lit.positive <;> cases hx : x lit.var <;>
      simp_all [CNFLiteral.eval]
  · intro h i lit hlit hvar
    subst i
    have he := h lit hlit
    cases hp : lit.positive <;> cases hx : x lit.var <;>
      simp_all [CNFLiteral.eval]

theorem indicator_clause {n : ℕ} (clause : CNFClause n) (x : Assignment n) :
    cubeIndicator (clauseCube clause) x =
      if CNFClause.eval clause (extendAssignment x) then 0 else 1 := by
  simp only [cubeIndicator, fits_clause]
  by_cases h : CNFClause.eval clause (extendAssignment x) = true
  · simp [h]
  · have hf : CNFClause.eval clause (extendAssignment x) = false := by simp_all
    simp [hf]

abbrev Terms (n : ℕ) := List (ℤ × Cube n)

def termsAt {n : ℕ} (terms : Terms n) (x : Assignment n) : ℤ :=
  (terms.map fun t => t.1 * cubeIndicator t.2 x).sum

def termsMass {n : ℕ} (terms : Terms n) : ℤ :=
  (terms.map fun t => t.1 * cubeMass t.2).sum

def clauseStep {n : ℕ} (clause : CNFClause n) (terms : Terms n) : Terms n :=
  terms ++ terms.map (fun t => (-t.1, joinCube t.2 (clauseCube clause)))

def jointProgram {n : ℕ} : CNFFormula n → Terms n
  | [] => [(1, topCube n)]
  | clause :: rest => clauseStep clause (jointProgram rest)

def jointReadout {n : ℕ} (formula : CNFFormula n) : ℤ :=
  termsMass (jointProgram formula)

def insertTerm {n : ℕ} (t : ℤ × Cube n) : Terms n → Terms n
  | [] => if t.1 = 0 then [] else [t]
  | u :: rest =>
      if t.2 = u.2 then
        if t.1 + u.1 = 0 then rest else (t.1 + u.1, u.2) :: rest
      else u :: insertTerm t rest

def collectTerms {n : ℕ} (terms : Terms n) : Terms n :=
  terms.foldr insertTerm []

def sharedProgram {n : ℕ} : CNFFormula n → Terms n
  | [] => [(1, topCube n)]
  | clause :: rest => collectTerms (clauseStep clause (sharedProgram rest))

def sharedReadout {n : ℕ} (formula : CNFFormula n) : ℤ :=
  termsMass (sharedProgram formula)

theorem insertTerm_at {n : ℕ} (t : ℤ × Cube n) (terms : Terms n)
    (x : Assignment n) :
    termsAt (insertTerm t terms) x = t.1 * cubeIndicator t.2 x + termsAt terms x := by
  induction terms with
  | nil =>
      by_cases h : t.1 = 0 <;> simp [insertTerm, termsAt, h]
  | cons u terms ih =>
      by_cases h : t.2 = u.2
      · by_cases hz : t.1 + u.1 = 0
        · simp [insertTerm, h, hz, termsAt]
          linear_combination -(cubeIndicator u.2 x) * hz
        · simp only [insertTerm, h, if_true, hz, if_false, termsAt,
            List.map_cons, List.sum_cons]
          ring
      · simp only [insertTerm, h, if_false, termsAt, List.map_cons, List.sum_cons] at *
        rw [ih]
        ring

theorem collectTerms_at {n : ℕ} (terms : Terms n) (x : Assignment n) :
    termsAt (collectTerms terms) x = termsAt terms x := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      simp only [collectTerms, List.foldr_cons, insertTerm_at] at *
      rw [ih]
      rfl

theorem termsMass_eq_sum {n : ℕ} (terms : Terms n) :
    termsMass terms = ∑ x : Assignment n, termsAt terms x := by
  induction terms with
  | nil => simp [termsMass, termsAt]
  | cons t terms ih =>
      simp only [termsMass, termsAt, List.map_cons, List.sum_cons] at *
      rw [Finset.sum_add_distrib, ← ih, cubeMass_eq_sum, Finset.mul_sum]

theorem clauseStep_at {n : ℕ} (clause : CNFClause n) (terms : Terms n)
    (x : Assignment n) :
    termsAt (clauseStep clause terms) x =
      termsAt terms x * (1 - cubeIndicator (clauseCube clause) x) := by
  induction terms with
  | nil => simp [termsAt, clauseStep]
  | cons t terms ih =>
      simp only [termsAt, clauseStep, List.map_append, List.map_cons,
        List.map_map, List.sum_append, List.sum_cons,
        indicator_join] at *
      linear_combination ih

theorem jointProgram_at {n : ℕ} (formula : CNFFormula n) (x : Assignment n) :
    termsAt (jointProgram formula) x =
      if CNFFormula.eval formula (extendAssignment x) then 1 else 0 := by
  induction formula with
  | nil => simp [jointProgram, termsAt, CNFFormula.eval]
  | cons clause rest ih =>
      rw [jointProgram, clauseStep_at, ih, indicator_clause]
      simp only [CNFFormula.eval, List.all_cons]
      by_cases hc : CNFClause.eval clause (extendAssignment x) = true <;>
        by_cases hr : rest.all (fun c => CNFClause.eval c (extendAssignment x)) = true <;>
          simp_all

theorem jointReadout_eq_count {n : ℕ} (formula : CNFFormula n) :
    jointReadout formula =
      ((Finset.univ.filter fun x : Assignment n =>
        CNFFormula.eval formula (extendAssignment x) = true).card : ℤ) := by
  rw [jointReadout, termsMass_eq_sum]
  simp only [jointProgram_at, Finset.sum_boole]

theorem sharedProgram_at {n : ℕ} (formula : CNFFormula n) (x : Assignment n) :
    termsAt (sharedProgram formula) x =
      if CNFFormula.eval formula (extendAssignment x) then 1 else 0 := by
  induction formula with
  | nil => simp [sharedProgram, termsAt, CNFFormula.eval]
  | cons clause rest ih =>
      rw [sharedProgram, collectTerms_at, clauseStep_at, ih, indicator_clause]
      simp only [CNFFormula.eval, List.all_cons]
      by_cases hc : CNFClause.eval clause (extendAssignment x) = true <;>
        by_cases hr : rest.all (fun c => CNFClause.eval c (extendAssignment x)) = true <;>
          simp_all

theorem sharedReadout_eq_count {n : ℕ} (formula : CNFFormula n) :
    sharedReadout formula =
      ((Finset.univ.filter fun x : Assignment n =>
        CNFFormula.eval formula (extendAssignment x) = true).card : ℤ) := by
  rw [sharedReadout, termsMass_eq_sum]
  simp only [sharedProgram_at, Finset.sum_boole]

theorem jointProgram_length {n : ℕ} (formula : CNFFormula n) :
    (jointProgram formula).length = 2 ^ formula.length := by
  induction formula with
  | nil => simp [jointProgram]
  | cons clause rest ih =>
      simp [jointProgram, clauseStep, ih, pow_succ, Nat.mul_two]

end SaturationMonoid.ComplexityProjection.SATJoint
