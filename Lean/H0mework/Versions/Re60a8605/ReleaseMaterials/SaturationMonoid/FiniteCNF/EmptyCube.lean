import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.CubeWords
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FaceBudget
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Spectrum

/-!
Empty source cylinders are detected from their actual finite coordinates or
their generated two-bit cells.  Removing these cylinders preserves the full
source function.  The same detector removes tautological original clauses
before their occurrence graph is consumed.
-/

namespace SaturationMonoid.ComplexityProjection.SATJoint

def emptyCube {n : ℕ} (c : Cube n) : Bool :=
  (List.finRange n).any fun i => decide (c i = ∅)

theorem emptyCube_true_iff_coordinate {n : ℕ} (c : Cube n) :
    emptyCube c = true ↔ ∃ i, c i = ∅ := by
  simp [emptyCube, List.any_eq_true]

def cubeChoice {n : ℕ} (c : Cube n) : Assignment n :=
  fun i => if false ∈ c i then false else true

theorem cubeChoice_fits {n : ℕ} (c : Cube n) (h : emptyCube c = false) :
    Fits c (cubeChoice c) := by
  intro i
  have hne : c i ≠ ∅ := by
    intro he
    have hh := (emptyCube_true_iff_coordinate c).mpr ⟨i, he⟩
    simp [h] at hh
  by_cases hf : false ∈ c i
  · simp [cubeChoice, hf]
  · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    cases b with
    | false => exact False.elim (hf hb)
    | true => simpa [cubeChoice, hf] using hb

theorem emptyCube_true_iff_indicator {n : ℕ} (c : Cube n) :
    emptyCube c = true ↔ ∀ x : Assignment n, cubeIndicator c x = 0 := by
  constructor
  · intro h x
    obtain ⟨i, hi⟩ := (emptyCube_true_iff_coordinate c).mp h
    have hn : ¬ Fits c x := by
      intro hf
      have hm := hf i
      simp [hi] at hm
    simp [cubeIndicator, hn]
  · intro h
    by_cases he : emptyCube c = true
    · exact he
    · have hf : emptyCube c = false := by simpa using he
      have hx := h (cubeChoice c)
      simp [cubeIndicator, cubeChoice_fits c hf] at hx

/-- Inspect two membership bits at a time; stop at the first empty cell. -/
def emptyCode : List Bool → Bool
  | a :: b :: rest => if a || b then emptyCode rest else true
  | _ => false

def emptyCodeCells : List Bool → ℕ
  | a :: b :: rest => 1 + if a || b then emptyCodeCells rest else 0
  | _ => 0

theorem emptyCode_pack (pairs : List (Bool × Bool)) :
    emptyCode (CubeWords.pack pairs) = pairs.any (fun p => !p.1 && !p.2) := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
      obtain ⟨a, b⟩ := p
      cases a <;> cases b <;> simp [CubeWords.pack, emptyCode, ih]

theorem emptyCode_correct {n : ℕ} (c : Cube n) :
    emptyCode (CubeWords.code c) = emptyCube c := by
  apply Bool.eq_iff_iff.mpr
  rw [emptyCube_true_iff_coordinate, CubeWords.code, emptyCode_pack]
  simp only [List.any_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨p, ⟨i, rfl⟩, hp⟩
    refine ⟨i, ?_⟩
    have hh : false ∉ c i ∧ true ∉ c i := by simpa using hp
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    cases b with
    | false => exact hh.1 hb
    | true => exact hh.2 hb
  · rintro ⟨i, hi⟩
    exact ⟨_, ⟨i, rfl⟩, by simp [hi]⟩

theorem emptyCodeCells_bound (word : List Bool) :
    2 * emptyCodeCells word ≤ word.length := by
  induction word using emptyCodeCells.induct with
  | case1 a b rest ih =>
      cases a <;> cases b <;> simp [emptyCodeCells] at * <;> omega
  | case2 word h =>
      cases word with
      | nil => simp [emptyCodeCells]
      | cons a rest =>
          cases rest with
          | nil => simp [emptyCodeCells]
          | cons b rest => exact False.elim (h a b rest rfl)

theorem emptyCodeCells_source {n : ℕ} (c : Cube n) :
    emptyCodeCells (CubeWords.code c) ≤ n := by
  have h := emptyCodeCells_bound (CubeWords.code c)
  rw [CubeWords.code_length] at h
  omega

def removeEmpty {n : ℕ} (terms : Terms n) : Terms n :=
  terms.filter fun t => !emptyCube t.2

theorem removeEmpty_at {n : ℕ} (terms : Terms n) (x : Assignment n) :
    termsAt (removeEmpty terms) x = termsAt terms x := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      cases he : emptyCube t.2 with
      | false => simp [removeEmpty, he, termsAt] at ih ⊢; exact ih
      | true =>
          have hz := (emptyCube_true_iff_indicator t.2).mp he x
          simp [removeEmpty, he, termsAt, hz] at ih ⊢
          exact ih

theorem removeEmpty_mass {n : ℕ} (terms : Terms n) :
    termsMass (removeEmpty terms) = termsMass terms := by
  simp only [termsMass_eq_sum, removeEmpty_at]

theorem removeEmpty_future {n : ℕ} (future : CNFFormula n) (terms : Terms n) :
    formulaMass future (removeEmpty terms) = formulaMass future terms := by
  simp only [formulaMass, termsMass_eq_sum, applyFormula_at, removeEmpty_at]

theorem removeEmpty_length_le {n : ℕ} (terms : Terms n) :
    (removeEmpty terms).length ≤ terms.length := List.length_filter_le _ _

theorem removeEmpty_weight_le {n : ℕ} (terms : Terms n) :
    termsWeight (removeEmpty terms) ≤ termsWeight terms := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      cases he : emptyCube t.2 <;>
        simp only [removeEmpty, List.filter_cons, he, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, if_true, if_false, termsWeight, List.map_cons, List.sum_cons] at * <;> omega

def tautologyClause {n : ℕ} (clause : CNFClause n) : Bool :=
  emptyCode (CubeWords.clauseCode clause)

theorem tautologyClause_eq_empty {n : ℕ} (clause : CNFClause n) :
    tautologyClause clause = emptyCube (clauseCube clause) := by
  rw [tautologyClause, CubeWords.clauseCode_correct, emptyCode_correct]

theorem tautologyClause_true_iff {n : ℕ} (clause : CNFClause n) :
    tautologyClause clause = true ↔
      ∀ assignment : ℕ → Bool, CNFClause.eval clause assignment = true := by
  rw [tautologyClause_eq_empty, emptyCube_true_iff_indicator]
  constructor
  · intro h assignment
    have hz := h (fun i => assignment i.val)
    rw [indicator_clause] at hz
    have hf : CNFClause.eval clause (extendAssignment fun i : Fin n => assignment i.val) = true := by
      by_cases he : CNFClause.eval clause (extendAssignment fun i : Fin n => assignment i.val) = true
      · exact he
      · simp [he] at hz
    exact (SATSource.clause_eval_restrict clause assignment).symm.trans hf
  · intro h x
    simp [indicator_clause, h (extendAssignment x)]

def dropTautologies {n : ℕ} (formula : CNFFormula n) : CNFFormula n :=
  formula.filter fun clause => !tautologyClause clause

theorem dropTautologies_eval {n : ℕ} (formula : CNFFormula n) (assignment : ℕ → Bool) :
    CNFFormula.eval (dropTautologies formula) assignment = CNFFormula.eval formula assignment := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases ht : tautologyClause clause with
      | false =>
          simp [dropTautologies, ht, CNFFormula.eval] at ih ⊢
          exact congrArg (fun b => CNFClause.eval clause assignment && b) ih
      | true =>
          have hc := (tautologyClause_true_iff clause).mp ht assignment
          simp [dropTautologies, ht, CNFFormula.eval, hc] at ih ⊢
          exact ih

theorem dropTautologies_length_le {n : ℕ} (formula : CNFFormula n) :
    (dropTautologies formula).length ≤ formula.length := List.length_filter_le _ _

def cleanFaceRun {n : ℕ} (coords : List (Fin n × Bool)) :
    CNFFormula n → Terms n → Terms n
  | [], terms => removeEmpty terms
  | clause :: rest, terms => cleanFaceRun coords rest
      (retireTerms (retireAfter clause rest)
        (collectTerms (facePass coords (removeEmpty (clauseStep clause terms)))))

def cleanReadout {n : ℕ} (formula : CNFFormula n) : ℤ :=
  let cleaned := dropTautologies formula
  termsMass (cleanFaceRun (sourceCoordinates cleaned) cleaned [(1, topCube n)])

theorem cleanFaceRun_mass {n : ℕ} (coords : List (Fin n × Bool))
    (formula : CNFFormula n) (terms : Terms n) :
    termsMass (cleanFaceRun coords formula terms) = formulaMass formula terms := by
  induction formula generalizing terms with
  | nil => exact removeEmpty_mass terms
  | cons clause rest ih =>
      rw [cleanFaceRun, ih, retireTerms_preserves _ rest _ (retireAfter_absent clause rest),
        formulaMass_collect, facePass_future, removeEmpty_future]
      rfl

theorem cleanReadout_eq_count {n : ℕ} (formula : CNFFormula n) :
    cleanReadout formula =
      ((Finset.univ.filter fun x : Assignment n =>
        CNFFormula.eval formula (extendAssignment x) = true).card : ℤ) := by
  rw [cleanReadout, cleanFaceRun_mass]
  simp only [formulaMass, termsMass_eq_sum]
  simp only [applyFormula_at, dropTautologies_eval]
  simp only [termsAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    indicator_top, mul_one, add_zero, one_mul, Finset.sum_boole]

end SaturationMonoid.ComplexityProjection.SATJoint
