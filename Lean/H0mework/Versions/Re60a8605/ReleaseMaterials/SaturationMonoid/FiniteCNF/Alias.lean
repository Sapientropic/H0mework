import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Factor

/-!
# Source-generated Boolean aliases from complementary binary clauses

The original clause list generates a pair and its membership proofs. Replacing
one variable by the corresponding literal removes an actual source coordinate;
an explicit assignment lift preserves the original satisfying slice. The ambient
variable bound stays fixed, so the contract is SAT preservation, not count or
Hamiltonian equality. Recursive contraction is followed by the original Factor
decision program.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Alias

def negate {n : Nat} (lit : CNFLiteral n) : CNFLiteral n :=
  { lit with positive := !lit.positive }

@[simp] theorem negate_eval {n : Nat} (lit : CNFLiteral n) (assignment : Nat → Bool) :
    (negate lit).eval assignment = !(lit.eval assignment) := by
  cases h : lit.positive <;> simp [negate, CNFLiteral.eval, h]

/-- Both clause occurrences and the nontrivial coordinate relation come from the source. -/
structure Pair {n : Nat} (formula : CNFFormula n) where
  left : CNFLiteral n
  right : CNFLiteral n
  different : left.var ≠ right.var
  first_mem : [left, right] ∈ formula
  opposite_mem : [negate left, negate right] ∈ formula ∨
    [negate right, negate left] ∈ formula

def inspectClause {n : Nat} (formula : CNFFormula n)
    (clause : { c : CNFClause n // c ∈ formula }) : Option (Pair formula) :=
  match hc : clause.val with
  | [a, b] =>
      if different : a.var ≠ b.var then
        if opposite : [negate a, negate b] ∈ formula ∨
            [negate b, negate a] ∈ formula then
          some ⟨a, b, different, hc ▸ clause.property, opposite⟩
        else none
      else none
  | _ => none

/-- The executable scanner takes only the original formula. -/
def scan {n : Nat} (formula : CNFFormula n) : Option (Pair formula) :=
  formula.attach.findSome? (inspectClause formula)

def replaceLiteral {n : Nat} (a b lit : CNFLiteral n) : CNFLiteral n :=
  if lit.var = b.var then
    ⟨a.var, if lit.positive = b.positive then !a.positive else a.positive⟩
  else lit

def replaceFormula {n : Nat} (formula : CNFFormula n) (a b : CNFLiteral n) : CNFFormula n :=
  formula.map fun clause => clause.map (replaceLiteral a b)

/-- Restore the removed variable from the retained literal's truth value. -/
def liftAssignment {n : Nat} (a b : CNFLiteral n) (assignment : Nat → Bool) : Nat → Bool :=
  fun i => if i = b.var.val then
    (if b.positive then !(a.eval assignment) else a.eval assignment)
  else assignment i

theorem replaceLiteral_eval {n : Nat} (a b lit : CNFLiteral n)
    (assignment : Nat → Bool) :
    (replaceLiteral a b lit).eval assignment =
      lit.eval (liftAssignment a b assignment) := by
  by_cases hv : lit.var = b.var
  · cases ha : a.positive <;> cases hb : b.positive <;> cases hl : lit.positive <;>
      simp [replaceLiteral, liftAssignment, CNFLiteral.eval, hv, ha, hb, hl]
  · have hv' : lit.var.val ≠ b.var.val := fun h => hv (Fin.ext h)
    simp [replaceLiteral, liftAssignment, CNFLiteral.eval, hv, hv']

theorem replaceFormula_eval {n : Nat} (formula : CNFFormula n) (a b : CNFLiteral n)
    (assignment : Nat → Bool) :
    CNFFormula.eval (replaceFormula formula a b) assignment =
      CNFFormula.eval formula (liftAssignment a b assignment) := by
  simp only [replaceFormula, CNFFormula.eval, List.all_map, CNFClause.eval,
    Function.comp_def, List.any_map]
  congr 1
  funext clause
  congr 1
  funext lit
  exact replaceLiteral_eval a b lit assignment

theorem Pair.literal_relation {n : Nat} {formula : CNFFormula n} (pair : Pair formula)
    (assignment : Nat → Bool) (satisfies : CNFFormula.eval formula assignment = true) :
    pair.right.eval assignment = !(pair.left.eval assignment) := by
  have clauses := List.all_eq_true.mp satisfies
  have first := clauses _ pair.first_mem
  have opposite :
      (!(pair.left.eval assignment) || !(pair.right.eval assignment)) = true := by
    rcases pair.opposite_mem with forward | backward
    · simpa [CNFClause.eval] using clauses _ forward
    · simpa [CNFClause.eval, Bool.or_comm] using clauses _ backward
  simp only [CNFClause.eval, List.any_cons, List.any_nil, Bool.or_false] at first
  cases ha : pair.left.eval assignment <;> cases hb : pair.right.eval assignment <;>
    simp_all

/-- Every original satisfying assignment already lies on the generated alias slice. -/
theorem Pair.lift_fixed {n : Nat} {formula : CNFFormula n} (pair : Pair formula)
    (assignment : Nat → Bool) (satisfies : CNFFormula.eval formula assignment = true) :
    liftAssignment pair.left pair.right assignment = assignment := by
  have relation := pair.literal_relation assignment satisfies
  funext i
  by_cases hi : i = pair.right.var.val
  · subst i
    cases hb : pair.right.positive
    · have equal := congrArg Bool.not relation
      simpa [liftAssignment, CNFLiteral.eval, hb] using equal.symm
    · simpa [liftAssignment, CNFLiteral.eval, hb] using relation.symm
  · simp [liftAssignment, hi]

def contract {n : Nat} {formula : CNFFormula n} (pair : Pair formula) : CNFFormula n :=
  replaceFormula formula pair.left pair.right

theorem contract_eval {n : Nat} {formula : CNFFormula n} (pair : Pair formula)
    (assignment : Nat → Bool) :
    CNFFormula.eval (contract pair) assignment =
      CNFFormula.eval formula (liftAssignment pair.left pair.right assignment) :=
  replaceFormula_eval formula pair.left pair.right assignment

theorem contract_sat {n : Nat} {formula : CNFFormula n} (pair : Pair formula) :
    CNFSatisfiable (contract pair) ↔ CNFSatisfiable formula := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact ⟨liftAssignment pair.left pair.right assignment, (contract_eval pair assignment).symm ▸ satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    refine ⟨assignment, ?_⟩
    rw [contract_eval, pair.lift_fixed assignment satisfies]
    exact satisfies

def activeVars {n : Nat} (formula : CNFFormula n) : Finset (Fin n) :=
  (Shared.sourceVars formula).toFinset

theorem mem_activeVars {n : Nat} (formula : CNFFormula n) (v : Fin n) :
    v ∈ activeVars formula ↔
      ∃ clause ∈ formula, ∃ lit ∈ clause, lit.var = v := by
  simp only [activeVars, List.mem_toFinset, Shared.sourceVars, List.mem_dedup,
    List.mem_map, List.mem_flatten]
  constructor
  · rintro ⟨lit, ⟨clause, hc, hl⟩, hv⟩
    exact ⟨clause, hc, lit, hl, hv⟩
  · rintro ⟨clause, hc, lit, hl, hv⟩
    exact ⟨lit, ⟨clause, hc, hl⟩, hv⟩

/-- The contraction removes exactly its eliminated source variable. -/
theorem activeVars_contract {n : Nat} {formula : CNFFormula n} (pair : Pair formula) :
    activeVars (contract pair) = (activeVars formula).erase pair.right.var := by
  have ha : pair.left.var ∈ activeVars formula :=
    (mem_activeVars formula pair.left.var).mpr
      ⟨[pair.left, pair.right], pair.first_mem, pair.left, by simp, rfl⟩
  ext v
  rw [Finset.mem_erase, mem_activeVars]
  constructor
  · rintro ⟨clause, hc, lit, hl, hv⟩
    change clause ∈ formula.map (fun c => c.map (replaceLiteral pair.left pair.right)) at hc
    obtain ⟨oldClause, oldClauseMem, clauseEq⟩ := List.mem_map.mp hc
    subst clause
    obtain ⟨oldLit, oldLitMem, litEq⟩ := List.mem_map.mp hl
    subst lit
    by_cases hvar : oldLit.var = pair.right.var
    · have heq : v = pair.left.var := by
        simpa [replaceLiteral, hvar] using hv.symm
      rw [heq]
      exact ⟨pair.different, ha⟩
    · have heq : oldLit.var = v := by simpa [replaceLiteral, hvar] using hv
      exact ⟨heq ▸ hvar,
        (mem_activeVars formula v).mpr ⟨oldClause, oldClauseMem, oldLit, oldLitMem, heq⟩⟩
  · rintro ⟨different, mem⟩
    obtain ⟨clause, hc, lit, hl, hv⟩ := (mem_activeVars formula v).mp mem
    have hvar : lit.var ≠ pair.right.var := hv ▸ different
    refine ⟨clause.map (replaceLiteral pair.left pair.right),
      List.mem_map.mpr ⟨clause, hc, rfl⟩, replaceLiteral pair.left pair.right lit,
      List.mem_map.mpr ⟨lit, hl, rfl⟩, ?_⟩
    simp only [replaceLiteral, if_neg hvar]
    exact hv

theorem activeVars_contract_lt {n : Nat} {formula : CNFFormula n} (pair : Pair formula) :
    (activeVars (contract pair)).card < (activeVars formula).card := by
  have hb : pair.right.var ∈ activeVars formula :=
    (mem_activeVars formula pair.right.var).mpr
      ⟨[pair.left, pair.right], pair.first_mem, pair.right, by simp, rfl⟩
  rw [activeVars_contract, Finset.card_erase_of_mem hb]
  have positive := Finset.card_pos.mpr ⟨pair.right.var, hb⟩
  omega

def reduceFuel {n : Nat} : Nat → CNFFormula n → CNFFormula n
  | 0, formula => formula
  | fuel + 1, formula =>
      match scan formula with
      | none => formula
      | some pair => reduceFuel fuel (contract pair)

def liftFuel {n : Nat} : Nat → CNFFormula n → (Nat → Bool) → (Nat → Bool)
  | 0, _, assignment => assignment
  | fuel + 1, formula, assignment =>
      match scan formula with
      | none => assignment
      | some pair => liftAssignment pair.left pair.right
          (liftFuel fuel (contract pair) assignment)

/-- Replay all generated aliases to read a final assignment on the original source. -/
theorem reduceFuel_eval {n : Nat} (fuel : Nat) (formula : CNFFormula n)
    (assignment : Nat → Bool) :
    CNFFormula.eval (reduceFuel fuel formula) assignment =
      CNFFormula.eval formula (liftFuel fuel formula assignment) := by
  induction fuel generalizing formula with
  | zero => rfl
  | succ fuel ih =>
      cases found : scan formula with
      | none => simp [reduceFuel, liftFuel, found]
      | some pair =>
          simp only [reduceFuel, liftFuel, found]
          rw [ih, contract_eval]

theorem reduceFuel_sat {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    CNFSatisfiable (reduceFuel fuel formula) ↔ CNFSatisfiable formula := by
  induction fuel generalizing formula with
  | zero => rfl
  | succ fuel ih =>
      cases found : scan formula with
      | none => simp [reduceFuel, found]
      | some pair =>
          simp only [reduceFuel, found]
          exact (ih (contract pair)).trans (contract_sat pair)

theorem reduceFuel_exhausted {n : Nat} (fuel : Nat) (formula : CNFFormula n)
    (enough : (activeVars formula).card ≤ fuel) : scan (reduceFuel fuel formula) = none := by
  induction fuel generalizing formula with
  | zero =>
      change scan formula = none
      cases found : scan formula with
      | none => rfl
      | some pair =>
          have smaller := activeVars_contract_lt pair
          omega
  | succ fuel ih =>
      cases found : scan formula with
      | none =>
          have unchanged : reduceFuel (fuel + 1) formula = formula := by
            simp [reduceFuel, found]
          rw [unchanged]
          exact found
      | some pair =>
          have next : reduceFuel (fuel + 1) formula = reduceFuel fuel (contract pair) := by
            simp [reduceFuel, found]
          rw [next]
          apply ih
          have smaller := activeVars_contract_lt pair
          omega

def reduce {n : Nat} (formula : CNFFormula n) : CNFFormula n :=
  reduceFuel (activeVars formula).card formula

theorem reduce_sat {n : Nat} (formula : CNFFormula n) :
    CNFSatisfiable (reduce formula) ↔ CNFSatisfiable formula := reduceFuel_sat _ _

theorem reduce_exhausted {n : Nat} (formula : CNFFormula n) : scan (reduce formula) = none :=
  reduceFuel_exhausted _ _ (Nat.le_refl _)

/-- Contract all source-generated aliases, then run the certified component decision program. -/
def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  Factor.decideFormula (reduce formula)

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  exact (Factor.decideFormula_correct (reduce formula)).trans (reduce_sat formula)

theorem decideFormula_no {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = false ↔ ¬ CNFSatisfiable formula := by
  rw [Bool.eq_false_iff]
  exact not_congr (decideFormula_correct formula)

theorem replaceFormula_clauseLengths {n : Nat} (formula : CNFFormula n)
    (a b : CNFLiteral n) :
    (replaceFormula formula a b).map List.length = formula.map List.length := by
  simp [replaceFormula, List.map_map]

theorem reduceFuel_clauseLengths {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    (reduceFuel fuel formula).map List.length = formula.map List.length := by
  induction fuel generalizing formula with
  | zero => rfl
  | succ fuel ih =>
      cases found : scan formula with
      | none => simp [reduceFuel, found]
      | some pair =>
          simp only [reduceFuel, found, ih, contract,
            replaceFormula_clauseLengths]

theorem reduce_clauseLengths {n : Nat} (formula : CNFFormula n) :
    (reduce formula).map List.length = formula.map List.length :=
  reduceFuel_clauseLengths _ _

theorem reduce_length {n : Nat} (formula : CNFFormula n) :
    (reduce formula).length = formula.length := by
  simpa using congrArg List.length (reduce_clauseLengths formula)

theorem reduce_literals {n : Nat} (formula : CNFFormula n) :
    (reduce formula).flatten.length = formula.flatten.length := by
  simp only [List.length_flatten, reduce_clauseLengths]

end SaturationMonoid.ComplexityProjection.SATSource.Alias
