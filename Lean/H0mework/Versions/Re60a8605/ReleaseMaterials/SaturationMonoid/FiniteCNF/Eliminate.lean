import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Eliminate.Normalize
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Subsumption

/-!
Source-generated existential resolution with a non-increasing clause budget.
The scanner checks each actually generated, normalized candidate.  Assignments
are lifted by an explicit bit computed from the same original clause partition.
-/

namespace SaturationMonoid.ComplexityProjection.SATSource.Eliminate

def strip {n : Nat} (v : Fin n) (clause : CNFClause n) : CNFClause n :=
  clause.filter fun lit => decide (lit.var ≠ v)

def positive {n : Nat} (formula : CNFFormula n) (v : Fin n) : CNFFormula n :=
  (formula.filter fun clause =>
    clauseContainsLiteral clause v true && !clauseContainsLiteral clause v false).map (strip v)

def negative {n : Nat} (formula : CNFFormula n) (v : Fin n) : CNFFormula n :=
  (formula.filter fun clause =>
    clauseContainsLiteral clause v false && !clauseContainsLiteral clause v true).map (strip v)

def neutral {n : Nat} (formula : CNFFormula n) (v : Fin n) : CNFFormula n :=
  formula.filter fun clause =>
    !clauseContainsLiteral clause v true && !clauseContainsLiteral clause v false

theorem no_var_of_absent {n : Nat} (clause : CNFClause n) (v : Fin n)
    (hp : clauseContainsLiteral clause v true = false)
    (hn : clauseContainsLiteral clause v false = false) :
    ∀ lit ∈ clause, lit.var ≠ v := by
  intro lit hl hv
  have hm : clauseContainsLiteral clause v lit.positive = true := by
    exact List.any_eq_true.mpr ⟨lit, hl, by simp [literalMatches, hv]⟩
  cases hb : lit.positive <;> simp_all

theorem strip_of_absent {n : Nat} (clause : CNFClause n) (v : Fin n)
    (hp : clauseContainsLiteral clause v true = false)
    (hn : clauseContainsLiteral clause v false = false) : strip v clause = clause := by
  apply List.filter_eq_self.mpr
  intro lit hl
  exact decide_eq_true (no_var_of_absent clause v hp hn lit hl)

theorem clause_forced {n : Nat} (clause : CNFClause n) (v : Fin n) (bit : Bool)
    (assignment : Nat → Bool) :
    CNFClause.eval clause (forceAssignment v bit assignment) =
      (clauseContainsLiteral clause v bit || CNFClause.eval (strip v clause) assignment) := by
  induction clause with
  | nil => simp [CNFClause.eval, clauseContainsLiteral, strip]
  | cons lit rest ih =>
      by_cases hv : lit.var = v
      · cases hp : lit.positive <;> cases bit <;>
          simp [CNFClause.eval, clauseContainsLiteral, strip, literalMatches,
            forceAssignment, CNFLiteral.eval, hv, hp] at ih ⊢ <;> exact ih
      · have he := literal_eval_force_eq_of_ne v bit assignment lit hv
        simp only [CNFClause.eval, List.any_cons] at ih he ⊢
        simp [clauseContainsLiteral, strip, literalMatches, hv, he, ih,
          Bool.or_left_comm]

theorem partition_forced {n : Nat} (formula : CNFFormula n) (v : Fin n) (bit : Bool)
    (assignment : Nat → Bool) :
    CNFFormula.eval formula (forceAssignment v bit assignment) =
      (CNFFormula.eval (neutral formula v) assignment &&
        ((bit || CNFFormula.eval (positive formula v) assignment) &&
          (!bit || CNFFormula.eval (negative formula v) assignment))) := by
  induction formula with
  | nil => simp [CNFFormula.eval, neutral, positive, negative]
  | cons clause rest ih =>
      simp only [CNFFormula.eval, List.all_cons] at ih ⊢
      rw [clause_forced, ih]
      cases hp : clauseContainsLiteral clause v true <;>
        cases hn : clauseContainsLiteral clause v false <;> cases bit <;>
          simp [neutral, positive, negative, hp, hn,
            Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
      all_goals rw [strip_of_absent clause v hp hn]

def resolvents {n : Nat} (left right : CNFFormula n) : CNFFormula n :=
  left.flatMap fun a => right.map fun b => a ++ b

theorem resolvents_eval {n : Nat} (left right : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (resolvents left right) assignment =
      (CNFFormula.eval left assignment || CNFFormula.eval right assignment) := by
  apply Bool.eq_iff_iff.mpr
  simp only [CNFFormula.eval, List.all_eq_true, Bool.or_eq_true]
  constructor
  · intro h
    by_cases hl : ∀ c ∈ left, CNFClause.eval c assignment = true
    · exact Or.inl hl
    · right
      intro b hb
      by_cases hv : CNFClause.eval b assignment = true
      · exact hv
      · apply False.elim
        apply hl
        intro a ha
        have hh := h (a ++ b) (List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩)
        have hor : CNFClause.eval a assignment = true ∨ CNFClause.eval b assignment = true := by
          simpa only [CNFClause.eval, List.any_append, Bool.or_eq_true] using hh
        exact hor.resolve_right hv
  · rintro (h | h) c hc
    · obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      simpa only [CNFClause.eval, List.any_append] using
        (Bool.or_eq_true_iff.mpr (Or.inl (h a ha)) :
          (CNFClause.eval a assignment || CNFClause.eval b assignment) = true)
    · obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      simpa only [CNFClause.eval, List.any_append] using
        (Bool.or_eq_true_iff.mpr (Or.inr (h b hb)) :
          (CNFClause.eval a assignment || CNFClause.eval b assignment) = true)

def residual {n : Nat} (formula : CNFFormula n) (v : Fin n) : CNFFormula n :=
  neutral formula v ++ resolvents (positive formula v) (negative formula v)

theorem residual_eval {n : Nat} (formula : CNFFormula n) (v : Fin n) (assignment : Nat → Bool) :
    CNFFormula.eval (residual formula v) assignment =
      (CNFFormula.eval (neutral formula v) assignment &&
        (CNFFormula.eval (positive formula v) assignment || CNFFormula.eval (negative formula v) assignment)) := by
  simpa only [residual, CNFFormula.eval, List.all_append] using
    congrArg (fun b => CNFFormula.eval (neutral formula v) assignment && b)
      (resolvents_eval (positive formula v) (negative formula v) assignment)

def lift {n : Nat} (formula : CNFFormula n) (v : Fin n) (assignment : Nat → Bool) : Nat → Bool :=
  forceAssignment v (!(CNFFormula.eval (positive formula v) assignment)) assignment

theorem residual_lift {n : Nat} (formula : CNFFormula n) (v : Fin n) (assignment : Nat → Bool) :
    CNFFormula.eval (residual formula v) assignment = CNFFormula.eval formula (lift formula v assignment) := by
  rw [lift, partition_forced, residual_eval]
  cases CNFFormula.eval (positive formula v) assignment <;> simp

theorem residual_of_satisfies {n : Nat} (formula : CNFFormula n) (v : Fin n)
    (assignment : Nat → Bool) (h : CNFFormula.eval formula assignment = true) :
    CNFFormula.eval (residual formula v) assignment = true := by
  have hf := partition_forced formula v (assignment v.val) assignment
  rw [forceAssignment_eq_self_of_value v (assignment v.val) assignment rfl, h] at hf
  rw [residual_eval]
  have hn := (Bool.and_eq_true_iff.mp hf.symm).1
  have hs := (Bool.and_eq_true_iff.mp hf.symm).2
  simp only [hn, Bool.true_and]
  cases hb : assignment v.val with
  | false =>
      have hp : CNFFormula.eval (positive formula v) assignment = true := by simpa [hb] using hs
      exact Bool.or_eq_true_iff.mpr (Or.inl hp)
  | true =>
      have hm : CNFFormula.eval (negative formula v) assignment = true := by simpa [hb] using hs
      exact Bool.or_eq_true_iff.mpr (Or.inr hm)

theorem residual_sat {n : Nat} (formula : CNFFormula n) (v : Fin n) :
    CNFSatisfiable (residual formula v) ↔ CNFSatisfiable formula := by
  constructor
  · rintro ⟨assignment, h⟩
    exact ⟨lift formula v assignment, (residual_lift formula v assignment).symm.trans h⟩
  · rintro ⟨assignment, h⟩
    exact ⟨assignment, residual_of_satisfies formula v assignment h⟩

theorem partition_length_le {n : Nat} (formula : CNFFormula n) (v : Fin n) :
    (neutral formula v).length + (positive formula v).length + (negative formula v).length ≤ formula.length := by
  induction formula with
  | nil => simp [neutral, positive, negative]
  | cons clause rest ih =>
      cases hp : clauseContainsLiteral clause v true <;>
        cases hn : clauseContainsLiteral clause v false <;>
          simp [neutral, positive, negative, hp, hn] at ih ⊢ <;> omega

theorem resolvents_length {n : Nat} (left right : CNFFormula n) :
    (resolvents left right).length = left.length * right.length := by
  simp [resolvents, List.length_flatMap]

theorem residual_length_bound {n : Nat} (formula : CNFFormula n) (v : Fin n) :
    (residual formula v).length ≤ formula.length + formula.length ^ 2 := by
  have hb := partition_length_le formula v
  simp only [residual, List.length_append, resolvents_length]
  have hp : (positive formula v).length ≤ formula.length := by omega
  have hn : (negative formula v).length ≤ formula.length := by omega
  have hm := Nat.mul_le_mul hp hn
  nlinarith

theorem stripped_origin {n : Nat} (formula : CNFFormula n) (v : Fin n)
    (pick : CNFClause n → Bool) (clause : CNFClause n) (hc : clause ∈ (formula.filter pick).map (strip v))
    (lit : CNFLiteral n) (hl : lit ∈ clause) :
    lit.var ≠ v ∧ ∃ original ∈ formula, lit ∈ original := by
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hl, hn⟩ := List.mem_filter.mp hl
  exact ⟨of_decide_eq_true hn, original, (List.mem_filter.mp ho).1, hl⟩

theorem neutral_origin {n : Nat} (formula : CNFFormula n) (v : Fin n)
    (clause : CNFClause n) (hc : clause ∈ neutral formula v)
    (lit : CNFLiteral n) (hl : lit ∈ clause) :
    lit.var ≠ v ∧ ∃ original ∈ formula, lit ∈ original := by
  obtain ⟨hc, hparts⟩ := List.mem_filter.mp hc
  have hp : clauseContainsLiteral clause v true = false := by
    simpa using (Bool.and_eq_true_iff.mp hparts).1
  have hn : clauseContainsLiteral clause v false = false := by
    simpa using (Bool.and_eq_true_iff.mp hparts).2
  exact ⟨no_var_of_absent clause v hp hn lit hl, clause, hc, hl⟩

theorem residual_origin {n : Nat} (formula : CNFFormula n) (v : Fin n)
    (clause : CNFClause n) (hc : clause ∈ residual formula v)
    (lit : CNFLiteral n) (hl : lit ∈ clause) :
    lit.var ≠ v ∧ ∃ original ∈ formula, lit ∈ original := by
  rcases List.mem_append.mp hc with hc | hc
  · exact neutral_origin formula v clause hc lit hl
  · obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    rcases List.mem_append.mp hl with hl | hl
    · exact stripped_origin formula v _ a ha lit hl
    · exact stripped_origin formula v _ b hb lit hl

theorem residual_active_subset {n : Nat} (formula : CNFFormula n) (v : Fin n) :
    Alias.activeVars (residual formula v) ⊆ (Alias.activeVars formula).erase v := by
  intro u hu
  obtain ⟨clause, hc, lit, hl, he⟩ := (Alias.mem_activeVars _ _).mp hu
  obtain ⟨hne, original, ho, hl⟩ := residual_origin formula v clause hc lit hl
  exact Finset.mem_erase.mpr ⟨he ▸ hne, (Alias.mem_activeVars _ _).mpr ⟨original, ho, lit, hl, he⟩⟩

def candidate {n : Nat} (formula : CNFFormula n) (v : Fin n) : CNFFormula n :=
  Subsumption.reduce (residual (normalize formula) v)

theorem candidate_eval {n : Nat} (formula : CNFFormula n) (v : Fin n) (assignment : Nat → Bool) :
    CNFFormula.eval (candidate formula v) assignment =
      CNFFormula.eval formula (lift (normalize formula) v assignment) := by
  rw [candidate, Subsumption.reduce_eval, residual_lift, normalize_eval]

theorem candidate_sat {n : Nat} (formula : CNFFormula n) (v : Fin n) :
    CNFSatisfiable (candidate formula v) ↔ CNFSatisfiable formula := by
  simp only [candidate, CNFSatisfiable, Subsumption.reduce_eval]
  exact (residual_sat (normalize formula) v).trans (normalize_sat formula)

theorem candidate_active_subset {n : Nat} (formula : CNFFormula n) (v : Fin n) :
    Alias.activeVars (candidate formula v) ⊆ (Alias.activeVars (normalize formula)).erase v :=
  (Subsumption.reduce_active_subset _).trans (residual_active_subset _ _)

theorem candidate_raw_length_bound {n : Nat} (formula : CNFFormula n) (v : Fin n) :
    (candidate formula v).length ≤ formula.length + formula.length ^ 2 := by
  have hr := (Subsumption.reduce_length_le (residual (normalize formula) v)).trans
    (residual_length_bound (normalize formula) v)
  have hn := normalize_length_le formula
  have hs := Nat.mul_le_mul hn hn
  change (candidate formula v).length ≤ _ at hr
  nlinarith

theorem candidate_clause_bound {n : Nat} (formula : CNFFormula n) (v : Fin n)
    (clause : CNFClause n) (h : clause ∈ candidate formula v) : clause.length ≤ 2 * n :=
  Subsumption.reduce_clause_bound _ clause h

theorem stripped_clause_bound {n : Nat} (formula : CNFFormula n) (v : Fin n)
    (pick : CNFClause n → Bool) (clause : CNFClause n)
    (h : clause ∈ (formula.filter pick).map (strip v))
    (bounded : ∀ c ∈ formula, c.length ≤ 2 * n) : clause.length ≤ 2 * n := by
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp h
  exact (List.length_filter_le _ _).trans (bounded original (List.mem_filter.mp ho).1)

theorem resolution_stage_clause_bound {n : Nat} (formula : CNFFormula n) (v : Fin n)
    (clause : CNFClause n) (h : clause ∈ residual (normalize formula) v) : clause.length ≤ 4 * n := by
  rcases List.mem_append.mp h with h | h
  · have hc := normalize_clause_bound formula clause (List.mem_filter.mp h).1
    omega
  · obtain ⟨a, ha, h⟩ := List.mem_flatMap.mp h
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
    have ha' := stripped_clause_bound (normalize formula) v _ a ha (normalize_clause_bound formula)
    have hb' := stripped_clause_bound (normalize formula) v _ b hb (normalize_clause_bound formula)
    simp only [List.length_append]
    omega

theorem resolution_stage_length_bound {n : Nat} (formula : CNFFormula n) (v : Fin n) :
    (residual (normalize formula) v).length ≤ formula.length + formula.length ^ 2 := by
  have hr := residual_length_bound (normalize formula) v
  have hn := normalize_length_le formula
  have hs := Nat.mul_le_mul hn hn
  nlinarith

structure Choice {n : Nat} (formula : CNFFormula n) where
  var : Fin n
  active : var ∈ Alias.activeVars (normalize formula)
  size : (candidate formula var).length ≤ formula.length

def inspectVar {n : Nat} (formula : CNFFormula n)
    (v : { v : Fin n // v ∈ Shared.sourceVars (normalize formula) }) : Option (Choice formula) :=
  if small : (candidate formula v.val).length ≤ formula.length then
    some ⟨v.val, by simpa [Alias.activeVars] using v.property, small⟩
  else none

def scan {n : Nat} (formula : CNFFormula n) : Option (Choice formula) :=
  (Shared.sourceVars (normalize formula)).attach.findSome? (inspectVar formula)

theorem scan_none_iff {n : Nat} (formula : CNFFormula n) :
    scan formula = none ↔ ∀ v ∈ Shared.sourceVars (normalize formula),
      formula.length < (candidate formula v).length := by
  rw [scan, List.findSome?_eq_none_iff]
  constructor
  · intro h v hv
    have hh := h ⟨v, hv⟩ (by simp)
    simp only [inspectVar] at hh
    split at hh
    · contradiction
    · omega
  · intro h v _
    have hv := h v.val v.property
    simp [inspectVar, Nat.not_le_of_gt hv]

def contract {n : Nat} {formula : CNFFormula n} (choice : Choice formula) : CNFFormula n :=
  candidate formula choice.var

theorem contract_eval {n : Nat} {formula : CNFFormula n} (choice : Choice formula)
    (assignment : Nat → Bool) : CNFFormula.eval (contract choice) assignment =
      CNFFormula.eval formula (lift (normalize formula) choice.var assignment) :=
  candidate_eval formula choice.var assignment

theorem contract_sat {n : Nat} {formula : CNFFormula n} (choice : Choice formula) :
    CNFSatisfiable (contract choice) ↔ CNFSatisfiable formula := candidate_sat formula choice.var

theorem contract_length_le {n : Nat} {formula : CNFFormula n} (choice : Choice formula) :
    (contract choice).length ≤ formula.length := choice.size

theorem contract_active_lt {n : Nat} {formula : CNFFormula n} (choice : Choice formula) :
    (Alias.activeVars (contract choice)).card < (Alias.activeVars formula).card := by
  have hs := Finset.card_le_card (candidate_active_subset formula choice.var)
  have hn := Finset.card_le_card (normalize_active_subset formula)
  have hp := Finset.card_pos.mpr ⟨choice.var, choice.active⟩
  rw [Finset.card_erase_of_mem choice.active] at hs
  change (Alias.activeVars (contract choice)).card ≤ _ at hs
  omega

theorem literalCount_le_of_clauses {n : Nat} (formula : CNFFormula n)
    (h : ∀ clause ∈ formula, clause.length ≤ 2 * n) :
    SATJoint.literalCount formula ≤ 2 * n * formula.length := by
  induction formula with
  | nil => simp [SATJoint.literalCount]
  | cons clause rest ih =>
      have hc := h clause (by simp)
      have hr := ih (by intro c hc; exact h c (by simp [hc]))
      simp only [SATJoint.literalCount, List.map_cons, List.sum_cons, List.length_cons] at *
      nlinarith

theorem contract_literalCount_le {n : Nat} {formula : CNFFormula n} (choice : Choice formula) :
    SATJoint.literalCount (contract choice) ≤ 2 * n * formula.length :=
  (literalCount_le_of_clauses _ (candidate_clause_bound formula choice.var)).trans
    (Nat.mul_le_mul_left _ choice.size)

def reduceFuel {n : Nat} : Nat → CNFFormula n → CNFFormula n
  | 0, formula => formula
  | fuel + 1, formula =>
      match scan formula with
      | none => formula
      | some choice => reduceFuel fuel (contract choice)

def liftFuel {n : Nat} : Nat → CNFFormula n → (Nat → Bool) → (Nat → Bool)
  | 0, _, assignment => assignment
  | fuel + 1, formula, assignment =>
      match scan formula with
      | none => assignment
      | some choice => lift (normalize formula) choice.var
          (liftFuel fuel (contract choice) assignment)

theorem reduceFuel_eval {n : Nat} (fuel : Nat) (formula : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (reduceFuel fuel formula) assignment =
      CNFFormula.eval formula (liftFuel fuel formula assignment) := by
  induction fuel generalizing formula with
  | zero => rfl
  | succ fuel ih =>
      cases found : scan formula with
      | none => simp [reduceFuel, liftFuel, found]
      | some choice =>
          simp only [reduceFuel, liftFuel, found]
          rw [ih, contract_eval]

theorem reduceFuel_sat {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    CNFSatisfiable (reduceFuel fuel formula) ↔ CNFSatisfiable formula := by
  induction fuel generalizing formula with
  | zero => rfl
  | succ fuel ih =>
      cases found : scan formula with
      | none => simp [reduceFuel, found]
      | some choice =>
          simp only [reduceFuel, found]
          exact (ih _).trans (contract_sat choice)

theorem reduceFuel_length_le {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    (reduceFuel fuel formula).length ≤ formula.length := by
  induction fuel generalizing formula with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      cases found : scan formula with
      | none => simp [reduceFuel, found]
      | some choice =>
          rw [reduceFuel, found]
          exact (ih (contract choice)).trans choice.size

theorem reduceFuel_exhausted {n : Nat} (fuel : Nat) (formula : CNFFormula n)
    (enough : (Alias.activeVars formula).card ≤ fuel) : scan (reduceFuel fuel formula) = none := by
  induction fuel generalizing formula with
  | zero =>
      change scan formula = none
      cases found : scan formula with
      | none => rfl
      | some choice =>
          have smaller := contract_active_lt choice
          omega
  | succ fuel ih =>
      have equation : reduceFuel (fuel + 1) formula =
          match scan formula with
          | none => formula
          | some choice => reduceFuel fuel (contract choice) := rfl
      rw [equation]
      split
      · assumption
      · rename_i choice found
        apply ih
        have smaller := contract_active_lt choice
        omega

def reduce {n : Nat} (formula : CNFFormula n) : CNFFormula n :=
  let prepared := Subsumption.reduce formula
  reduceFuel (Alias.activeVars prepared).card prepared

theorem reduce_sat {n : Nat} (formula : CNFFormula n) :
    CNFSatisfiable (reduce formula) ↔ CNFSatisfiable formula := by
  rw [reduce, reduceFuel_sat]
  simp only [CNFSatisfiable, Subsumption.reduce_eval]

theorem reduce_exhausted {n : Nat} (formula : CNFFormula n) : scan (reduce formula) = none :=
  reduceFuel_exhausted _ _ (Nat.le_refl _)

theorem reduce_rejects_all {n : Nat} (formula : CNFFormula n) :
    ∀ v ∈ Shared.sourceVars (normalize (reduce formula)),
      (reduce formula).length < (candidate (reduce formula) v).length :=
  (scan_none_iff (reduce formula)).mp (reduce_exhausted formula)

theorem reduce_eval {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (reduce formula) assignment =
      CNFFormula.eval formula
        (liftFuel (Alias.activeVars (Subsumption.reduce formula)).card (Subsumption.reduce formula) assignment) := by
  rw [reduce, reduceFuel_eval, Subsumption.reduce_eval]

theorem reduce_length_le {n : Nat} (formula : CNFFormula n) :
    (reduce formula).length ≤ formula.length :=
  (reduceFuel_length_le _ _).trans (Subsumption.reduce_length_le formula)

theorem reduceFuel_clause_bound {n : Nat} (fuel : Nat) (formula : CNFFormula n)
    (h : ∀ clause ∈ formula, clause.length ≤ 2 * n) :
    ∀ clause ∈ reduceFuel fuel formula, clause.length ≤ 2 * n := by
  induction fuel generalizing formula with
  | zero => exact h
  | succ fuel ih =>
      intro clause hc
      rw [reduceFuel] at hc
      split at hc
      · exact h clause hc
      · rename_i choice found
        exact ih (contract choice) (candidate_clause_bound formula choice.var) clause hc

theorem reduce_clause_bound {n : Nat} (formula : CNFFormula n)
    (clause : CNFClause n) (h : clause ∈ reduce formula) : clause.length ≤ 2 * n :=
  reduceFuel_clause_bound _ _ (Subsumption.reduce_clause_bound formula) clause h

theorem reduce_literalCount_le {n : Nat} (formula : CNFFormula n) :
    SATJoint.literalCount (reduce formula) ≤ 2 * n * formula.length :=
  (literalCount_le_of_clauses _ (reduce_clause_bound formula)).trans
    (Nat.mul_le_mul_left _ (reduce_length_le formula))

def reduceStates {n : Nat} : Nat → CNFFormula n → List (CNFFormula n)
  | 0, formula => [formula]
  | fuel + 1, formula => formula ::
      match scan formula with
      | none => []
      | some choice => reduceStates fuel (contract choice)

theorem reduceStates_length_le {n : Nat} (fuel : Nat) (formula state : CNFFormula n)
    (h : state ∈ reduceStates fuel formula) : state.length ≤ formula.length := by
  induction fuel generalizing formula with
  | zero =>
      have he : state = formula := by simpa [reduceStates] using h
      subst state
      exact Nat.le_refl _
  | succ fuel ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_refl _
      · cases found : scan formula with
        | none => simp [found] at h
        | some choice =>
            have hs : state ∈ reduceStates fuel (contract choice) := by simpa [found] using h
            exact (ih _ hs).trans choice.size

theorem reduceStates_clause_bound {n : Nat} (fuel : Nat) (formula state : CNFFormula n)
    (hf : ∀ clause ∈ formula, clause.length ≤ 2 * n)
    (hs : state ∈ reduceStates fuel formula) : ∀ clause ∈ state, clause.length ≤ 2 * n := by
  induction fuel generalizing formula with
  | zero =>
      have he : state = formula := by simpa [reduceStates] using hs
      subst state
      exact hf
  | succ fuel ih =>
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hf
      · cases found : scan formula with
        | none => simp [found] at hs
        | some choice =>
            apply ih (contract choice) (candidate_clause_bound formula choice.var)
            simpa [found] using hs

theorem reduceStates_count_le {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    (reduceStates fuel formula).length ≤ fuel + 1 := by
  induction fuel generalizing formula with
  | zero => simp [reduceStates]
  | succ fuel ih =>
      cases found : scan formula <;> simp [reduceStates, found, ih]

def states {n : Nat} (formula : CNFFormula n) : List (CNFFormula n) :=
  let prepared := Subsumption.reduce formula
  reduceStates (Alias.activeVars prepared).card prepared

theorem states_source_bound {n : Nat} (formula state : CNFFormula n) (h : state ∈ states formula) :
    state.length ≤ formula.length ∧
      (∀ clause ∈ state, clause.length ≤ 2 * n) ∧
      SATJoint.literalCount state ≤ 2 * n * formula.length := by
  have hlen := (reduceStates_length_le _ _ _ h).trans (Subsumption.reduce_length_le formula)
  have hclause := reduceStates_clause_bound _ _ _ (Subsumption.reduce_clause_bound formula) h
  exact ⟨hlen, hclause, (literalCount_le_of_clauses state hclause).trans (Nat.mul_le_mul_left _ hlen)⟩

theorem states_count_bound {n : Nat} (formula : CNFFormula n) : (states formula).length ≤ n + 1 := by
  have h := reduceStates_count_le (Alias.activeVars (Subsumption.reduce formula)).card (Subsumption.reduce formula)
  have hc : (Alias.activeVars (Subsumption.reduce formula)).card ≤ n := by
    simpa using (Alias.activeVars (Subsumption.reduce formula)).card_le_univ
  exact h.trans (Nat.add_le_add_right hc 1)

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool := Factor.decideFormula (reduce formula)

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula :=
  (Factor.decideFormula_correct (reduce formula)).trans (reduce_sat formula)

theorem decideFormula_no {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = false ↔ ¬ CNFSatisfiable formula := by
  rw [Bool.eq_false_iff]
  exact not_congr (decideFormula_correct formula)

end SaturationMonoid.ComplexityProjection.SATSource.Eliminate
