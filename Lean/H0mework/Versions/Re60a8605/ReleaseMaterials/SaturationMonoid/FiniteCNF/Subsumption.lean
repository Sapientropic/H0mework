import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Eliminate.Normalize
import Mathlib.Data.List.Flatten

/-!
Source-local clause absorption and self-subsuming resolution.  Both clauses,
the pivot and the tested inclusion come from one original list.  Every update
preserves that list's Boolean evaluation at each assignment and strictly reduces
its literal count.  Saturation supplies a stronger normalization consumer.
-/

namespace SaturationMonoid.ComplexityProjection.SATSource.Subsumption

def covers {n : Nat} (small large : CNFClause n) : Bool :=
  small.all fun lit => decide (lit ∈ large)

theorem covers_true_iff {n : Nat} (small large : CNFClause n) :
    covers small large = true ↔ small ⊆ large := by
  simp only [covers, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h _ hx => h _ hx, fun h _ hx => h hx⟩

theorem covers_eval {n : Nat} (small large : CNFClause n)
    (h : covers small large = true) (assignment : Nat → Bool)
    (hs : CNFClause.eval small assignment = true) : CNFClause.eval large assignment = true := by
  obtain ⟨lit, hl, he⟩ := List.any_eq_true.mp hs
  exact List.any_eq_true.mpr ⟨lit, (covers_true_iff small large).mp h hl, he⟩

theorem clause_erase_eval {n : Nat} (clause : CNFClause n) (lit : CNFLiteral n)
    (h : lit ∈ clause) (assignment : Nat → Bool) :
    CNFClause.eval clause assignment =
      (lit.eval assignment || CNFClause.eval (clause.erase lit) assignment) := by
  simpa only [CNFClause.eval, List.any_cons] using (List.perm_cons_erase h).any_eq

theorem formula_erase_eval {n : Nat} (formula : CNFFormula n) (clause : CNFClause n)
    (h : clause ∈ formula) (assignment : Nat → Bool) :
    CNFFormula.eval formula assignment =
      (CNFClause.eval clause assignment && CNFFormula.eval (formula.erase clause) assignment) := by
  simpa only [CNFFormula.eval, List.all_cons] using (List.perm_cons_erase h).all_eq

theorem selfSubsuming_eval {n : Nat} (parent victim : CNFClause n) (pivot : CNFLiteral n)
    (hp : pivot ∈ parent) (hv : Alias.negate pivot ∈ victim)
    (included : covers (parent.erase pivot) (victim.erase (Alias.negate pivot)) = true)
    (assignment : Nat → Bool) (parent_true : CNFClause.eval parent assignment = true) :
    CNFClause.eval victim assignment = CNFClause.eval (victim.erase (Alias.negate pivot)) assignment := by
  rw [clause_erase_eval victim (Alias.negate pivot) hv, Alias.negate_eval]
  have hparent := (clause_erase_eval parent pivot hp assignment).symm.trans parent_true
  cases he : pivot.eval assignment with
  | true => simp
  | false =>
      have ha : CNFClause.eval (parent.erase pivot) assignment = true := by simpa [he] using hparent
      have hb := covers_eval _ _ included assignment ha
      simp [hb]

theorem literalCount_sublist {n : Nat} {left right : CNFFormula n} (h : left.Sublist right) :
    SATJoint.literalCount left ≤ SATJoint.literalCount right := by
  simpa only [SATJoint.literalCount, List.length_flatten] using h.flatten.length_le

theorem literalCount_map_dedup_le {n : Nat} (formula : CNFFormula n) :
    SATJoint.literalCount (formula.map List.dedup) ≤ SATJoint.literalCount formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      have hc := (List.dedup_sublist clause).length_le
      simp only [SATJoint.literalCount, List.map_cons, List.sum_cons] at *
      omega

theorem normalize_literalCount_le {n : Nat} (formula : CNFFormula n) :
    SATJoint.literalCount (Eliminate.normalize formula) ≤ SATJoint.literalCount formula := by
  have outer := literalCount_sublist (List.dedup_sublist ((SATJoint.dropTautologies formula).map List.dedup))
  have middle := literalCount_map_dedup_le (SATJoint.dropTautologies formula)
  have inner : SATJoint.literalCount (SATJoint.dropTautologies formula) ≤ SATJoint.literalCount formula :=
    literalCount_sublist List.filter_sublist
  exact outer.trans (middle.trans inner)

theorem erase_literalCount {n : Nat} (formula : CNFFormula n) (clause : CNFClause n)
    (h : clause ∈ formula) :
    SATJoint.literalCount formula = clause.length + SATJoint.literalCount (formula.erase clause) := by
  simpa only [SATJoint.literalCount, List.map_cons, List.sum_cons] using
    ((List.perm_cons_erase h).map List.length).sum_eq

inductive Change {n : Nat} (formula : CNFFormula n)
  | absorb (parent victim : CNFClause n)
      (parent_mem : parent ∈ formula) (victim_mem : victim ∈ formula)
      (different : parent ≠ victim) (positive : 0 < victim.length)
      (included : covers parent victim = true)
  | shorten (parent victim : CNFClause n) (pivot : CNFLiteral n)
      (parent_mem : parent ∈ formula) (victim_mem : victim ∈ formula)
      (different : parent ≠ victim) (pivot_mem : pivot ∈ parent)
      (opposite_mem : Alias.negate pivot ∈ victim)
      (included : covers (parent.erase pivot) (victim.erase (Alias.negate pivot)) = true)

def inspectPair {n : Nat} (formula : CNFFormula n)
    (parent victim : { c : CNFClause n // c ∈ formula }) : Option (Change formula) :=
  if different : parent.val ≠ victim.val then
    if included : covers parent.val victim.val = true then
      if positive : 0 < victim.val.length then
        some (.absorb parent.val victim.val parent.property victim.property different positive included)
      else none
    else
      parent.val.attach.findSome? fun pivot =>
        if opposite : Alias.negate pivot.val ∈ victim.val then
          if subset : covers (parent.val.erase pivot.val) (victim.val.erase (Alias.negate pivot.val)) = true then
            some (.shorten parent.val victim.val pivot.val parent.property victim.property
              different pivot.property opposite subset)
          else none
        else none
  else none

def scan {n : Nat} (formula : CNFFormula n) : Option (Change formula) :=
  formula.attach.findSome? fun parent => formula.attach.findSome? (inspectPair formula parent)

def rawUpdate {n : Nat} {formula : CNFFormula n} : Change formula → CNFFormula n
  | .absorb _ victim _ _ _ _ _ => formula.erase victim
  | .shorten _ victim pivot _ _ _ _ _ _ =>
      victim.erase (Alias.negate pivot) :: formula.erase victim

def update {n : Nat} {formula : CNFFormula n} (change : Change formula) : CNFFormula n :=
  Eliminate.normalize (rawUpdate change)

theorem rawUpdate_eval {n : Nat} {formula : CNFFormula n} (change : Change formula)
    (assignment : Nat → Bool) :
    CNFFormula.eval (rawUpdate change) assignment = CNFFormula.eval formula assignment := by
  cases change with
  | absorb parent victim hp hv hd positive included =>
      have retained := (List.mem_erase_of_ne hd).mpr hp
      rw [formula_erase_eval formula victim hv]
      cases hr : CNFFormula.eval (formula.erase victim) assignment with
      | false => simp [rawUpdate, hr]
      | true =>
          have ht := List.all_eq_true.mp hr parent retained
          have hc := covers_eval parent victim included assignment ht
          simp [rawUpdate, hr, hc]
  | shorten parent victim pivot hp hv hd hpm hvm included =>
      have retained := (List.mem_erase_of_ne hd).mpr hp
      rw [formula_erase_eval formula victim hv]
      cases hr : CNFFormula.eval (formula.erase victim) assignment with
      | false =>
          change (CNFClause.eval (victim.erase (Alias.negate pivot)) assignment &&
            CNFFormula.eval (formula.erase victim) assignment) = _
          rw [hr]
          simp
      | true =>
          have ht := List.all_eq_true.mp hr parent retained
          have he := selfSubsuming_eval parent victim pivot hpm hvm included assignment ht
          simp only [rawUpdate, CNFFormula.eval, List.all_cons]
          change (CNFClause.eval (victim.erase (Alias.negate pivot)) assignment &&
            CNFFormula.eval (formula.erase victim) assignment) = _
          rw [hr, he]

theorem update_eval {n : Nat} {formula : CNFFormula n} (change : Change formula)
    (assignment : Nat → Bool) :
    CNFFormula.eval (update change) assignment = CNFFormula.eval formula assignment := by
  rw [update, Eliminate.normalize_eval, rawUpdate_eval]

theorem rawUpdate_length_le {n : Nat} {formula : CNFFormula n} (change : Change formula) :
    (rawUpdate change).length ≤ formula.length := by
  cases change with
  | absorb parent victim hp hv hd positive included =>
      exact List.erase_sublist.length_le
  | shorten parent victim pivot hp hv hd hpm hvm included =>
      exact Nat.le_of_eq (List.length_erase_add_one hv)

theorem update_length_le {n : Nat} {formula : CNFFormula n} (change : Change formula) :
    (update change).length ≤ formula.length :=
  (Eliminate.normalize_length_le _).trans (rawUpdate_length_le change)

theorem rawUpdate_literalCount_lt {n : Nat} {formula : CNFFormula n} (change : Change formula) :
    SATJoint.literalCount (rawUpdate change) < SATJoint.literalCount formula := by
  cases change with
  | absorb parent victim hp hv hd positive included =>
      have h := erase_literalCount formula victim hv
      change SATJoint.literalCount (formula.erase victim) < _
      omega
  | shorten parent victim pivot hp hv hd hpm hvm included =>
      have h := erase_literalCount formula victim hv
      have he := List.length_erase_add_one hvm
      change (victim.erase (Alias.negate pivot)).length + SATJoint.literalCount (formula.erase victim) < _
      omega

theorem update_literalCount_lt {n : Nat} {formula : CNFFormula n} (change : Change formula) :
    SATJoint.literalCount (update change) < SATJoint.literalCount formula :=
  (normalize_literalCount_le _).trans_lt (rawUpdate_literalCount_lt change)

theorem rawUpdate_active_subset {n : Nat} {formula : CNFFormula n} (change : Change formula) :
    Alias.activeVars (rawUpdate change) ⊆ Alias.activeVars formula := by
  cases change with
  | absorb parent victim hp hv hd positive included =>
      intro v h
      obtain ⟨clause, hc, lit, hl, he⟩ := (Alias.mem_activeVars _ _).mp h
      exact (Alias.mem_activeVars _ _).mpr
        ⟨clause, List.mem_of_mem_erase hc, lit, hl, he⟩
  | shorten parent victim pivot hp hv hd hpm hvm included =>
      intro v h
      obtain ⟨clause, hc, lit, hl, he⟩ := (Alias.mem_activeVars _ _).mp h
      rcases List.mem_cons.mp hc with rfl | hc
      · exact (Alias.mem_activeVars _ _).mpr ⟨victim, hv, lit, List.mem_of_mem_erase hl, he⟩
      · exact (Alias.mem_activeVars _ _).mpr ⟨clause, List.mem_of_mem_erase hc, lit, hl, he⟩

theorem update_active_subset {n : Nat} {formula : CNFFormula n} (change : Change formula) :
    Alias.activeVars (update change) ⊆ Alias.activeVars formula :=
  (Eliminate.normalize_active_subset _).trans (rawUpdate_active_subset change)

def reduceFuel {n : Nat} : Nat → CNFFormula n → CNFFormula n
  | 0, formula => formula
  | fuel + 1, formula =>
      match scan formula with
      | none => formula
      | some change => reduceFuel fuel (update change)

theorem reduceFuel_eval {n : Nat} (fuel : Nat) (formula : CNFFormula n)
    (assignment : Nat → Bool) :
    CNFFormula.eval (reduceFuel fuel formula) assignment = CNFFormula.eval formula assignment := by
  induction fuel generalizing formula with
  | zero => rfl
  | succ fuel ih =>
      cases found : scan formula with
      | none => simp [reduceFuel, found]
      | some change =>
          rw [reduceFuel, found, ih, update_eval]

theorem reduceFuel_length_le {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    (reduceFuel fuel formula).length ≤ formula.length := by
  induction fuel generalizing formula with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      cases found : scan formula with
      | none => simp [reduceFuel, found]
      | some change =>
          rw [reduceFuel, found]
          exact (ih _).trans (update_length_le change)

theorem reduceFuel_literalCount_le {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    SATJoint.literalCount (reduceFuel fuel formula) ≤ SATJoint.literalCount formula := by
  induction fuel generalizing formula with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      cases found : scan formula with
      | none => simp [reduceFuel, found]
      | some change =>
          rw [reduceFuel, found]
          exact (ih _).trans (Nat.le_of_lt (update_literalCount_lt change))

theorem reduceFuel_active_subset {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    Alias.activeVars (reduceFuel fuel formula) ⊆ Alias.activeVars formula := by
  induction fuel generalizing formula with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
      cases found : scan formula with
      | none => simp [reduceFuel, found]
      | some change =>
          rw [reduceFuel, found]
          exact (ih _).trans (update_active_subset change)

theorem reduceFuel_clause_bound {n : Nat} (fuel : Nat) (formula : CNFFormula n)
    (bounded : ∀ clause ∈ formula, clause.length ≤ 2 * n) :
    ∀ clause ∈ reduceFuel fuel formula, clause.length ≤ 2 * n := by
  induction fuel generalizing formula with
  | zero => exact bounded
  | succ fuel ih =>
      intro clause hc
      rw [reduceFuel] at hc
      split at hc
      · exact bounded clause hc
      · rename_i change found
        exact ih (update change) (Eliminate.normalize_clause_bound _) clause hc

theorem reduceFuel_exhausted {n : Nat} (fuel : Nat) (formula : CNFFormula n)
    (enough : SATJoint.literalCount formula ≤ fuel) : scan (reduceFuel fuel formula) = none := by
  induction fuel generalizing formula with
  | zero =>
      change scan formula = none
      cases found : scan formula with
      | none => rfl
      | some change =>
          have h := update_literalCount_lt change
          omega
  | succ fuel ih =>
      have equation : reduceFuel (fuel + 1) formula =
          match scan formula with
          | none => formula
          | some change => reduceFuel fuel (update change) := rfl
      rw [equation]
      split
      · assumption
      · rename_i change found
        apply ih
        have h := update_literalCount_lt change
        omega

def reduce {n : Nat} (formula : CNFFormula n) : CNFFormula n :=
  let prepared := Eliminate.normalize formula
  reduceFuel (SATJoint.literalCount prepared) prepared

theorem reduce_eval {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (reduce formula) assignment = CNFFormula.eval formula assignment := by
  rw [reduce, reduceFuel_eval, Eliminate.normalize_eval]

theorem reduce_exhausted {n : Nat} (formula : CNFFormula n) : scan (reduce formula) = none :=
  reduceFuel_exhausted _ _ (Nat.le_refl _)

theorem reduce_length_le {n : Nat} (formula : CNFFormula n) :
    (reduce formula).length ≤ formula.length :=
  (reduceFuel_length_le _ _).trans (Eliminate.normalize_length_le formula)

theorem reduce_literalCount_le {n : Nat} (formula : CNFFormula n) :
    SATJoint.literalCount (reduce formula) ≤ SATJoint.literalCount formula :=
  (reduceFuel_literalCount_le _ _).trans (normalize_literalCount_le formula)

theorem reduce_active_subset {n : Nat} (formula : CNFFormula n) :
    Alias.activeVars (reduce formula) ⊆ Alias.activeVars formula :=
  (reduceFuel_active_subset _ _).trans (Eliminate.normalize_active_subset formula)

theorem reduce_clause_bound {n : Nat} (formula : CNFFormula n)
    (clause : CNFClause n) (h : clause ∈ reduce formula) : clause.length ≤ 2 * n :=
  reduceFuel_clause_bound _ _ (Eliminate.normalize_clause_bound formula) clause h

end SaturationMonoid.ComplexityProjection.SATSource.Subsumption
