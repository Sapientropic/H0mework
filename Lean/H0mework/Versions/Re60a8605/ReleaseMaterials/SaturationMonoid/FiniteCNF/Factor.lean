import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Pruned

/-!
The original clause supports generate independent conjunction factors. A source
flood moves every clause touching the current component and stops when no
crossing variable remains. Each generated component is decided before the next
one, so independent source choices never enter a common residual frontier.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Factor

open Shared

def Separated {n : Nat} (left right : CNFFormula n) : Prop :=
  ∀ clause ∈ right, ∀ lit ∈ clause, lit.var ∉ sourceVars left

theorem clause_eval_agree {n : Nat} (clause : CNFClause n)
    (left right : Nat → Bool)
    (agree : ∀ lit ∈ clause, left lit.var.val = right lit.var.val) :
    CNFClause.eval clause left = CNFClause.eval clause right := by
  induction clause with
  | nil => rfl
  | cons lit rest ih =>
      have hl := agree lit List.mem_cons_self
      have hr := ih (by intro l h; exact agree l (List.mem_cons_of_mem _ h))
      simp only [CNFClause.eval, List.any_cons] at hr ⊢
      rw [hr]
      simp [CNFLiteral.eval, hl]

theorem formula_eval_agree {n : Nat} (formula : CNFFormula n)
    (left right : Nat → Bool)
    (agree : ∀ clause ∈ formula, ∀ lit ∈ clause,
      left lit.var.val = right lit.var.val) :
    CNFFormula.eval formula left = CNFFormula.eval formula right := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      have hc := clause_eval_agree clause left right (agree clause List.mem_cons_self)
      have hr := ih (by intro c h; exact agree c (List.mem_cons_of_mem _ h))
      simp only [CNFFormula.eval, List.all_cons] at hr ⊢
      rw [hc, hr]

def mergeAssignment {n : Nat} (left : CNFFormula n)
    (a b : Nat → Bool) : Nat → Bool :=
  fun i => if i ∈ (sourceVars left).map Fin.val then a i else b i

theorem separated_sat {n : Nat} (left right : CNFFormula n)
    (separated : Separated left right) :
    CNFSatisfiable (left ++ right) ↔ CNFSatisfiable left ∧ CNFSatisfiable right := by
  constructor
  · rintro ⟨assignment, hs⟩
    simp only [CNFFormula.eval, List.all_append, Bool.and_eq_true] at hs
    exact ⟨⟨assignment, hs.1⟩, ⟨assignment, hs.2⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨mergeAssignment left a b, ?_⟩
    have hl : CNFFormula.eval left (mergeAssignment left a b) = CNFFormula.eval left a := by
      apply formula_eval_agree
      intro clause hc lit hlit
      have hm : lit.var.val ∈ (sourceVars left).map Fin.val :=
        List.mem_map.mpr ⟨lit.var, sourceVars_supported left clause hc lit hlit, rfl⟩
      simp [mergeAssignment, hm]
    have hr : CNFFormula.eval right (mergeAssignment left a b) = CNFFormula.eval right b := by
      apply formula_eval_agree
      intro clause hc lit hlit
      have hm : lit.var.val ∉ (sourceVars left).map Fin.val := by
        intro hm
        obtain ⟨v, hv, he⟩ := List.mem_map.mp hm
        exact separated clause hc lit hlit (Fin.ext he ▸ hv)
      simp [mergeAssignment, hm]
    simpa only [CNFFormula.eval, List.all_append, Bool.and_eq_true] using
      And.intro (hl.trans ha) (hr.trans hb)

def touches {n : Nat} (component : CNFFormula n) (clause : CNFClause n) : Bool :=
  clause.any fun lit => decide (lit.var ∈ sourceVars component)

def grow {n : Nat} : Nat → CNFFormula n → CNFFormula n → CNFFormula n × CNFFormula n
  | 0, component, rest => (component, rest)
  | fuel + 1, component, rest =>
      let moved := rest.filter (touches component)
      if moved = [] then (component, rest)
      else grow fuel (component ++ moved) (rest.filter fun clause => !touches component clause)

theorem grow_members {n : Nat} (fuel : Nat) (component rest : CNFFormula n)
    (clause : CNFClause n) :
    clause ∈ (grow fuel component rest).1 ++ (grow fuel component rest).2 ↔
      clause ∈ component ++ rest := by
  induction fuel generalizing component rest with
  | zero => rfl
  | succ fuel ih =>
      simp only [grow]
      split
      · rfl
      · rw [ih]
        simp only [List.mem_append, List.mem_filter]
        cases touches component clause <;> simp

theorem no_touching_separated {n : Nat} (component rest : CNFFormula n)
    (empty : rest.filter (touches component) = []) : Separated component rest := by
  intro clause hc lit hl
  have ht : touches component clause = false :=
    Bool.eq_false_iff.mpr ((List.filter_eq_nil_iff.mp empty) clause hc)
  exact of_decide_eq_false (Bool.eq_false_iff.mpr ((List.any_eq_false.mp ht) lit hl))

theorem grow_separated {n : Nat} (fuel : Nat) (component rest : CNFFormula n)
    (enough : rest.length ≤ fuel) :
    Separated (grow fuel component rest).1 (grow fuel component rest).2 := by
  induction fuel generalizing component rest with
  | zero =>
      have hr : rest = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
      simp [grow, hr, Separated]
  | succ fuel ih =>
      simp only [grow]
      split
      · exact no_touching_separated component rest (by assumption)
      · rename_i hnonempty
        apply ih
        have positive : 0 < (rest.filter (touches component)).length :=
          List.length_pos_iff.mpr hnonempty
        have accounting := List.length_eq_length_filter_add (l := rest) (touches component)
        omega

theorem grow_rest_length_le {n : Nat} (fuel : Nat) (component rest : CNFFormula n) :
    (grow fuel component rest).2.length ≤ rest.length := by
  induction fuel generalizing component rest with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      simp only [grow]
      split
      · exact Nat.le_refl _
      · exact (ih _ _).trans (List.length_filter_le _ _)

theorem generated_remainder_lt {n : Nat} (clause : CNFClause n) (rest : CNFFormula n) :
    (grow rest.length [clause] rest).2.length < (clause :: rest).length :=
  Nat.lt_succ_of_le (grow_rest_length_le _ _ _)

theorem formula_eval_of_members {n : Nat} (left right : CNFFormula n)
    (same : ∀ clause, clause ∈ left ↔ clause ∈ right) (assignment : Nat → Bool) :
    CNFFormula.eval left assignment = CNFFormula.eval right assignment := by
  apply Bool.eq_iff_iff.mpr
  simp only [CNFFormula.eval, List.all_eq_true]
  exact ⟨fun h c hc => h c ((same c).mpr hc), fun h c hc => h c ((same c).mp hc)⟩

theorem grow_sat {n : Nat} (fuel : Nat) (component rest : CNFFormula n)
    (enough : rest.length ≤ fuel) :
    CNFSatisfiable (component ++ rest) ↔
      CNFSatisfiable (grow fuel component rest).1 ∧
        CNFSatisfiable (grow fuel component rest).2 := by
  have same : CNFSatisfiable (component ++ rest) ↔
      CNFSatisfiable ((grow fuel component rest).1 ++ (grow fuel component rest).2) := by
    apply exists_congr
    intro assignment
    rw [formula_eval_of_members _ _ (grow_members fuel component rest) assignment]
  exact same.trans (separated_sat _ _ (grow_separated fuel component rest enough))

def decideRun {n : Nat} : Nat → CNFFormula n → Bool
  | 0, formula => decideSource formula
  | _ + 1, [] => true
  | fuel + 1, clause :: rest =>
      let factors := grow rest.length [clause] rest
      decideSource factors.1 && decideRun fuel factors.2

theorem decideRun_correct {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    decideRun fuel formula = true ↔ CNFSatisfiable formula := by
  induction fuel generalizing formula with
  | zero => exact decideSource_correct formula
  | succ fuel ih =>
      cases formula with
      | nil => simp [decideRun, CNFSatisfiable, CNFFormula.eval]
      | cons clause rest =>
          simp only [decideRun, Bool.and_eq_true, decideSource_correct, ih]
          exact (grow_sat rest.length [clause] rest (Nat.le_refl _)).symm

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  decideRun formula.length formula

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := decideRun_correct _ _

theorem decideFormula_no {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = false ↔ ¬ CNFSatisfiable formula := by
  rw [Bool.eq_false_iff]
  exact not_congr (decideFormula_correct formula)

end SaturationMonoid.ComplexityProjection.SATSource.Factor
