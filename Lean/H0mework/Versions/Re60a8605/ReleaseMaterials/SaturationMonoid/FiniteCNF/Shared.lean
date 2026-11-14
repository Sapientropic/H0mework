import H0mework.Computation.SelfReduction.P694
import Mathlib.Data.List.Dedup

/-! Executable variable elimination through the original CNF residual operation.
Equal residual formulas are merged before the next source operation. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Shared

def cofactor {n : Nat} (formula : CNFFormula n) (v : Fin n) (bit : Bool) :
    CNFFormula n := unitPropagationResidual formula v bit

theorem cofactor_eval {n : Nat} (formula : CNFFormula n) (v : Fin n)
    (bit : Bool) (assignment : Nat → Bool) :
    CNFFormula.eval (cofactor formula v bit) assignment =
      CNFFormula.eval formula (forceAssignment v bit assignment) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases hc : clauseContainsLiteral clause v bit with
      | false =>
          have he := clause_eval_force_eq_remove_opposite_of_not_contains
            clause v bit assignment hc
          simpa [cofactor, unitPropagationResidual, hc, CNFFormula.eval, he]
            using congrArg (fun b =>
              CNFClause.eval (clauseRemoveOpposite clause v bit) assignment && b) ih
      | true =>
          have he := clause_eval_true_of_contains_literal clause v bit assignment hc
          simpa [cofactor, unitPropagationResidual, hc, CNFFormula.eval, he] using ih

theorem cofactor_sat {n : Nat} (formula : CNFFormula n) (v : Fin n) :
    CNFSatisfiable formula ↔
      CNFSatisfiable (cofactor formula v false) ∨
        CNFSatisfiable (cofactor formula v true) := by
  constructor
  · rintro ⟨assignment, hsat⟩
    have hf : forceAssignment v (assignment v.val) assignment = assignment := by
      funext i
      simp only [forceAssignment]
      split <;> simp_all
    have hr : CNFSatisfiable (cofactor formula v (assignment v.val)) :=
      ⟨assignment, by rw [cofactor_eval, hf]; exact hsat⟩
    cases hb : assignment v.val
    · exact Or.inl (hb ▸ hr)
    · exact Or.inr (hb ▸ hr)
  · rintro (⟨assignment, hsat⟩ | ⟨assignment, hsat⟩)
    · exact ⟨forceAssignment v false assignment, (cofactor_eval ..) ▸ hsat⟩
    · exact ⟨forceAssignment v true assignment, (cofactor_eval ..) ▸ hsat⟩

def SupportedBy {n : Nat} (formula : CNFFormula n) (vars : List (Fin n)) : Prop :=
  ∀ clause ∈ formula, ∀ lit ∈ clause, lit.var ∈ vars

theorem cofactor_supported {n : Nat} (formula : CNFFormula n) (v : Fin n)
    (bit : Bool) (vars : List (Fin n))
    (hs : SupportedBy formula (v :: vars)) :
    SupportedBy (cofactor formula v bit) vars := by
  intro clause hc lit hl
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hof, hon⟩ := List.mem_filter.mp ho
  obtain ⟨hlo, hln⟩ := List.mem_filter.mp hl
  have hsame : literalMatches v bit lit = false := by
    have hnot : clauseContainsLiteral original v bit = false := by simpa using hon
    exact Bool.eq_false_iff.mpr ((List.any_eq_false.mp hnot) lit hlo)
  have hopp : literalMatches v (!bit) lit = false := by simpa using hln
  have hne := literal_var_ne_of_no_polarity_match v bit lit hsame hopp
  exact (List.mem_cons.mp (hs original hof lit hlo)).resolve_left hne

def live {n : Nat} (frontier : List (CNFFormula n)) : Prop :=
  ∃ formula ∈ frontier, CNFSatisfiable formula

def advance {n : Nat} (frontier : List (CNFFormula n)) (v : Fin n) :
    List (CNFFormula n) :=
  (frontier.flatMap fun formula =>
    [cofactor formula v false, cofactor formula v true]).dedup

theorem advance_live {n : Nat} (frontier : List (CNFFormula n)) (v : Fin n) :
    live (advance frontier v) ↔ live frontier := by
  simp only [live, advance, List.mem_dedup, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨residual, ⟨formula, hf, he | he⟩, hs⟩
    · subst residual
      exact ⟨formula, hf, (cofactor_sat formula v).mpr (Or.inl hs)⟩
    · subst residual
      exact ⟨formula, hf, (cofactor_sat formula v).mpr (Or.inr hs)⟩
  · rintro ⟨formula, hf, hs⟩
    rcases (cofactor_sat formula v).mp hs with hs | hs
    · exact ⟨_, ⟨formula, hf, Or.inl rfl⟩, hs⟩
    · exact ⟨_, ⟨formula, hf, Or.inr rfl⟩, hs⟩

theorem advance_supported {n : Nat} (frontier : List (CNFFormula n)) (v : Fin n)
    (vars : List (Fin n))
    (hs : ∀ formula ∈ frontier, SupportedBy formula (v :: vars)) :
    ∀ formula ∈ advance frontier v, SupportedBy formula vars := by
  intro formula hf
  simp only [advance, List.mem_dedup, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  obtain ⟨original, ho, hf | hf⟩ := hf
  · subst formula
    exact cofactor_supported original v false vars (hs original ho)
  · subst formula
    exact cofactor_supported original v true vars (hs original ho)

def run {n : Nat} : List (Fin n) → List (CNFFormula n) → List (CNFFormula n)
  | [], frontier => frontier
  | v :: vars, frontier => run vars (advance frontier v)

theorem run_live {n : Nat} (vars : List (Fin n))
    (frontier : List (CNFFormula n)) : live (run vars frontier) ↔ live frontier := by
  induction vars generalizing frontier with
  | nil => rfl
  | cons v vars ih => exact (ih _).trans (advance_live frontier v)

theorem run_supported {n : Nat} (vars : List (Fin n))
    (frontier : List (CNFFormula n))
    (hs : ∀ formula ∈ frontier, SupportedBy formula vars) :
    ∀ formula ∈ run vars frontier, SupportedBy formula [] := by
  induction vars generalizing frontier with
  | nil => exact hs
  | cons v vars ih =>
      exact ih (advance frontier v) (advance_supported frontier v vars hs)

theorem eval_eq_of_supported_nil {n : Nat} (formula : CNFFormula n)
    (hs : SupportedBy formula []) (left right : Nat → Bool) :
    CNFFormula.eval formula left = CNFFormula.eval formula right := by
  cases formula with
  | nil => rfl
  | cons clause rest =>
      have hc : clause = [] := List.eq_nil_iff_forall_not_mem.mpr (by
        intro lit hl
        exact List.not_mem_nil (hs clause List.mem_cons_self lit hl))
      simp [CNFFormula.eval, CNFClause.eval, hc]

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  (run (List.finRange n) [formula]).any
    (fun residual => CNFFormula.eval residual (fun _ => false))

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  have hsupport : ∀ f ∈ run (List.finRange n) [formula], SupportedBy f [] := by
    apply run_supported
    intro f _ clause _ lit _
    exact List.mem_finRange lit.var
  have hread : decideFormula formula = true ↔
      live (run (List.finRange n) [formula]) := by
    change (List.any _ _) = true ↔ _
    rw [List.any_eq_true]
    constructor
    · rintro ⟨f, hf, hs⟩
      exact ⟨f, hf, ⟨fun _ => false, hs⟩⟩
    · rintro ⟨f, hf, assignment, hs⟩
      exact ⟨f, hf, (eval_eq_of_supported_nil f (hsupport f hf)
        assignment (fun _ => false)) ▸ hs⟩
  rw [hread, run_live]
  simp only [live, List.mem_singleton, exists_eq_left]

theorem decideFormula_no {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = false ↔ ¬ CNFSatisfiable formula := by
  rw [Bool.eq_false_iff]
  exact not_congr (decideFormula_correct formula)

end SaturationMonoid.ComplexityProjection.SATSource.Shared
