import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Eliminate

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine

open InterferenceProgram

theorem eval_false (vars : List Nat) : Parity.eval (fun _ => false) vars = false := by
  induction vars with
  | nil => rfl
  | cons i rest ih => simp [Parity.eval, ih]

theorem eval_delta_absent (vars : List Nat) (p : Nat) (absent : p ∉ vars) :
    Parity.eval (fun i => decide (i = p)) vars = false := by
  rw [← eval_false vars]
  apply Parity.eval_congr
  intro i member
  have different : i ≠ p := by rintro rfl; exact absent member
  simp [different]

theorem eval_delta (vars : List Nat) (p : Nat) (nodup : vars.Nodup) :
    Parity.eval (fun i => decide (i = p)) vars = decide (p ∈ vars) := by
  induction vars with
  | nil => rfl
  | cons i rest ih =>
      have separate := List.nodup_cons.mp nodup
      by_cases same : i = p
      · subst i
        simp only [Parity.eval, decide_true, eval_delta_absent rest p separate.1,
          Bool.xor_false, List.mem_cons, true_or, decide_true]
      · have tail := ih separate.2
        simp [Parity.eval, same, Ne.symm same, tail]

theorem Row.xor_mem (left right : Row) (leftNodup : left.vars.Nodup) (rightNodup : right.vars.Nodup)
    (p : Nat) : decide (p ∈ (left.xor right).vars) = (decide (p ∈ left.vars) ^^ decide (p ∈ right.vars)) := by
  rw [← eval_delta _ p (Row.xor_nodup left right rightNodup), Row.xor]
  rw [Parity.eval_merge, eval_delta _ p leftNodup, eval_delta _ p rightNodup]

theorem Row.xor_absent (left right : Row) (leftNodup : left.vars.Nodup) (rightNodup : right.vars.Nodup)
    (p : Nat) (leftAbsent : p ∉ left.vars) (rightAbsent : p ∉ right.vars) : p ∉ (left.xor right).vars := by
  have member := Row.xor_mem left right leftNodup rightNodup p
  simpa [leftAbsent, rightAbsent] using member

theorem Row.xor_cancels (left right : Row) (leftNodup : left.vars.Nodup) (rightNodup : right.vars.Nodup)
    (p : Nat) (leftPresent : p ∈ left.vars) (rightPresent : p ∈ right.vars) : p ∉ (left.xor right).vars := by
  have member := Row.xor_mem left right leftNodup rightNodup p
  simpa [leftPresent, rightPresent] using member

def RowsNodup (basis : List Row) : Prop := ∀ row ∈ basis, row.vars.Nodup

theorem reduceWith_nodup (basis : List Row) (basisNodup : RowsNodup basis) (row : Row)
    (nodup : row.vars.Nodup) : (reduceWith basis row).vars.Nodup := by
  induction basis generalizing row with
  | nil => exact nodup
  | cons pivot rest ih =>
      have pivotNodup := basisNodup pivot (by simp)
      have tailNodup : RowsNodup rest := fun value member => basisNodup value (by simp [member])
      simp only [reduceWith, List.foldl_cons]
      apply ih tailNodup
      cases shape : pivot.vars with
      | nil => exact nodup
      | cons p vars =>
          simp only
          split
          · exact Row.xor_nodup row pivot pivotNodup
          · exact nodup

theorem reduceWith_absent (basis : List Row) (basisNodup : RowsNodup basis) (row : Row)
    (nodup : row.vars.Nodup) (p : Nat) (absent : p ∉ row.vars)
    (basisAbsent : ∀ other ∈ basis, p ∉ other.vars) : p ∉ (reduceWith basis row).vars := by
  induction basis generalizing row with
  | nil => exact absent
  | cons pivot rest ih =>
      have pivotNodup := basisNodup pivot (by simp)
      have tailNodup : RowsNodup rest := fun value member => basisNodup value (by simp [member])
      have pivotAbsent := basisAbsent pivot (by simp)
      have tailAbsent : ∀ other ∈ rest, p ∉ other.vars := fun value member => basisAbsent value (by simp [member])
      simp only [reduceWith, List.foldl_cons]
      apply ih tailNodup
      · cases shape : pivot.vars with
        | nil => exact nodup
        | cons q vars =>
            simp only
            split
            · exact Row.xor_nodup row pivot pivotNodup
            · exact nodup
      · cases shape : pivot.vars with
        | nil => exact absent
        | cons q vars =>
            simp only
            split
            · exact Row.xor_absent row pivot nodup pivotNodup p absent pivotAbsent
            · exact absent
      · exact tailAbsent

def Above (earlier later : Row) : Prop :=
  ∀ p, earlier.vars.head? = some p → p ∉ later.vars

def Triangular (basis : List Row) : Prop :=
  RowsNodup basis ∧ (∀ row ∈ basis, row.vars ≠ []) ∧ basis.Pairwise Above

theorem triangular_nil : Triangular [] := by simp [Triangular, RowsNodup]

theorem triangular_tail (row : Row) (rest : List Row) (triangular : Triangular (row :: rest)) :
    Triangular rest := by
  refine ⟨fun value member => triangular.1 value (by simp [member]),
    fun value member => triangular.2.1 value (by simp [member]), ?_⟩
  exact (List.pairwise_cons.mp triangular.2.2).2

theorem reduceWith_erases (basis : List Row) (triangular : Triangular basis) (row : Row)
    (nodup : row.vars.Nodup) :
    ∀ old ∈ basis, ∀ p, old.vars.head? = some p → p ∉ (reduceWith basis row).vars := by
  induction basis generalizing row with
  | nil => simp
  | cons pivot rest ih =>
      have pivotNodup := triangular.1 pivot (by simp)
      have nonempty := triangular.2.1 pivot (by simp)
      have tail := triangular_tail pivot rest triangular
      have later := (List.pairwise_cons.mp triangular.2.2).1
      cases shape : pivot.vars with
      | nil => exact False.elim (nonempty shape)
      | cons q vars =>
          let next := if q ∈ row.vars then row.xor pivot else row
          have nextNodup : next.vars.Nodup := by
            dsimp only [next]
            split
            · exact Row.xor_nodup row pivot pivotNodup
            · exact nodup
          have absent : q ∉ next.vars := by
            dsimp only [next]
            split
            · rename_i present
              exact Row.xor_cancels row pivot nodup pivotNodup q present (by simp [shape])
            · assumption
          have remaining : ∀ other ∈ rest, q ∉ other.vars :=
            fun other member => later other member q (by simp [shape])
          have restErases := ih tail next nextNodup
          intro old member p head
          simp only [reduceWith, List.foldl_cons, shape]
          change p ∉ (reduceWith rest next).vars
          rcases List.mem_cons.mp member with rfl | member
          · have same : q = p := by simpa only [shape, List.head?_cons, Option.some.injEq] using head
            subst p
            exact reduceWith_absent rest tail.1 next nextNodup q absent remaining
          · exact restErases old member p head

theorem triangular_append (basis : List Row) (triangular : Triangular basis) (row : Row)
    (nodup : row.vars.Nodup) (nonempty : row.vars ≠ [])
    (follows : ∀ old ∈ basis, Above old row) : Triangular (basis ++ [row]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro value member
    rcases List.mem_append.mp member with prior | last
    · exact triangular.1 value prior
    · simpa only [List.mem_singleton.mp last] using nodup
  · intro value member
    rcases List.mem_append.mp member with prior | last
    · exact triangular.2.1 value prior
    · simpa only [List.mem_singleton.mp last] using nonempty
  · apply List.pairwise_append.mpr
    refine ⟨triangular.2.2, by simp, ?_⟩
    intro old oldMember value member
    have same := List.mem_singleton.mp member
    subst value
    exact follows old oldMember

def Result.triangular : Result → Prop
  | .contradiction => True
  | .basis stored => Triangular stored

theorem Result.insert_triangular (result : Result) (valid : result.triangular) (row : Row) :
    (result.insert row).triangular := by
  cases result with
  | contradiction => trivial
  | basis basis =>
      have nodup := reduceWith_nodup basis valid.1 row.normalize row.normalize_nodup
      have erased := reduceWith_erases basis valid row.normalize row.normalize_nodup
      cases reduced : reduceWith basis row.normalize with
      | mk vars rhs =>
          rw [reduced] at nodup erased
          cases vars with
          | nil => cases rhs <;> simp only [insert, reduced, Result.triangular] <;> trivial
          | cons p vars =>
              simp only [insert, reduced, Result.triangular]
              exact triangular_append basis valid _ nodup (by simp) erased

theorem eliminateFrom_triangular (result : Result) (valid : result.triangular) (rows : List Row) :
    (eliminateFrom result rows).triangular := by
  induction rows generalizing result with
  | nil => exact valid
  | cons row rest ih => exact ih _ (Result.insert_triangular result valid row)

theorem eliminate_triangular (rows : List Row) : (eliminate rows).triangular :=
  eliminateFrom_triangular (.basis []) triangular_nil rows

end SaturationMonoid.ComplexityProjection.SATSource.Affine
