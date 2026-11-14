import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Parity

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine

open InterferenceProgram

structure Row where
  vars : List Nat
  rhs : Bool
  deriving DecidableEq, Repr

def Row.eval (row : Row) (assignment : Nat → Bool) : Bool := Parity.eval assignment row.vars

def Row.holds (row : Row) (assignment : Nat → Bool) : Bool := row.eval assignment == row.rhs

theorem Row.holds_iff (row : Row) (assignment : Nat → Bool) :
    row.holds assignment = true ↔ row.eval assignment = row.rhs := by
  simp [Row.holds]

def Row.normalize (row : Row) : Row := ⟨Parity.merge row.vars [], row.rhs⟩

theorem Row.normalize_eval (row : Row) (assignment : Nat → Bool) :
    row.normalize.eval assignment = row.eval assignment := by
  simp only [normalize, eval, Parity.eval_merge, Parity.eval, Bool.xor_false]

theorem Row.normalize_holds (row : Row) (assignment : Nat → Bool) :
    row.normalize.holds assignment = row.holds assignment := by
  change (row.normalize.eval assignment == row.rhs) = (row.eval assignment == row.rhs)
  rw [normalize_eval]

theorem Row.normalize_nodup (row : Row) : row.normalize.vars.Nodup :=
  Parity.merge_nodup _ _ (by simp)

def Row.xor (left right : Row) : Row :=
  ⟨Parity.merge left.vars right.vars, left.rhs ^^ right.rhs⟩

theorem Row.xor_eval (left right : Row) (assignment : Nat → Bool) :
    (left.xor right).eval assignment = (left.eval assignment ^^ right.eval assignment) :=
  Parity.eval_merge assignment left.vars right.vars

theorem Row.xor_nodup (left right : Row) (nodup : right.vars.Nodup) :
    (left.xor right).vars.Nodup := Parity.merge_nodup _ _ nodup

theorem Row.xor_holds (left right : Row) (assignment : Nat → Bool)
    (accepted : right.holds assignment = true) :
    (left.xor right).holds assignment = left.holds assignment := by
  have rightValue := (right.holds_iff assignment).mp accepted
  change ((left.xor right).eval assignment == (left.rhs ^^ right.rhs)) = (left.eval assignment == left.rhs)
  rw [xor_eval, rightValue]
  cases left.eval assignment <;> cases left.rhs <;> cases right.rhs <;> rfl

def holds (rows : List Row) (assignment : Nat → Bool) : Bool := rows.all (fun row => row.holds assignment)

theorem holds_iff (rows : List Row) (assignment : Nat → Bool) :
    holds rows assignment = true ↔ ∀ row ∈ rows, row.holds assignment = true := by
  simp [holds]

def reduceWith (basis : List Row) (row : Row) : Row :=
  basis.foldl (fun current pivot =>
    match pivot.vars with
    | [] => current
    | pivotVar :: _ => if pivotVar ∈ current.vars then current.xor pivot else current) row

theorem reduceWith_holds (basis : List Row) (row : Row) (assignment : Nat → Bool)
    (accepted : holds basis assignment = true) :
    (reduceWith basis row).holds assignment = row.holds assignment := by
  induction basis generalizing row with
  | nil => rfl
  | cons pivot rest ih =>
      have head : pivot.holds assignment = true := ((holds_iff _ _).mp accepted) pivot (by simp)
      have tail : holds rest assignment = true := (holds_iff _ _).mpr
        (fun value member => ((holds_iff _ _).mp accepted) value (by simp [member]))
      simp only [reduceWith, List.foldl_cons]
      change (reduceWith rest _).holds assignment = _
      rw [ih _ tail]
      cases shape : pivot.vars with
      | nil => simp only
      | cons pivotVar vars =>
          simp only
          split
          · exact Row.xor_holds row pivot assignment head
          · rfl

theorem empty_holds (rhs : Bool) (assignment : Nat → Bool) :
    (Row.mk [] rhs).holds assignment = !rhs := by
  cases rhs <;> rfl

end SaturationMonoid.ComplexityProjection.SATSource.Affine
