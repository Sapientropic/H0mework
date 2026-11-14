import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Row

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine

inductive Result where
  | contradiction
  | basis : List Row → Result
  deriving DecidableEq, Repr

def Result.holds : Result → (Nat → Bool) → Bool
  | .contradiction, _ => false
  | .basis stored, assignment => Affine.holds stored assignment

def Result.insert (result : Result) (row : Row) : Result :=
  match result with
  | .contradiction => .contradiction
  | .basis stored =>
      let reduced := reduceWith stored row.normalize
      match reduced.vars with
      | [] => if reduced.rhs then .contradiction else .basis stored
      | _ :: _ => .basis (stored ++ [reduced])

theorem Result.insert_holds (result : Result) (row : Row) (assignment : Nat → Bool) :
    (result.insert row).holds assignment = (result.holds assignment && row.holds assignment) := by
  cases result with
  | contradiction => rfl
  | basis basis =>
      by_cases accepted : Affine.holds basis assignment = true
      · have value : (reduceWith basis row.normalize).holds assignment = row.holds assignment :=
          (reduceWith_holds basis row.normalize assignment accepted).trans (row.normalize_holds assignment)
        change (Result.insert (.basis basis) row).holds assignment =
          (Affine.holds basis assignment && row.holds assignment)
        rw [accepted, Bool.true_and]
        cases reduced : reduceWith basis row.normalize with
        | mk vars rhs =>
            rw [reduced] at value
            cases vars with
            | nil =>
                rw [empty_holds] at value
                cases rhs <;> simp only [insert, reduced, Result.holds]
                · simpa [accepted] using value
                · simpa using value
            | cons v vars =>
                simp only [insert, reduced, Result.holds]
                simp only [Affine.holds, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
                change (Affine.holds basis assignment && (Row.mk (v :: vars) rhs).holds assignment) = _
                rw [accepted, Bool.true_and]
                exact value
      · have rejected : Affine.holds basis assignment = false := Bool.eq_false_iff.mpr accepted
        cases reduced : reduceWith basis row.normalize with
        | mk vars rhs =>
            cases vars with
            | nil => cases rhs <;> simp [insert, reduced, Result.holds, rejected]
            | cons v vars => simp [insert, reduced, Result.holds, Affine.holds, List.all_append,
                show basis.all (fun row => row.holds assignment) = false from rejected]

def eliminateFrom (result : Result) (rows : List Row) : Result := rows.foldl Result.insert result

theorem eliminateFrom_holds (result : Result) (rows : List Row) (assignment : Nat → Bool) :
    (eliminateFrom result rows).holds assignment = (result.holds assignment && Affine.holds rows assignment) := by
  induction rows generalizing result with
  | nil => simp [eliminateFrom, Affine.holds]
  | cons row rest ih =>
      simp only [eliminateFrom, List.foldl_cons]
      change (eliminateFrom (result.insert row) rest).holds assignment = _
      rw [ih, Result.insert_holds]
      simp [Affine.holds, Bool.and_assoc]

def eliminate (rows : List Row) : Result := eliminateFrom (.basis []) rows

theorem eliminate_holds (rows : List Row) (assignment : Nat → Bool) :
    (eliminate rows).holds assignment = Affine.holds rows assignment := by
  rw [eliminate, eliminateFrom_holds]
  rfl

theorem contradiction_unsatisfiable (rows : List Row) (contradiction : eliminate rows = .contradiction) :
    ∀ assignment : Nat → Bool, Affine.holds rows assignment = false := by
  intro assignment
  rw [← eliminate_holds, contradiction]
  rfl

theorem basis_solutions (rows basis : List Row) (generated : eliminate rows = .basis basis)
    (assignment : Nat → Bool) : Affine.holds basis assignment = Affine.holds rows assignment := by
  rw [← eliminate_holds rows assignment, generated]
  rfl

end SaturationMonoid.ComplexityProjection.SATSource.Affine
