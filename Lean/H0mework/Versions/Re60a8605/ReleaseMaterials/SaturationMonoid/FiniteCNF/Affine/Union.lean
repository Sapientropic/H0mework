import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.BranchImage
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.EliminateCost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.Union

open InterferenceProgram

def pair (base : Result) (left right : Row) : EliminateCost.Outcome :=
  EliminateCost.runFrom base [Propagation.flip left,Propagation.flip right]

theorem pair_holds (base : Result) (left right : Row) (assignment : Nat → Bool) :
    (pair base left right).result.holds assignment =
      (base.holds assignment && (!left.holds assignment && !right.holds assignment)) := by
  rw [pair,EliminateCost.runFrom_result,eliminateFrom_holds]
  simp [holds,Propagation.flip_holds]

theorem pair_triangular (base : Result) (valid : base.triangular) (left right : Row) :
    (pair base left right).result.triangular := by
  rw [pair,EliminateCost.runFrom_result]
  exact eliminateFrom_triangular base valid _

def pairEmpty (base : Result) (left right : Row) : Bool :=
  match (pair base left right).result with
  | .contradiction => true
  | .basis _ => false

theorem pairEmpty_iff (base : Result) (valid : base.triangular) (left right : Row) :
    pairEmpty base left right = true ↔ ∀ assignment : Nat → Bool,
      base.holds assignment = true → left.holds assignment = true ∨ right.holds assignment = true := by
  constructor
  · intro empty assignment accepted
    by_cases first : left.holds assignment = true
    · exact Or.inl first
    · right
      by_contra second
      have same := pair_holds base left right assignment
      have dead : (pair base left right).result = .contradiction := by
        cases found : (pair base left right).result <;> simp_all [pairEmpty]
      rw [dead] at same
      change false = (base.holds assignment && (!left.holds assignment && !right.holds assignment)) at same
      simp [accepted,Bool.eq_false_iff.mpr first,Bool.eq_false_iff.mpr second] at same
  · intro covered
    cases generated : (pair base left right).result with
    | contradiction => simp [pairEmpty,generated]
    | basis basis =>
        have triangular : Triangular basis := by simpa only [generated,Result.triangular] using pair_triangular base valid left right
        let point := fill basis (fun _ => false)
        have realized : holds basis point = true := fill_holds basis triangular _
        have same := pair_holds base left right point
        rw [generated] at same
        change holds basis point = (base.holds point && (!left.holds point && !right.holds point)) at same
        rw [realized] at same
        have facts : base.holds point = true ∧ left.holds point = false ∧ right.holds point = false := by
          simpa using same.symm
        rcases covered point facts.1 with first | second
        · simp [facts.2.1] at first
        · simp [facts.2.2] at second

structure Check where
  accepted : Bool
  calls : Nat
  cells : Nat
  deriving Repr

def checkRight (base : Result) (left : Row) : List Row → Check
  | [] => ⟨true,0,1⟩
  | right::rest =>
      let tested := pair base left right
      match tested.result with
      | .contradiction =>
          let tail := checkRight base left rest
          ⟨tail.accepted,tail.calls+1,tested.cells+tail.cells+2⟩
      | .basis _ => ⟨false,1,tested.cells+2⟩

theorem checkRight_value (base : Result) (left : Row) (right : List Row) :
    (checkRight base left right).accepted = right.all (pairEmpty base left) := by
  induction right with
  | nil => rfl
  | cons row rest ih =>
      cases tested : (pair base left row).result <;> simp [checkRight,pairEmpty,tested,ih]

def check (base : Result) : List Row → List Row → Check
  | [],_ => ⟨true,0,1⟩
  | left::rest,right =>
      let first := checkRight base left right
      if first.accepted then
        let tail := check base rest right
        ⟨tail.accepted,first.calls+tail.calls,first.cells+tail.cells+2⟩
      else ⟨false,first.calls,first.cells+2⟩

theorem check_value (base : Result) (left right : List Row) :
    (check base left right).accepted = left.all (fun row => right.all (pairEmpty base row)) := by
  induction left with
  | nil => rfl
  | cons row rest ih =>
      simp only [check,List.all_cons]
      split <;> simp_all [checkRight_value]

theorem check_iff (base : Result) (valid : base.triangular) (left right : List Row) :
    (check base left right).accepted = true ↔ ∀ assignment : Nat → Bool,
      base.holds assignment = true → (holds left assignment || holds right assignment) = true := by
  rw [check_value]
  simp only [List.all_eq_true]
  constructor
  · intro tested assignment accepted
    by_cases first : holds left assignment = true
    · simp [first]
    · by_cases second : holds right assignment = true
      · simp [second]
      · obtain ⟨l,memberLeft,violatedLeft⟩ := List.all_eq_false.mp (Bool.eq_false_iff.mpr first)
        obtain ⟨r,memberRight,violatedRight⟩ := List.all_eq_false.mp (Bool.eq_false_iff.mpr second)
        have excluded := (pairEmpty_iff base valid l r).mp (tested l memberLeft r memberRight) assignment accepted
        rcases excluded with a | b
        · simp [violatedLeft] at a
        · simp [violatedRight] at b
  · intro covered l memberLeft r memberRight
    apply (pairEmpty_iff base valid l r).mpr
    intro assignment accepted
    have alternatives : holds left assignment = true ∨ holds right assignment = true := by
      simpa using covered assignment accepted
    rcases alternatives with first | second
    · exact Or.inl ((holds_iff _ _).mp first l memberLeft)
    · exact Or.inr ((holds_iff _ _).mp second r memberRight)

theorem checkRight_calls (base : Result) (left : Row) (right : List Row) :
    (checkRight base left right).calls ≤ right.length := by
  induction right with
  | nil => rfl
  | cons row rest ih =>
      cases tested : (pair base left row).result with
      | contradiction => simpa only [checkRight,tested,List.length_cons] using Nat.add_le_add_right ih 1
      | basis basis => simp [checkRight,tested]

theorem check_calls (base : Result) (left right : List Row) :
    (check base left right).calls ≤ left.length*right.length := by
  induction left with
  | nil => simp [check]
  | cons row rest ih =>
      have first := checkRight_calls base row right
      simp only [check,List.length_cons]
      split <;> simp only <;> nlinarith

def pairBudget (n : Nat) : Nat := 2*n*(2*n+5)+2*(EliminateCost.insertCellBudget n+1)+1

theorem pair_cells (n : Nat) (base : Result) (inside : base.within n) (triangular : base.triangular)
    (left right : Row) (leftValid : Table.RowValid n left) (rightValid : Table.RowValid n right) :
    (pair base left right).cells ≤ pairBudget n := by
  have rowsWithin : RowsWithin n [Propagation.flip left,Propagation.flip right] := by
    intro row member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact leftValid.2
    · exact rightValid.2
  have cost := EliminateCost.runFrom_cells n base triangular inside _ rowsWithin
  have first := Table.row_length_le n left leftValid
  have second := Table.row_length_le n right rightValid
  simp only [Gates.rowTerms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Propagation.flip,List.length_cons,List.length_nil] at cost
  apply cost.trans
  unfold pairBudget
  nlinarith

theorem checkRight_cells (n : Nat) (base : Result) (inside : base.within n) (triangular : base.triangular)
    (left : Row) (right : List Row) (leftValid : Table.RowValid n left)
    (rightValid : ∀ row ∈ right, Table.RowValid n row) :
    (checkRight base left right).cells ≤ right.length*(pairBudget n+2)+1 := by
  induction right with
  | nil => simp [checkRight]
  | cons row rest ih =>
      have first := pair_cells n base inside triangular left row leftValid (rightValid row (by simp))
      have tail := ih (fun other member => rightValid other (by simp [member]))
      cases tested : (pair base left row).result <;> simp only [checkRight,tested,List.length_cons] <;> nlinarith

theorem check_cells (n : Nat) (base : Result) (inside : base.within n) (triangular : base.triangular)
    (left right : List Row) (leftValid : ∀ row ∈ left, Table.RowValid n row)
    (rightValid : ∀ row ∈ right, Table.RowValid n row) :
    (check base left right).cells ≤ left.length*(right.length*(pairBudget n+2)+3)+1 := by
  induction left with
  | nil => simp [check]
  | cons row rest ih =>
      have first := checkRight_cells n base inside triangular row right (leftValid row (by simp)) rightValid
      have tail := ih (fun other member => leftValid other (by simp [member]))
      simp only [check,List.length_cons]
      split <;> simp only <;> nlinarith

structure Proposal where
  value : Option (List Row)
  calls : Nat
  checkCells : Nat
  deriving Repr

/-- The old generated affine hull is shared by every exact-union check. -/
def merge (n : Nat) (left right : List Row) : Proposal :=
  let base := BranchImage.join n (.basis left) (.basis right)
  let tested := check base left right
  let value := match base with
    | .contradiction => none
    | .basis rows => if tested.accepted then some rows else none
  ⟨value,tested.calls,tested.cells⟩

theorem merge_holds (n : Nat) (left right current : List Row)
    (leftInside : RowsWithin n left) (leftTriangular : Triangular left)
    (rightInside : RowsWithin n right) (rightTriangular : Triangular right)
    (found : (merge n left right).value = some current) (assignment : Nat → Bool) :
    holds current assignment = (holds left assignment || holds right assignment) := by
  have valid := BranchImage.join_invariants n (.basis left) (.basis right)
    leftInside leftTriangular rightInside rightTriangular
  cases generated : BranchImage.join n (.basis left) (.basis right) with
  | contradiction => simp [merge,generated] at found
  | basis base =>
      have accepted : (check (.basis base) left right).accepted = true := by
        by_contra rejected
        simp [merge,generated,rejected] at found
      have same : base = current := by simpa only [merge,generated,accepted,if_true,Option.some.injEq] using found
      subst current
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro realized
        have complete := (check_iff (.basis base) (by simpa only [generated,Result.triangular] using valid.2) left right).mp accepted
        exact complete assignment realized
      · intro realized
        have included := BranchImage.join_covers n (.basis left) (.basis right)
          leftInside leftTriangular rightInside rightTriangular assignment (by
            change holds left assignment = true ∨ holds right assignment = true
            simpa using realized)
        simpa only [generated,Result.holds] using included

theorem merge_valid (n : Nat) (left right current : List Row)
    (leftInside : RowsWithin n left) (leftTriangular : Triangular left)
    (rightInside : RowsWithin n right) (rightTriangular : Triangular right)
    (found : (merge n left right).value = some current) : RowsWithin n current ∧ Triangular current := by
  have valid := BranchImage.join_invariants n (.basis left) (.basis right)
    leftInside leftTriangular rightInside rightTriangular
  cases generated : BranchImage.join n (.basis left) (.basis right) with
  | contradiction => simp [merge,generated] at found
  | basis base =>
      simp only [merge,generated] at found
      split at found
      · have same : base = current := Option.some.inj found
        simpa only [generated,Result.within,Result.triangular,same] using valid
      · cases found

theorem merge_calls (n : Nat) (left right : List Row)
    (leftInside : RowsWithin n left) (leftTriangular : Triangular left)
    (rightInside : RowsWithin n right) (rightTriangular : Triangular right) :
    (merge n left right).calls ≤ n*n :=
  (check_calls _ left right).trans (Nat.mul_le_mul
    (basis_length_le n left leftTriangular leftInside) (basis_length_le n right rightTriangular rightInside))

theorem merge_checkCells (n : Nat) (left right : List Row)
    (leftInside : RowsWithin n left) (leftTriangular : Triangular left)
    (rightInside : RowsWithin n right) (rightTriangular : Triangular right) :
    (merge n left right).checkCells ≤ n*(n*(pairBudget n+2)+3)+1 := by
  have valid := BranchImage.join_invariants n (.basis left) (.basis right)
    leftInside leftTriangular rightInside rightTriangular
  have checked := check_cells n _ valid.1 valid.2 left right
    (fun row member => ⟨leftTriangular.1 row member,leftInside row member⟩)
    (fun row member => ⟨rightTriangular.1 row member,rightInside row member⟩)
  apply checked.trans
  gcongr
  · exact basis_length_le n left leftTriangular leftInside
  · exact basis_length_le n right rightTriangular rightInside

end SaturationMonoid.ComplexityProjection.SATSource.Affine.Union
