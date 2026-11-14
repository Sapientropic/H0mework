import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.JointFeedback

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.BranchImage

open InterferenceProgram

def leftAddress (i : Nat) : Nat := 2*i+1
def rightAddress (i : Nat) : Nat := 2*i+2

def mergeRow (left right : Row) : Row :=
  ⟨left.vars.map leftAddress ++ right.vars.map rightAddress ++
    (if left.rhs ^^ right.rhs then [0] else []), left.rhs⟩

def leftSeed (environment : Nat → Bool) (i : Nat) : Bool :=
  if i%2=1 then environment (i/2) else false

def rightSeed (environment : Nat → Bool) (i : Nat) : Bool :=
  if i=0 then true else if i%2=0 then environment (i/2-1) else false

theorem leftSeed_zero (environment : Nat → Bool) : leftSeed environment 0 = false := rfl

theorem leftSeed_left (environment : Nat → Bool) (i : Nat) :
    leftSeed environment (leftAddress i) = environment i := by
  simp only [leftSeed, leftAddress]
  have odd : (2*i+1)%2=1 := by omega
  have div : (2*i+1)/2=i := by omega
  simp [odd, div]

theorem leftSeed_right (environment : Nat → Bool) (i : Nat) :
    leftSeed environment (rightAddress i) = false := by
  simp only [leftSeed, rightAddress]
  have even : (2*i+2)%2≠1 := by omega
  simp

theorem rightSeed_zero (environment : Nat → Bool) : rightSeed environment 0 = true := rfl

theorem rightSeed_left (environment : Nat → Bool) (i : Nat) :
    rightSeed environment (leftAddress i) = false := by
  simp only [rightSeed, leftAddress]
  have nonzero : 2*i+1≠0 := by omega
  have odd : (2*i+1)%2≠0 := by omega
  simp

theorem rightSeed_right (environment : Nat → Bool) (i : Nat) :
    rightSeed environment (rightAddress i) = environment i := by
  simp only [rightSeed, rightAddress]
  have nonzero : 2*i+2≠0 := by omega
  have even : (2*i+2)%2=0 := by omega
  have div : (2*i+2)/2-1=i := by omega
  simp [even]

theorem parity_append (environment : Nat → Bool) (left right : List Nat) :
    Parity.eval environment (left++right) =
      (Parity.eval environment left ^^ Parity.eval environment right) := by
  induction left with
  | nil => simp [Parity.eval]
  | cons i rest ih => simp only [List.cons_append, Parity.eval, ih, Bool.xor_assoc]

theorem parity_false (terms : List Nat) : Parity.eval (fun _ => false) terms = false := by
  induction terms with
  | nil => rfl
  | cons i rest ih => simp [Parity.eval, ih]

theorem mergeRow_left (left right : Row) (environment : Nat → Bool) :
    Gates.value (mergeRow left right) (leftSeed environment) = Gates.value left environment := by
  simp only [Gates.value, Row.eval, mergeRow, parity_append, Parity.eval_map]
  have first : (fun i => leftSeed environment (leftAddress i)) = environment := by
    funext i
    exact leftSeed_left environment i
  have second : (fun i => leftSeed environment (rightAddress i)) = fun _ => false := by
    funext i
    exact leftSeed_right environment i
  rw [first, second, parity_false]
  cases left.rhs <;> cases right.rhs <;> simp [Parity.eval, leftSeed]

theorem mergeRow_right (left right : Row) (environment : Nat → Bool) :
    Gates.value (mergeRow left right) (rightSeed environment) = Gates.value right environment := by
  simp only [Gates.value, Row.eval, mergeRow, parity_append, Parity.eval_map]
  have first : (fun i => rightSeed environment (leftAddress i)) = fun _ => false := by
    funext i
    exact rightSeed_left environment i
  have second : (fun i => rightSeed environment (rightAddress i)) = environment := by
    funext i
    exact rightSeed_right environment i
  rw [first, second, parity_false]
  cases left.rhs <;> cases right.rhs <;> simp [Parity.eval, rightSeed]

/-- The table generates the affine hull of the two actual parameterized sources. -/
def table (n : Nat) (left right : Array Row) : Array Row :=
  (List.ofFn fun i : Fin n => mergeRow (left.getD i.val Gates.zeroRow)
    (right.getD i.val Gates.zeroRow)).toArray

@[simp] theorem table_size (n : Nat) (left right : Array Row) : (table n left right).size=n := by
  simp [table]

theorem table_get (n : Nat) (left right : Array Row) (i : Fin n) :
    (table n left right).getD i.val Gates.zeroRow =
      mergeRow (left.getD i.val Gates.zeroRow) (right.getD i.val Gates.zeroRow) := by
  simp [table, Array.getD_eq_getD_getElem?]

theorem table_left (n : Nat) (left right : Array Row) (environment : Nat → Bool) (i : Fin n) :
    Gates.coordinate (table n left right) (leftSeed environment) i.val =
      Gates.coordinate left environment i.val := by
  rw [Table.coordinate_getD, table_get, mergeRow_left, ← Table.coordinate_getD]

theorem table_right (n : Nat) (left right : Array Row) (environment : Nat → Bool) (i : Fin n) :
    Gates.coordinate (table n left right) (rightSeed environment) i.val =
      Gates.coordinate right environment i.val := by
  rw [Table.coordinate_getD, table_get, mergeRow_right, ← Table.coordinate_getD]

theorem mergeRow_within (n : Nat) (left right : Row)
    (leftWithin : Parity.Within n left.vars) (rightWithin : Parity.Within n right.vars) :
    Parity.Within (2*n+1) (mergeRow left right).vars := by
  intro i member
  simp only [mergeRow, List.mem_append, List.mem_map] at member
  rcases member with (⟨j, hit, rfl⟩ | ⟨j, hit, rfl⟩) | member
  · have inside := leftWithin j hit
    simp only [leftAddress]
    omega
  · have inside := rightWithin j hit
    simp only [rightAddress]
    omega
  · split at member
    · simp only [List.mem_singleton] at member
      subst i
      omega
    · simp at member

theorem table_within (n : Nat) (left right : Array Row)
    (leftWithin : AtomImage.SourceWithin n left) (rightWithin : AtomImage.SourceWithin n right) :
    AtomImage.SourceWithin (2*n+1) (table n left right) := by
  intro row member
  simp only [table, List.toList_toArray, List.mem_ofFn] at member
  obtain ⟨i,rfl⟩ := member
  apply mergeRow_within n
  · by_cases valid : i.val < left.size
    · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem valid, Option.getD_some]
      exact leftWithin _ (Array.getElem_mem_toList valid)
    · simp [Array.getD, valid, Gates.zeroRow, Parity.Within]
  · by_cases valid : i.val < right.size
    · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem valid, Option.getD_some]
      exact rightWithin _ (Array.getElem_mem_toList valid)
    · simp [Array.getD, valid, Gates.zeroRow, Parity.Within]

theorem coordinates_within (n : Nat) (basis : List Row) :
    AtomImage.SourceWithin n (Table.coordinates n basis) := by
  intro row member i hit
  exact lt_of_lt_of_le ((Table.coordinates_valid n basis row member).2 i hit) (Table.freeWidth_le n basis)

def source (n : Nat) (left right : List Row) : Array Row :=
  table n (Table.coordinates n left) (Table.coordinates n right)

@[simp] theorem source_size (n : Nat) (left right : List Row) : (source n left right).size=n := by
  simp [source]

theorem source_within (n : Nat) (left right : List Row) :
    AtomImage.SourceWithin (2*n+1) (source n left right) :=
  table_within n _ _ (coordinates_within n left) (coordinates_within n right)

def common (n : Nat) (left right : List Row) : List Row :=
  (AtomImage.generate (source n left right)).kernel

theorem common_within (n : Nat) (left right : List Row) : RowsWithin n (common n left right) := by
  intro row member
  have valid := (AtomImage.generate_valid (2*n+1) (source n left right) (source_within n left right)).2 row member
  simpa only [source_size] using valid.2

theorem common_length (n : Nat) (left right : List Row) : (common n left right).length ≤ n := by
  have count := AtomImage.generate_count (source n left right)
  simp only [source_size] at count
  unfold common
  omega

theorem coordinate_recovery (n : Nat) (basis : List Row) (inside : RowsWithin n basis)
    (triangular : Triangular basis) (assignment : Nat → Bool) (accepted : holds basis assignment = true) :
    ∃ environment : Nat → Bool, ∀ i : Fin n,
      Gates.coordinate (Table.coordinates n basis) environment i.val = assignment i.val := by
  let finite : Assignment n := fun i => assignment i.val
  have acceptedFinite : holds basis (extendAssignment finite) = true :=
    (AtomSource.holds_restrict n basis inside assignment).trans accepted
  have recovered := (Decision.table_lift n basis inside (projectFree n basis finite)).trans
    (parameterLift_projectFree n basis triangular finite acceptedFinite)
  refine ⟨extendAssignment (projectFree n basis finite), ?_⟩
  intro i
  exact congrFun recovered i

theorem common_left (n : Nat) (left right : List Row) (inside : RowsWithin n left)
    (triangular : Triangular left) (assignment : Nat → Bool) (accepted : holds left assignment = true) :
    holds (common n left right) assignment = true := by
  obtain ⟨environment, recovered⟩ := coordinate_recovery n left inside triangular assignment accepted
  apply (AtomImage.image_iff_kernel (source n left right) assignment).mp
  refine ⟨leftSeed environment, ?_⟩
  intro i
  let j : Fin n := ⟨i.val, by simpa using i.isLt⟩
  exact (table_left n _ _ environment j).trans (recovered j)

theorem common_right (n : Nat) (left right : List Row) (inside : RowsWithin n right)
    (triangular : Triangular right) (assignment : Nat → Bool) (accepted : holds right assignment = true) :
    holds (common n left right) assignment = true := by
  obtain ⟨environment, recovered⟩ := coordinate_recovery n right inside triangular assignment accepted
  apply (AtomImage.image_iff_kernel (source n left right) assignment).mp
  refine ⟨rightSeed environment, ?_⟩
  intro i
  let j : Fin n := ⟨i.val, by simpa using i.isLt⟩
  exact (table_right n _ _ environment j).trans (recovered j)

theorem parity_xor (left right : Nat → Bool) (terms : List Nat) :
    Parity.eval (fun i => left i ^^ right i) terms =
      (Parity.eval left terms ^^ Parity.eval right terms) := by
  induction terms with
  | nil => rfl
  | cons i rest ih =>
      simp only [Parity.eval, ih]
      simp [Bool.xor_left_comm]

theorem row_three (row : Row) (left right anchor : Nat → Bool)
    (a : row.holds left = true) (b : row.holds right = true) (c : row.holds anchor = true) :
    row.holds (fun i => left i ^^ right i ^^ anchor i) = true := by
  rw [Row.holds_iff] at a b c ⊢
  change Parity.eval (fun i => (left i ^^ right i) ^^ anchor i) row.vars = _
  rw [parity_xor, parity_xor]
  change (row.eval left ^^ row.eval right ^^ row.eval anchor) = _
  rw [a,b,c]
  simp

theorem mergeRow_three (left right : Row) (environment : Nat → Bool) :
    Gates.value (mergeRow left right) environment =
      (Gates.value left (fun i => environment (leftAddress i)) ^^
       Gates.value right (fun i => environment (rightAddress i)) ^^
       if environment 0 then Gates.value left (fun _ => false) else Gates.value right (fun _ => false)) := by
  simp only [Gates.value, Row.eval, mergeRow, parity_append, Parity.eval_map, parity_false]
  cases left.rhs <;> cases right.rhs <;> cases zero : environment 0 <;>
    simp [Parity.eval, zero, Bool.xor_comm]

theorem table_three (n : Nat) (left right : Array Row) (environment : Nat → Bool) (i : Fin n) :
    Gates.coordinate (table n left right) environment i.val =
      (Gates.coordinate left (fun j => environment (leftAddress j)) i.val ^^
       Gates.coordinate right (fun j => environment (rightAddress j)) i.val ^^
       if environment 0 then Gates.coordinate left (fun _ => false) i.val
       else Gates.coordinate right (fun _ => false) i.val) := by
  simp only [Table.coordinate_getD, table_get, mergeRow_three]

theorem common_complete (n : Nat) (left right : List Row)
    (leftWithin : RowsWithin n left) (leftTriangular : Triangular left)
    (rightWithin : RowsWithin n right) (rightTriangular : Triangular right)
    (row : Row) (inside : Parity.Within n row.vars)
    (leftRule : ∀ assignment, holds left assignment = true → row.holds assignment = true)
    (rightRule : ∀ assignment, holds right assignment = true → row.holds assignment = true)
    (assignment : Nat → Bool) (accepted : holds (common n left right) assignment = true) :
    row.holds assignment = true := by
  obtain ⟨environment,realized⟩ := (AtomImage.image_iff_kernel (source n left right) assignment).mpr accepted
  have first (parameters : Nat → Bool) : row.holds (Gates.coordinate (Table.coordinates n left) parameters) = true := by
    apply leftRule
    rw [Table.coordinates_value n left leftWithin]
    exact fill_holds left leftTriangular _
  have second (parameters : Nat → Bool) : row.holds (Gates.coordinate (Table.coordinates n right) parameters) = true := by
    apply rightRule
    rw [Table.coordinates_value n right rightWithin]
    exact fill_holds right rightTriangular _
  let anchor := if environment 0 then Gates.coordinate (Table.coordinates n left) (fun _ => false)
    else Gates.coordinate (Table.coordinates n right) (fun _ => false)
  have anchorRule : row.holds anchor = true := by
    dsimp only [anchor]
    split
    · exact first _
    · exact second _
  have combined := row_three row _ _ anchor
    (first (fun i => environment (leftAddress i))) (second (fun i => environment (rightAddress i))) anchorRule
  have same : row.holds assignment =
      row.holds (fun i => Gates.coordinate (Table.coordinates n left) (fun j => environment (leftAddress j)) i ^^
        Gates.coordinate (Table.coordinates n right) (fun j => environment (rightAddress j)) i ^^ anchor i) := by
    apply congrArg (fun value => value == row.rhs)
    apply Parity.eval_congr
    intro i member
    let j : Fin n := ⟨i,inside i member⟩
    have equality := realized ⟨i,by simpa only [source_size] using inside i member⟩
    apply equality.symm.trans
    have mixed := table_three n (Table.coordinates n left) (Table.coordinates n right) environment j
    apply mixed.trans
    dsimp only [anchor]
    split <;> rfl
  exact same.trans combined

theorem mergeRow_length (left right : Row) :
    (mergeRow left right).vars.length ≤ left.vars.length+right.vars.length+1 := by
  simp only [mergeRow, List.length_append, List.length_map]
  split <;> simp

theorem source_storage (n : Nat) (left right : List Row) :
    Gates.rowTerms (source n left right).toList ≤ n*(2*n+1) := by
  have perRow : ∀ row ∈ (source n left right).toList, row.vars.length ≤ 2*n+1 := by
    intro row member
    simp only [source, table, List.toList_toArray, List.mem_ofFn] at member
    obtain ⟨i,rfl⟩ := member
    have leftBound := Table.row_length_le _ _ (Table.read_valid _ _ (Table.coordinates_valid n left) i.val)
    have rightBound := Table.row_length_le _ _ (Table.read_valid _ _ (Table.coordinates_valid n right) i.val)
    have leftSize := Table.freeWidth_le n left
    have rightSize := Table.freeWidth_le n right
    have merged := mergeRow_length ((Table.coordinates n left).getD i.val Gates.zeroRow)
      ((Table.coordinates n right).getD i.val Gates.zeroRow)
    omega
  have bound : ∀ rows : List Row, (∀ row ∈ rows, row.vars.length ≤ 2*n+1) →
      Gates.rowTerms rows ≤ rows.length*(2*n+1) := by
    intro rows valid
    induction rows with
    | nil => simp [Gates.rowTerms]
    | cons row rest ih =>
        have tail := ih (fun other member => valid other (by simp [member]))
        have head := valid row (by simp)
        simp only [Gates.rowTerms, List.map_cons, List.sum_cons, List.length_cons] at *
        nlinarith
  simpa only [Array.length_toList, source_size] using bound _ perRow

theorem common_visits (n : Nat) (left right : List Row) :
    AtomImage.generateVisits (source n left right) ≤
      (n*(2*n+1)+n)*(2*((2*n+1)+n)+5)+
      n*((2*n+1)*AtomImage.stepBudget (2*n+1) n+n+11)+2 := by
  have bound := AtomImage.generateVisits_bound (2*n+1) (source n left right) (source_within n left right)
  simp only [source_size] at bound
  apply bound.trans
  gcongr
  exact source_storage n left right

def join (n : Nat) : Result → Result → Result
  | .contradiction, right => right
  | left, .contradiction => left
  | .basis left, .basis right => eliminate (common n left right)

theorem join_invariants (n : Nat) (left right : Result)
    (leftWithin : left.within n) (leftTriangular : left.triangular)
    (rightWithin : right.within n) (rightTriangular : right.triangular) :
    (join n left right).within n ∧ (join n left right).triangular := by
  cases left with
  | contradiction => exact ⟨rightWithin,rightTriangular⟩
  | basis left =>
      cases right with
      | contradiction => exact ⟨leftWithin,leftTriangular⟩
      | basis right => exact ⟨eliminate_within n _ (common_within n left right), eliminate_triangular _⟩

theorem join_covers (n : Nat) (left right : Result)
    (leftWithin : left.within n) (leftTriangular : left.triangular)
    (rightWithin : right.within n) (rightTriangular : right.triangular)
    (assignment : Nat → Bool) (accepted : left.holds assignment = true ∨ right.holds assignment = true) :
    (join n left right).holds assignment = true := by
  cases left with
  | contradiction => simpa only [join, Result.holds, Bool.false_eq_true, false_or] using accepted
  | basis left =>
      cases right with
      | contradiction => simpa only [join, Result.holds, Bool.false_eq_true, or_false] using accepted
      | basis right =>
          rw [join, eliminate_holds]
          rcases accepted with accepted | accepted
          · exact common_left n left right leftWithin leftTriangular assignment accepted
          · exact common_right n left right rightWithin rightTriangular assignment accepted

def branch {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n) (value : Bool) : Result :=
  JointFeedback.iterate formula (n+1) (result.insert ⟨[i.val],value⟩)

theorem branch_holds {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n) (value : Bool)
    (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (branch formula result i value).holds assignment) =
      (CNFFormula.eval formula assignment && result.holds assignment && (assignment i.val == value)) := by
  rw [branch, JointFeedback.iterate_holds, Result.insert_holds]
  simp [Row.holds, Row.eval, Parity.eval, Bool.and_assoc]

theorem branch_invariants {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n) (value : Bool)
    (inside : result.within n) (triangular : result.triangular) :
    (branch formula result i value).within n ∧ (branch formula result i value).triangular := by
  apply JointFeedback.iterate_invariants
  · exact Result.insert_within n result inside _ (by simp only [Parity.Within, List.mem_singleton, forall_eq]; exact i.isLt)
  · exact Result.insert_triangular result triangular _

def absorb (result learned : Result) : Result :=
  match learned with
  | .contradiction => .contradiction
  | .basis rows => eliminateFrom result rows

theorem absorb_holds (result learned : Result) (assignment : Nat → Bool) :
    (absorb result learned).holds assignment = (result.holds assignment && learned.holds assignment) := by
  cases learned with
  | contradiction => simp [absorb, Result.holds]
  | basis rows => exact eliminateFrom_holds result rows assignment

theorem absorb_invariants (n : Nat) (result learned : Result)
    (inside : result.within n) (triangular : result.triangular) (learnedWithin : learned.within n) :
    (absorb result learned).within n ∧ (absorb result learned).triangular := by
  cases learned with
  | contradiction => exact ⟨True.intro,True.intro⟩
  | basis rows => exact ⟨eliminateFrom_within n result inside rows learnedWithin,
      eliminateFrom_triangular result triangular rows⟩

def refine {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n) : Result :=
  let left := branch formula result i false
  let right := branch formula result i true
  absorb result (join n left right)

theorem refine_invariants {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n)
    (inside : result.within n) (triangular : result.triangular) :
    (refine formula result i).within n ∧ (refine formula result i).triangular := by
  have left := branch_invariants formula result i false inside triangular
  have right := branch_invariants formula result i true inside triangular
  exact absorb_invariants n result _ inside triangular (join_invariants n _ _ left.1 left.2 right.1 right.2).1

theorem refine_holds {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n)
    (inside : result.within n) (triangular : result.triangular) (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (refine formula result i).holds assignment) =
      (CNFFormula.eval formula assignment && result.holds assignment) := by
  unfold refine
  rw [absorb_holds]
  by_cases accepted : CNFFormula.eval formula assignment = true
  · by_cases relations : result.holds assignment = true
    · have actual : (branch formula result i (assignment i.val)).holds assignment = true := by
        have equation := branch_holds formula result i (assignment i.val) assignment
        simpa only [accepted, relations, Bool.true_and, Bool.and_true, beq_self_eq_true] using equation
      have left := branch_invariants formula result i false inside triangular
      have right := branch_invariants formula result i true inside triangular
      have learned := join_covers n _ _ left.1 left.2 right.1 right.2 assignment (by
        cases selected : assignment i.val
        · exact Or.inl (by simpa only [selected] using actual)
        · exact Or.inr (by simpa only [selected] using actual))
      simp [accepted, relations, learned]
    · simp [relations]
  · simp [accepted]

theorem eliminateFrom_contradiction (rows : List Row) : eliminateFrom .contradiction rows = .contradiction := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simpa only [eliminateFrom, List.foldl_cons, Result.insert] using ih

theorem absorb_contradiction (learned : Result) : absorb .contradiction learned = .contradiction := by
  cases learned with
  | contradiction => rfl
  | basis rows => exact eliminateFrom_contradiction rows

theorem refine_contradiction {n : Nat} (formula : CNFFormula n) (i : Fin n) :
    refine formula .contradiction i = .contradiction := absorb_contradiction _

theorem absorb_retains (basis : List Row) (learned : Result) (current : List Row)
    (produced : absorb (.basis basis) learned = .basis current) : basis.IsPrefix current := by
  cases learned with
  | contradiction => cases produced
  | basis rows => exact Atoms.eliminateFrom_prefix basis rows current produced

theorem refine_progress {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n)
    (inside : result.within n) (triangular : result.triangular) (changed : refine formula result i ≠ result) :
    Propagation.remaining n (refine formula result i) < Propagation.remaining n result := by
  cases result with
  | contradiction => exact False.elim (changed (refine_contradiction formula i))
  | basis basis =>
      have rank := basis_length_le n basis triangular inside
      cases next : refine formula (.basis basis) i with
      | contradiction => simp only [Propagation.remaining]; omega
      | basis current =>
          have pref := absorb_retains basis _ current next
          have apart : basis ≠ current := by
            intro same
            exact changed (by simpa only [same] using next)
          have growth : basis.length < current.length := by
            by_contra! absent
            exact apart (pref.eq_of_length_le absent)
          simp only [Propagation.remaining]
          omega

def scan {n : Nat} (formula : CNFFormula n) : List (Fin n) → Result → Result × Nat
  | [], result => (result,0)
  | i :: rest, result =>
      let next := refine formula result i
      if next = result then
        let tail := scan formula rest result
        (tail.1,tail.2+1)
      else (next,1)

theorem scan_trials {n : Nat} (formula : CNFFormula n) (indices : List (Fin n)) (result : Result) :
    (scan formula indices result).2 ≤ indices.length := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [scan]
      split
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        omega

theorem scan_invariants {n : Nat} (formula : CNFFormula n) (indices : List (Fin n)) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    (scan formula indices result).1.within n ∧ (scan formula indices result).1.triangular := by
  induction indices with
  | nil => exact ⟨inside,triangular⟩
  | cons i rest ih =>
      simp only [scan]
      split
      · exact ih
      · exact refine_invariants formula result i inside triangular

theorem scan_holds {n : Nat} (formula : CNFFormula n) (indices : List (Fin n)) (result : Result)
    (inside : result.within n) (triangular : result.triangular) (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (scan formula indices result).1.holds assignment) =
      (CNFFormula.eval formula assignment && result.holds assignment) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [scan]
      split
      · exact ih
      · exact refine_holds formula result i inside triangular assignment

theorem scan_progress {n : Nat} (formula : CNFFormula n) (indices : List (Fin n)) (result : Result)
    (inside : result.within n) (triangular : result.triangular)
    (changed : (scan formula indices result).1 ≠ result) :
    Propagation.remaining n (scan formula indices result).1 < Propagation.remaining n result := by
  induction indices with
  | nil => exact False.elim (changed rfl)
  | cons i rest ih =>
      by_cases fixed : refine formula result i = result
      · simp only [scan, if_pos fixed] at changed ⊢
        exact ih changed
      · simp only [scan, if_neg fixed]
        exact refine_progress formula result i inside triangular fixed

theorem scan_fixed {n : Nat} (formula : CNFFormula n) (indices : List (Fin n)) (result : Result) :
    (scan formula indices result).1 = result ↔ ∀ i ∈ indices, refine formula result i = result := by
  induction indices with
  | nil => simp [scan]
  | cons i rest ih =>
      simp only [scan]
      split
      · rename_i fixed
        simpa only [List.forall_mem_cons, fixed, true_and] using ih
      · rename_i changed
        simp only [changed, List.forall_mem_cons, false_and]

def iterate {n : Nat} (formula : CNFFormula n) : Nat → Result → Result
  | 0, result => result
  | fuel+1, result => iterate formula fuel (scan formula (List.finRange n) result).1

theorem iterate_invariants {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    (iterate formula fuel result).within n ∧ (iterate formula fuel result).triangular := by
  induction fuel generalizing result with
  | zero => exact ⟨inside,triangular⟩
  | succ fuel ih =>
      have valid := scan_invariants formula (List.finRange n) result inside triangular
      exact ih _ valid.1 valid.2

theorem iterate_holds {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (inside : result.within n) (triangular : result.triangular) (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (iterate formula fuel result).holds assignment) =
      (CNFFormula.eval formula assignment && result.holds assignment) := by
  induction fuel generalizing result with
  | zero => rfl
  | succ fuel ih =>
      have valid := scan_invariants formula (List.finRange n) result inside triangular
      exact (ih _ valid.1 valid.2).trans (scan_holds formula _ result inside triangular assignment)

theorem iterate_fixed {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (fixed : (scan formula (List.finRange n) result).1 = result) : iterate formula fuel result = result := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [iterate, fixed] using ih

theorem iterate_settled {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (inside : result.within n) (triangular : result.triangular)
    (enough : Propagation.remaining n result ≤ fuel) :
    (scan formula (List.finRange n) (iterate formula fuel result)).1 = iterate formula fuel result := by
  induction fuel generalizing result with
  | zero =>
      cases result with
      | contradiction =>
          apply (scan_fixed formula _ _).mpr
          intro i _
          exact refine_contradiction formula i
      | basis basis =>
          have rank := basis_length_le n basis triangular inside
          simp only [Propagation.remaining] at enough
          omega
  | succ fuel ih =>
      by_cases fixed : (scan formula (List.finRange n) result).1 = result
      · rw [iterate_fixed formula (fuel+1) result fixed]
        exact fixed
      · have progress := scan_progress formula (List.finRange n) result inside triangular fixed
        have next := scan_invariants formula (List.finRange n) result inside triangular
        exact ih _ next.1 next.2 (by omega)

def generate {n : Nat} (formula : CNFFormula n) (rows : List Row) : Result :=
  iterate formula (n+1) (JointFeedback.generate formula rows)

theorem generate_invariants {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (inside : RowsWithin n rows) :
    (generate formula rows).within n ∧ (generate formula rows).triangular := by
  have valid := JointFeedback.generate_invariants formula rows inside
  exact iterate_invariants formula (n+1) _ valid.1 valid.2

theorem generate_holds {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (inside : RowsWithin n rows) (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (generate formula rows).holds assignment) =
      (CNFFormula.eval formula assignment && holds rows assignment) := by
  have valid := JointFeedback.generate_invariants formula rows inside
  exact (iterate_holds formula (n+1) _ valid.1 valid.2 assignment).trans
    (JointFeedback.generate_holds formula rows assignment)

theorem generate_settled {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (inside : RowsWithin n rows) (i : Fin n) :
    refine formula (generate formula rows) i = generate formula rows := by
  have valid := JointFeedback.generate_invariants formula rows inside
  apply (scan_fixed formula (List.finRange n) _).mp
    (iterate_settled formula (n+1) _ valid.1 valid.2 (by
      cases JointFeedback.generate formula rows <;> simp [Propagation.remaining]))
  simp

def decideRows {n : Nat} (formula : CNFFormula n) (rows : List Row) : Bool :=
  JointFeedback.decideResult formula (generate formula rows)

theorem decideRows_correct {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (inside : RowsWithin n rows) :
    decideRows formula rows = true ↔ ∃ assignment : Assignment n,
      CNFFormula.eval formula (extendAssignment assignment) = true ∧ holds rows (extendAssignment assignment) = true := by
  have valid := generate_invariants formula rows inside
  rw [decideRows, JointFeedback.decideResult_correct formula _ valid.1 valid.2]
  simp only [generate_holds formula rows inside, Bool.and_eq_true]

theorem decideRows_eq_original {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (inside : RowsWithin n rows) : decideRows formula rows = JointFeedback.decideRows formula rows := by
  apply Bool.eq_iff_iff.mpr
  rw [decideRows_correct formula rows inside, JointFeedback.decideRows_correct formula rows inside]

def decideData (data : List (List Row)) : Bool :=
  let image := AtomImage.generate (Atoms.table data)
  let formula := Subsumption.reduce (Atoms.compile data)
  decideRows formula image.kernel

theorem decideData_eq_original (n : Nat) (data : List (List Row))
    (valid : ∀ row ∈ data.flatten, Table.RowValid n row) :
    decideData data = JointFeedback.decideData data :=
  decideRows_eq_original _ _ (AtomSource.kernel_within n data valid)

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  match Atoms.generate formula with
  | .contradiction => false
  | .basis basis => decideData (Atoms.data basis formula)

theorem decideFormula_eq_original {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = JointFeedback.decideFormula formula := by
  cases generated : Atoms.generate formula with
  | contradiction => simp [decideFormula, JointFeedback.decideFormula, generated]
  | basis basis =>
      simp only [decideFormula, JointFeedback.decideFormula, generated]
      exact decideData_eq_original n _ (Atoms.data_valid basis (Atoms.generated_within formula basis generated) formula)

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  rw [decideFormula_eq_original, JointFeedback.decideFormula_correct]

def decideBits (bits : List Bool) : Bool :=
  match Encoding.parse bits with
  | none => false
  | some input => decideFormula input.2

theorem decideBits_eq_original (bits : List Bool) : decideBits bits = Encoding.decideBits bits := by
  rw [← JointFeedback.decideBits_eq_original]
  cases parsed : Encoding.parse bits with
  | none => simp [decideBits, JointFeedback.decideBits, parsed]
  | some input => simp [decideBits, JointFeedback.decideBits, parsed, decideFormula_eq_original]

theorem decideBits_iff_rootVerify (bits : List Bool) :
    decideBits bits = true ↔ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧
      ∃ assignment : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_eq_original, Encoding.decideBits_iff_rootVerify]

theorem decideBits_no (bits : List Bool) :
    decideBits bits = false ↔ ¬ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧ CNFSatisfiable input.2 := by
  rw [decideBits_eq_original, Encoding.decideBits_no]

theorem decideBits_invalid (bits : List Bool) (invalid : Encoding.parse bits = none) : decideBits bits = false := by
  simp [decideBits, invalid]

def jointValue (data : List (List Row)) (target : Nat → Bool) : Bool :=
  let image := AtomImage.generate (Atoms.table data)
  let formula := Subsumption.reduce (Atoms.compile data)
  CNFFormula.eval formula target && (generate formula image.kernel).holds target

theorem jointValue_eq_original (n : Nat) (data : List (List Row))
    (valid : ∀ row ∈ data.flatten, Table.RowValid n row) (target : Nat → Bool) :
    jointValue data target = AtomSource.jointValue data target := by
  rw [jointValue, generate_holds _ _ (AtomSource.kernel_within n data valid), AtomSource.jointValue, Bool.and_comm]

def sourceAction {n : Nat} (formula : CNFFormula n) (basis : List Row) (source : Source n) : Source n :=
  fun assignment =>
    let input := extendAssignment assignment
    if holds basis input && jointValue (Atoms.data basis formula) (Atoms.read (Atoms.data basis formula) input)
    then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : Atoms.generate formula = .basis basis) (source : Source n) :
    zeroProjector formula source = sourceAction formula basis source := by
  rw [AtomSource.original_projector formula basis generated source]
  funext assignment
  simp only [AtomSource.sourceAction, sourceAction,
    jointValue_eq_original n _ (Atoms.data_valid basis (Atoms.generated_within formula basis generated) formula)]

def trialCount {n : Nat} (formula : CNFFormula n) : Nat → Result → Nat
  | 0, _ => 0
  | fuel+1, result =>
      let current := scan formula (List.finRange n) result
      current.2 + trialCount formula fuel current.1

theorem trialCount_bound {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result) :
    trialCount formula fuel result ≤ fuel*n := by
  induction fuel generalizing result with
  | zero => simp [trialCount]
  | succ fuel ih =>
      have trials := scan_trials formula (List.finRange n) result
      simp only [List.length_finRange] at trials
      have tail := ih (scan formula (List.finRange n) result).1
      simp only [trialCount]
      nlinarith

theorem generated_trialCount {n : Nat} (formula : CNFFormula n) (rows : List Row) :
    trialCount formula (n+1) (JointFeedback.generate formula rows) ≤ n*(n+1) := by
  simpa only [Nat.mul_comm] using trialCount_bound formula (n+1) (JointFeedback.generate formula rows)

end SaturationMonoid.ComplexityProjection.SATSource.Affine.BranchImage
