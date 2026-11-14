import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Basis
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Extract

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine

open InterferenceProgram

def RowsWithin (n : Nat) (rows : List Row) : Prop :=
  ∀ row ∈ rows, Parity.Within n row.vars

theorem Row.normalize_within (n : Nat) (row : Row) (inside : Parity.Within n row.vars) :
    Parity.Within n row.normalize.vars :=
  Parity.merge_within row.vars [] n inside (by simp [Parity.Within])

theorem Row.xor_within (n : Nat) (left right : Row)
    (leftInside : Parity.Within n left.vars) (rightInside : Parity.Within n right.vars) :
    Parity.Within n (left.xor right).vars :=
  Parity.merge_within left.vars right.vars n leftInside rightInside

theorem reduceWith_within (n : Nat) (basis : List Row) (inside : RowsWithin n basis)
    (row : Row) (rowInside : Parity.Within n row.vars) :
    Parity.Within n (reduceWith basis row).vars := by
  induction basis generalizing row with
  | nil => exact rowInside
  | cons pivot rest ih =>
      have first := inside pivot (by simp)
      have tail : RowsWithin n rest := fun other member => inside other (by simp [member])
      simp only [reduceWith, List.foldl_cons]
      apply ih tail
      cases shape : pivot.vars with
      | nil => exact rowInside
      | cons p vars =>
          simp only
          split
          · exact Row.xor_within n row pivot rowInside first
          · exact rowInside

def Result.within (n : Nat) : Result → Prop
  | .contradiction => True
  | .basis rows => RowsWithin n rows

theorem Result.insert_within (n : Nat) (result : Result) (inside : result.within n)
    (row : Row) (rowInside : Parity.Within n row.vars) : (result.insert row).within n := by
  cases result with
  | contradiction => trivial
  | basis basis =>
      have reducedInside := reduceWith_within n basis inside row.normalize
        (Row.normalize_within n row rowInside)
      cases reduced : reduceWith basis row.normalize with
      | mk vars rhs =>
          rw [reduced] at reducedInside
          cases vars with
          | nil => cases rhs <;> simp only [insert, reduced, Result.within] <;> trivial
          | cons p vars =>
              simp only [insert, reduced, Result.within]
              intro other member
              rcases List.mem_append.mp member with prior | last
              · exact inside other prior
              · simpa only [List.mem_singleton.mp last] using reducedInside

theorem eliminateFrom_within (n : Nat) (result : Result) (inside : result.within n)
    (rows : List Row) (rowsInside : RowsWithin n rows) : (eliminateFrom result rows).within n := by
  induction rows generalizing result with
  | nil => exact inside
  | cons row rest ih =>
      exact ih _ (Result.insert_within n result inside row (rowsInside row (by simp)))
        (fun other member => rowsInside other (by simp [member]))

theorem eliminate_within (n : Nat) (rows : List Row) (inside : RowsWithin n rows) :
    (eliminate rows).within n :=
  eliminateFrom_within n (.basis []) (by simp [Result.within, RowsWithin]) rows inside

def pivots (basis : List Row) : List Nat := basis.filterMap (fun row => row.vars.head?)

def freeIndices (n : Nat) (basis : List Row) : List Nat :=
  let occupied := pivots basis
  (List.range n).filter (fun i => decide (i ∉ occupied))

theorem mem_pivots (basis : List Row) (p : Nat) :
    p ∈ pivots basis ↔ ∃ row ∈ basis, row.vars.head? = some p := by
  simp [pivots]

theorem head_mem (row : Row) (p : Nat) (head : row.vars.head? = some p) : p ∈ row.vars := by
  cases shape : row.vars with
  | nil => simp [shape] at head
  | cons q rest =>
      have same : q = p := by simpa only [shape, List.head?_cons, Option.some.injEq] using head
      simp [same]

theorem pivots_within (n : Nat) (basis : List Row) (inside : RowsWithin n basis) :
    ∀ p ∈ pivots basis, p < n := by
  intro p member
  obtain ⟨row, rowMember, head⟩ := (mem_pivots basis p).mp member
  exact inside row rowMember p (head_mem row p head)

theorem pivots_length (basis : List Row) (triangular : Triangular basis) :
    (pivots basis).length = basis.length := by
  induction basis with
  | nil => rfl
  | cons row rest ih =>
      have nonempty := triangular.2.1 row (by simp)
      have tail := ih (triangular_tail row rest triangular)
      cases shape : row.vars with
      | nil => exact False.elim (nonempty shape)
      | cons p vars => simp only [pivots, List.filterMap_cons, shape, List.head?_cons,
          List.length_cons]; exact congrArg Nat.succ tail

theorem pivots_nodup (basis : List Row) (triangular : Triangular basis) :
    (pivots basis).Nodup := by
  induction basis with
  | nil => simp [pivots]
  | cons row rest ih =>
      have nonempty := triangular.2.1 row (by simp)
      have tail := ih (triangular_tail row rest triangular)
      have later := (List.pairwise_cons.mp triangular.2.2).1
      cases shape : row.vars with
      | nil => exact False.elim (nonempty shape)
      | cons p vars =>
          simp only [pivots, List.filterMap_cons, shape, List.head?_cons]
          change (p :: pivots rest).Nodup
          refine List.nodup_cons.mpr ⟨?_, tail⟩
          intro member
          obtain ⟨other, otherMember, head⟩ := (mem_pivots rest p).mp member
          exact later other otherMember p (by simp [shape]) (head_mem other p head)

theorem mem_freeIndices (n : Nat) (basis : List Row) (i : Nat) :
    i ∈ freeIndices n basis ↔ i < n ∧ i ∉ pivots basis := by
  simp [freeIndices]

theorem freeIndices_nodup (n : Nat) (basis : List Row) : (freeIndices n basis).Nodup :=
  (List.nodup_range (n := n)).filter _

theorem freeIndices_within (n : Nat) (basis : List Row) :
    ∀ i ∈ freeIndices n basis, i < n :=
  fun i member => ((mem_freeIndices n basis i).mp member).1

theorem freeIndices_get_lt (n : Nat) (basis : List Row) (i : Fin (freeIndices n basis).length) :
    (freeIndices n basis).get i < n :=
  freeIndices_within n basis _ (List.get_mem _ i)

def freeAddress (n : Nat) (basis : List Row) (i : Nat) (member : i ∈ freeIndices n basis) :
    Fin (freeIndices n basis).length :=
  ⟨(freeIndices n basis).idxOf i, List.idxOf_lt_length_of_mem member⟩

theorem free_get_address (n : Nat) (basis : List Row) (i : Nat)
    (member : i ∈ freeIndices n basis) :
    (freeIndices n basis).get (freeAddress n basis i member) = i := List.idxOf_get _

theorem free_idxOf_get (n : Nat) (basis : List Row) (i : Fin (freeIndices n basis).length) :
    (freeIndices n basis).idxOf ((freeIndices n basis).get i) = i.val :=
  List.get_idxOf (freeIndices_nodup n basis) i

theorem free_address_get (n : Nat) (basis : List Row) (i : Fin (freeIndices n basis).length) :
    freeAddress n basis ((freeIndices n basis).get i) (List.get_mem _ i) = i := by
  apply Fin.ext
  exact free_idxOf_get n basis i

def freeVariable (n : Nat) (basis : List Row) (i : Fin (freeIndices n basis).length) : Fin n :=
  ⟨(freeIndices n basis).get i, freeIndices_get_lt n basis i⟩

theorem freeIndices_dimension (n : Nat) (basis : List Row) (triangular : Triangular basis)
    (inside : RowsWithin n basis) : (freeIndices n basis).length + basis.length = n := by
  have permutation : ((List.range n).filter (fun p => decide (p ∈ pivots basis))).Perm (pivots basis) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_range (n := n)).filter _) (pivots_nodup basis triangular)).mpr
    intro p
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨And.right, fun member => ⟨pivots_within n basis inside p member, member⟩⟩
  have partition := List.length_eq_length_filter_add (l := List.range n)
    (fun p => decide (p ∈ pivots basis))
  have complement : (List.range n).filter (fun p => !decide (p ∈ pivots basis)) = freeIndices n basis := by
    simp [freeIndices]
  rw [List.length_range, permutation.length_eq, complement, pivots_length basis triangular] at partition
  omega

theorem basis_length_le (n : Nat) (basis : List Row) (triangular : Triangular basis)
    (inside : RowsWithin n basis) : basis.length ≤ n := by
  have dimension := freeIndices_dimension n basis triangular inside
  omega

theorem extract_rowsWithin {n : Nat} (formula : CNFFormula n) : RowsWithin n (Extract.extract formula) :=
  fun row member => (Extract.extract_wellFormed formula row member).2.2

theorem extracted_basis_within {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : eliminate (Extract.extract formula) = .basis basis) : RowsWithin n basis := by
  have bounded := eliminate_within n (Extract.extract formula) (extract_rowsWithin formula)
  simpa only [generated, Result.within] using bounded

theorem extracted_basis_dimension {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : eliminate (Extract.extract formula) = .basis basis) :
    (freeIndices n basis).length + basis.length = n := by
  have triangular := eliminate_triangular (Extract.extract formula)
  rw [generated] at triangular
  exact freeIndices_dimension n basis triangular (extracted_basis_within formula basis generated)

/-- Visited list cells in the membership test used by the free-index filter. -/
def pivotMemberVisits (i : Nat) : List Nat → Nat
  | [] => 1
  | p :: rest => if i = p then 1 else pivotMemberVisits i rest + 1

theorem pivotMemberVisits_bound (i : Nat) (occupied : List Nat) :
    pivotMemberVisits i occupied ≤ occupied.length + 1 := by
  induction occupied with
  | nil => simp [pivotMemberVisits]
  | cons p rest ih =>
      simp only [pivotMemberVisits, List.length_cons]
      split <;> omega

def filterVisits (occupied : List Nat) : List Nat → Nat
  | [] => 1
  | i :: rest => pivotMemberVisits i occupied + filterVisits occupied rest + 1

theorem filterVisits_bound (occupied candidates : List Nat) :
    filterVisits occupied candidates ≤ candidates.length * (occupied.length + 2) + 1 := by
  induction candidates with
  | nil => simp [filterVisits]
  | cons i rest ih =>
      have head := pivotMemberVisits_bound i occupied
      simp only [filterVisits, List.length_cons]
      nlinarith

/-- Head extraction is shared once. This ledger counts source cells, not address bit operations. -/
def freeIndexVisits (n : Nat) (basis : List Row) : Nat :=
  basis.length + 1 + filterVisits (pivots basis) (List.range n)

theorem freeIndexVisits_bound (n : Nat) (basis : List Row) (triangular : Triangular basis) :
    freeIndexVisits n basis ≤ basis.length + 2 + n * (basis.length + 2) := by
  have filtering := filterVisits_bound (pivots basis) (List.range n)
  simp only [List.length_range, pivots_length basis triangular] at filtering
  unfold freeIndexVisits
  omega

theorem bounded_freeIndexVisits (n : Nat) (basis : List Row) (triangular : Triangular basis)
    (inside : RowsWithin n basis) : freeIndexVisits n basis ≤ (n + 1) * (n + 2) := by
  have visits := freeIndexVisits_bound n basis triangular
  have size := basis_length_le n basis triangular inside
  nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.Affine
