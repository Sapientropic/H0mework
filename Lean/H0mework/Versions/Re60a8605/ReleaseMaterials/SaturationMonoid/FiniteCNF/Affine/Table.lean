import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Indices
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Gates
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Lift

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.Table

open InterferenceProgram

def seedRow (free : List Nat) (i : Nat) : Row :=
  if i ∈ free then ⟨[free.idxOf i], false⟩ else Gates.zeroRow

def seed (n : Nat) (basis : List Row) : Array Row :=
  let free := freeIndices n basis
  Array.ofFn (fun i : Fin n => seedRow free i.val)

@[simp] theorem seed_size (n : Nat) (basis : List Row) : (seed n basis).size = n := by simp [seed]

theorem coordinate_getD (table : Array Row) (environment : Nat → Bool) (i : Nat) :
    Gates.coordinate table environment i = Gates.value (table.getD i Gates.zeroRow) environment := by
  simp [Gates.coordinate, Array.getD_eq_getD_getElem?]

theorem value_xor (left right : Row) (environment : Nat → Bool) :
    Gates.value (left.xor right) environment =
      (Gates.value left environment ^^ Gates.value right environment) := by
  change ((left.rhs ^^ right.rhs) ^^ (left.xor right).eval environment) =
    ((left.rhs ^^ left.eval environment) ^^ (right.rhs ^^ right.eval environment))
  rw [Row.xor_eval]
  cases left.rhs <;> cases right.rhs <;> cases left.eval environment <;>
    cases right.eval environment <;> rfl

def combine (table : Array Row) : List Nat → Row → Row
  | [], initial => initial
  | i :: rest, initial => combine table rest (initial.xor (table.getD i Gates.zeroRow))

theorem combine_value (table : Array Row) (terms : List Nat) (initial : Row)
    (environment : Nat → Bool) :
    Gates.value (combine table terms initial) environment =
      (Gates.value initial environment ^^ Parity.eval (Gates.coordinate table environment) terms) := by
  induction terms generalizing initial with
  | nil => simp [combine, Parity.eval]
  | cons i rest ih =>
      rw [combine, ih, value_xor, ← coordinate_getD]
      simp only [Parity.eval, Bool.xor_assoc]

/-- No assignment or function closure is stored: the pivot receives a finite XOR row. -/
def bind (row : Row) (table : Array Row) : Array Row :=
  match row.vars with
  | [] => table
  | p :: tail => table.setIfInBounds p (combine table tail ⟨[], row.rhs⟩)

@[simp] theorem bind_size (row : Row) (table : Array Row) : (bind row table).size = table.size := by
  unfold bind
  split <;> simp

theorem coordinate_set (table : Array Row) (environment : Nat → Bool) (p : Nat)
    (expression : Row) (inside : p < table.size) :
    Gates.coordinate (table.setIfInBounds p expression) environment =
      Function.update (Gates.coordinate table environment) p (Gates.value expression environment) := by
  funext i
  by_cases same : i = p
  · subst i
    simp [coordinate_getD, Array.getD_eq_getD_getElem?, inside]
  · simp [coordinate_getD, Array.getD_eq_getD_getElem?, same, Ne.symm same]

theorem bind_coordinate (row : Row) (table : Array Row) (environment : Nat → Bool)
    (inside : Parity.Within table.size row.vars) :
    Gates.coordinate (bind row table) environment = row.bind (Gates.coordinate table environment) := by
  cases shape : row.vars with
  | nil => simp [bind, Row.bind, shape]
  | cons p tail =>
      have pivotBound := inside p (by simp [shape])
      simp only [bind, Row.bind, shape]
      rw [coordinate_set table environment p _ pivotBound, combine_value]
      simp only [Gates.value, Row.eval, Parity.eval, Bool.xor_false]

def backSubstitute (basis : List Row) (table : Array Row) : Array Row := basis.foldr bind table

@[simp] theorem backSubstitute_size (basis : List Row) (table : Array Row) :
    (backSubstitute basis table).size = table.size := by
  induction basis with
  | nil => rfl
  | cons row rest ih => simpa [backSubstitute, List.foldr_cons] using ih

theorem backSubstitute_coordinate (basis : List Row) (table : Array Row) (environment : Nat → Bool)
    (inside : RowsWithin table.size basis) :
    Gates.coordinate (backSubstitute basis table) environment =
      fill basis (Gates.coordinate table environment) := by
  induction basis with
  | nil => rfl
  | cons row rest ih =>
      have tail := ih (fun other member => inside other (by simp [member]))
      have head : Parity.Within (backSubstitute rest table).size row.vars := by
        simpa only [backSubstitute_size] using inside row (by simp)
      change Gates.coordinate (bind row (backSubstitute rest table)) environment =
        row.bind (fill rest (Gates.coordinate table environment))
      rw [bind_coordinate row _ environment head, tail]

theorem seed_coordinate (n : Nat) (basis : List Row) (environment : Nat → Bool) :
    Gates.coordinate (seed n basis) environment = freeSeed n basis environment := by
  funext i
  by_cases inside : i < n
  · by_cases member : i ∈ freeIndices n basis <;>
      simp [coordinate_getD, seed, Array.getD_eq_getD_getElem?,
        inside, seedRow, member, Gates.value, Row.eval, Parity.eval, Gates.zeroRow, freeSeed]
  · have absent : i ∉ freeIndices n basis := by
      intro member
      exact inside ((mem_freeIndices n basis i).mp member).1
    simp [coordinate_getD, seed, Array.getD_eq_getD_getElem?,
      inside, Gates.value, Row.eval, Parity.eval, Gates.zeroRow, freeSeed, absent]

def coordinates (n : Nat) (basis : List Row) : Array Row := backSubstitute basis (seed n basis)

@[simp] theorem coordinates_size (n : Nat) (basis : List Row) : (coordinates n basis).size = n := by
  simp [coordinates]

theorem coordinates_value (n : Nat) (basis : List Row) (inside : RowsWithin n basis)
    (environment : Nat → Bool) :
    Gates.coordinate (coordinates n basis) environment = fill basis (freeSeed n basis environment) := by
  rw [coordinates, backSubstitute_coordinate basis _ environment (by simpa using inside), seed_coordinate]

def RowValid (width : Nat) (row : Row) : Prop := row.vars.Nodup ∧ Parity.Within width row.vars

def Valid (width : Nat) (table : Array Row) : Prop := ∀ row ∈ table.toList, RowValid width row

theorem zero_valid (width : Nat) : RowValid width Gates.zeroRow := by
  simp [RowValid, Gates.zeroRow, Parity.Within]

theorem seedRow_valid (free : List Nat) (i : Nat) : RowValid free.length (seedRow free i) := by
  unfold seedRow
  split
  · rename_i member
    refine ⟨by simp, ?_⟩
    intro j hit
    have same : j = free.idxOf i := by simpa only [List.mem_singleton] using hit
    subst j
    exact List.idxOf_lt_length_of_mem member
  · exact zero_valid _

theorem seed_valid (n : Nat) (basis : List Row) : Valid (freeIndices n basis).length (seed n basis) := by
  intro row member
  simp only [seed, Array.toList_ofFn, List.mem_ofFn] at member
  obtain ⟨i, rfl⟩ := member
  exact seedRow_valid _ _

theorem read_valid (width : Nat) (table : Array Row) (valid : Valid width table) (i : Nat) :
    RowValid width (table.getD i Gates.zeroRow) := by
  by_cases inside : i < table.size
  · simpa [Array.getD, inside] using valid table[i] (Array.getElem_mem_toList inside)
  · simpa [Array.getD, inside] using zero_valid width

theorem xor_valid (width : Nat) (left right : Row) (leftValid : RowValid width left)
    (rightValid : RowValid width right) : RowValid width (left.xor right) :=
  ⟨Row.xor_nodup left right rightValid.1, Row.xor_within width left right leftValid.2 rightValid.2⟩

theorem combine_valid (width : Nat) (table : Array Row) (valid : Valid width table)
    (terms : List Nat) (initial : Row) (initialValid : RowValid width initial) :
    RowValid width (combine table terms initial) := by
  induction terms generalizing initial with
  | nil => exact initialValid
  | cons i rest ih => exact ih _ (xor_valid width initial _ initialValid (read_valid width table valid i))

theorem bind_valid (width : Nat) (row : Row) (table : Array Row) (valid : Valid width table) :
    Valid width (bind row table) := by
  unfold bind
  split
  · exact valid
  · rename_i p tail shape
    have combined : RowValid width (combine table tail ⟨[], row.rhs⟩) :=
      combine_valid width table valid tail _ (by simp [RowValid, Parity.Within])
    intro other member
    have inArray : other ∈ table.setIfInBounds p (combine table tail ⟨[], row.rhs⟩) := by
      exact Array.mem_def.mpr member
    rcases Array.mem_or_eq_of_mem_setIfInBounds inArray with old | last
    · exact valid other (Array.mem_def.mp old)
    · simpa only [last] using combined

theorem backSubstitute_valid (width : Nat) (basis : List Row) (table : Array Row)
    (valid : Valid width table) : Valid width (backSubstitute basis table) := by
  induction basis with
  | nil => exact valid
  | cons row rest ih => exact bind_valid width row _ ih

theorem coordinates_valid (n : Nat) (basis : List Row) :
    Valid (freeIndices n basis).length (coordinates n basis) :=
  backSubstitute_valid _ basis _ (seed_valid n basis)

theorem coordinates_bounded (n : Nat) (basis : List Row) :
    Gates.Bounded (freeIndices n basis).length (coordinates n basis) :=
  fun row member => (coordinates_valid n basis row member).2

theorem row_length_le (width : Nat) (row : Row) (valid : RowValid width row) : row.vars.length ≤ width := by
  have included : row.vars ⊆ List.range width := fun i member => List.mem_range.mpr (valid.2 i member)
  have lengthBound := (List.subperm_of_subset valid.1 included).length_le
  simpa using lengthBound

theorem rowTerms_bound (width : Nat) (table : Array Row) (valid : Valid width table) :
    Gates.rowTerms table.toList ≤ table.size * width := by
  suffices ∀ rows : List Row, (∀ row ∈ rows, RowValid width row) →
      Gates.rowTerms rows ≤ rows.length * width by
    simpa using this table.toList valid
  intro rows validRows
  induction rows with
  | nil => simp [Gates.rowTerms]
  | cons row rest ih =>
      have head := row_length_le width row (validRows row (by simp))
      have tail := ih (fun other member => validRows other (by simp [member]))
      simp only [Gates.rowTerms, List.map_cons, List.sum_cons, List.length_cons]
      simp only [Gates.rowTerms] at tail
      nlinarith

theorem coordinates_storage (n : Nat) (basis : List Row) :
    Gates.rowTerms (coordinates n basis).toList ≤ n * (freeIndices n basis).length := by
  simpa only [coordinates_size] using rowTerms_bound _ _ (coordinates_valid n basis)

theorem generated_coordinates_value {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : eliminate (Extract.extract formula) = .basis basis) (environment : Nat → Bool) :
    Gates.coordinate (coordinates n basis) environment = fill basis (freeSeed n basis environment) :=
  coordinates_value n basis (extracted_basis_within formula basis generated) environment

/-- Source-cell visits of the membership/erase work in the existing finite XOR implementation. -/
def toggleVisits (i : Nat) (terms : List Nat) : Nat :=
  pivotMemberVisits i terms + (if i ∈ terms then pivotMemberVisits i terms else 0) + 2

theorem toggleVisits_bound (width i : Nat) (terms : List Nat) (nodup : terms.Nodup)
    (inside : Parity.Within width terms) : toggleVisits i terms ≤ 2 * width + 4 := by
  have lengthBound := row_length_le width (Row.mk terms false) ⟨nodup, inside⟩
  change terms.length ≤ width at lengthBound
  have scan := pivotMemberVisits_bound i terms
  simp only [toggleVisits]
  split <;> omega

def mergeVisits : List Nat → List Nat → Nat
  | [], _ => 1
  | i :: rest, right => toggleVisits i right + mergeVisits rest (Parity.toggle i right) + 1

theorem mergeVisits_bound (width : Nat) (left right : List Nat)
    (leftInside : Parity.Within width left) (rightNodup : right.Nodup)
    (rightInside : Parity.Within width right) :
    mergeVisits left right ≤ left.length * (2 * width + 5) + 1 := by
  induction left generalizing right with
  | nil => simp [mergeVisits]
  | cons i rest ih =>
      have head := leftInside i (by simp)
      have tailInside : Parity.Within width rest := fun j member => leftInside j (by simp [member])
      have nextNodup := Parity.toggle_nodup right i rightNodup
      have nextInside := Parity.toggle_within right width i rightInside head
      have next := ih (Parity.toggle i right) tailInside nextNodup nextInside
      have first := toggleVisits_bound width i right rightNodup rightInside
      simp only [mergeVisits, List.length_cons]
      nlinarith

def combineVisits (table : Array Row) : List Nat → Row → Nat
  | [], _ => 1
  | i :: rest, initial =>
      let other := table.getD i Gates.zeroRow
      mergeVisits initial.vars other.vars + combineVisits table rest (initial.xor other) + 3

theorem combineVisits_bound (width : Nat) (table : Array Row) (valid : Valid width table)
    (terms : List Nat) (initial : Row) (initialValid : RowValid width initial) :
    combineVisits table terms initial ≤ terms.length * (width * (2 * width + 5) + 4) + 1 := by
  induction terms generalizing initial with
  | nil => simp [combineVisits]
  | cons i rest ih =>
      have other := read_valid width table valid i
      have first := mergeVisits_bound width initial.vars (table.getD i Gates.zeroRow).vars
        initialValid.2 other.1 other.2
      have currentLength := row_length_le width initial initialValid
      have next := ih _ (xor_valid width initial _ initialValid other)
      simp only [combineVisits, List.length_cons]
      nlinarith

def bindVisits (row : Row) (table : Array Row) : Nat :=
  match row.vars with
  | [] => 1
  | _ :: tail => combineVisits table tail ⟨[], row.rhs⟩ + table.size + 2

theorem bindVisits_bound (width : Nat) (row : Row) (table : Array Row) (valid : Valid width table) :
    bindVisits row table ≤ row.vars.length * (width * (2 * width + 5) + 4) + table.size + 3 := by
  cases shape : row.vars with
  | nil => simp [bindVisits, shape]
  | cons p tail =>
      have visits := combineVisits_bound width table valid tail (Row.mk [] row.rhs)
        (by simp [RowValid, Parity.Within])
      simp only [bindVisits, shape, List.length_cons]
      nlinarith

def backSubstituteVisits : List Row → Array Row → Nat
  | [], _ => 1
  | row :: rest, table =>
      backSubstituteVisits rest table + bindVisits row (backSubstitute rest table) + 1

theorem backSubstituteVisits_bound (width : Nat) (basis : List Row) (table : Array Row)
    (valid : Valid width table) :
    backSubstituteVisits basis table ≤
      Gates.rowTerms basis * (width * (2 * width + 5) + 4) + basis.length * (table.size + 4) + 1 := by
  induction basis with
  | nil => simp [backSubstituteVisits, Gates.rowTerms]
  | cons row rest ih =>
      have first := bindVisits_bound width row (backSubstitute rest table)
        (backSubstitute_valid width rest table valid)
      simp only [backSubstitute_size] at first
      simp only [backSubstituteVisits, Gates.rowTerms, List.map_cons, List.sum_cons, List.length_cons]
      simp only [Gates.rowTerms] at ih
      nlinarith

/-- This ledger includes source-head/filter cells, row XOR scans and conservative table-write cells.
It does not replace the separate classical implementation of address-bit and allocation operations. -/
def coordinatesVisits (n : Nat) (basis : List Row) : Nat :=
  freeIndexVisits n basis + n * (2 * (freeIndices n basis).length + 5) + 1 +
    backSubstituteVisits basis (seed n basis)

theorem coordinatesVisits_bound (n : Nat) (basis : List Row) :
    coordinatesVisits n basis ≤
      freeIndexVisits n basis + n * (2 * (freeIndices n basis).length + 5) + 2 +
      Gates.rowTerms basis * ((freeIndices n basis).length * (2 * (freeIndices n basis).length + 5) + 4) +
      basis.length * (n + 4) := by
  have back := backSubstituteVisits_bound _ basis (seed n basis) (seed_valid n basis)
  simp only [seed_size] at back
  unfold coordinatesVisits
  omega

theorem freeWidth_le (n : Nat) (basis : List Row) : (freeIndices n basis).length ≤ n := by
  simpa only [freeIndices, List.length_range] using
    List.length_filter_le (fun i => decide (i ∉ pivots basis)) (List.range n)

theorem coordinates_storage_quadratic (n : Nat) (basis : List Row) :
    Gates.rowTerms (coordinates n basis).toList ≤ n ^ 2 := by
  have stored := coordinates_storage n basis
  have width := freeWidth_le n basis
  nlinarith

theorem coordinatesVisits_polynomial (n : Nat) (basis : List Row) (triangular : Triangular basis)
    (inside : RowsWithin n basis) : coordinatesVisits n basis ≤ 10 * (n + 1) ^ 4 := by
  have bounded := coordinatesVisits_bound n basis
  have indices := bounded_freeIndexVisits n basis triangular inside
  have width := freeWidth_le n basis
  have rank := basis_length_le n basis triangular inside
  have rows : Gates.rowTerms basis ≤ basis.length * n := by
    simpa using rowTerms_bound n basis.toArray
      (fun row member => ⟨triangular.1 row (by simpa using member), inside row (by simpa using member)⟩)
  have rowBound : Gates.rowTerms basis ≤ n ^ 2 := by nlinarith
  have perRow : (freeIndices n basis).length * (2 * (freeIndices n basis).length + 5) + 4 ≤
      n * (2 * n + 5) + 4 := by nlinarith
  have total : coordinatesVisits n basis ≤ (n + 1) * (n + 2) + n * (2 * n + 5) + 2 +
      n ^ 2 * (n * (2 * n + 5) + 4) + n * (n + 4) := by
    refine bounded.trans ?_
    gcongr
  nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.Affine.Table
