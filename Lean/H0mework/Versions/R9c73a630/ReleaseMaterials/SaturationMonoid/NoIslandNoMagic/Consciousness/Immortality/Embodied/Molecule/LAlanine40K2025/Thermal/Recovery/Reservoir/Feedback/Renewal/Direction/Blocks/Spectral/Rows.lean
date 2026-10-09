import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Rows
open scoped Matrix

def dot : List Int → List Int → Int
  | a::as,b::bs => a*b+dot as bs
  | _,_ => 0

theorem dot_ofFn {n : Nat} (a b : Fin n → Int) :
    dot (List.ofFn a) (List.ofFn b) = ∑ i, a i*b i := by
  induction n with
  | zero => simp [dot]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [dot, Fin.sum_univ_succ]
    rw [ih]

def read {n : Nat} (row : List Int) (i : Fin n) : Int := row[i.val]!

theorem ofFn_read {n : Nat} (row : List Int) (length : row.length = n) :
    List.ofFn (read (n := n) row) = row := by
  subst n
  change List.ofFn (fun i : Fin row.length => row[i.val]!) = row
  have entries : (fun i : Fin row.length => row[i.val]!) = (fun i => row[i.val]) := by
    funext i
    exact getElem!_pos row i.val i.isLt
  rw [entries]
  exact List.ofFn_getElem

theorem dot_eq_sum {n : Nat} (a b : List Int) (aLength : a.length = n) (bLength : b.length = n) :
    dot a b = ∑ i : Fin n, read a i * read b i := by
  calc
    _ = dot (List.ofFn (read (n := n) a)) (List.ofFn (read (n := n) b)) := by
      rw [ofFn_read a aLength, ofFn_read b bLength]
    _ = _ := dot_ofFn _ _

def rowAt {n : Nat} (rows : List (List Int)) (i : Fin n) : List Int := rows[i.val]!
def rowMatrix {n : Nat} (rows : List (List Int)) : Matrix (Fin n) (Fin n) Int :=
  fun i j => read (rowAt rows i) j
def columnMatrix {n : Nat} (columns : List (List Int)) : Matrix (Fin n) (Fin n) Int :=
  fun i j => read (rowAt columns j) i

theorem read_map {n : Nat} (rows : List (List Int)) (length : rows.length = n)
    (f : List Int → Int) (i : Fin n) : read (rows.map f) i = f (rowAt rows i) := by
  have bound : i.val < rows.length := length ▸ i.isLt
  simp only [read, rowAt, getElem!_pos, List.getElem_map, List.length_map, bound]

theorem first_matrix {n : Nat} (rows columns first : List (List Int))
    (rowsLength : rows.length = n)
    (rowLengths : ∀ i : Fin n, (rowAt rows i).length = n)
    (columnLengths : ∀ j : Fin n, (rowAt columns j).length = n)
    (exactColumns : ∀ j : Fin n, rowAt first j = rows.map (fun row => dot row (rowAt columns j))) :
    columnMatrix (n := n) first = rowMatrix rows * columnMatrix columns := by
  ext i j
  change read (rowAt first j) i = ∑ k, read (rowAt rows i) k * read (rowAt columns j) k
  rw [exactColumns j, read_map rows rowsLength]
  exact dot_eq_sum _ _ (rowLengths i) (columnLengths j)

theorem second_matrix {n : Nat} (columns first gram : List (List Int))
    (firstLength : first.length = n)
    (columnLengths : ∀ i : Fin n, (rowAt columns i).length = n)
    (firstLengths : ∀ j : Fin n, (rowAt first j).length = n)
    (exactRows : ∀ i : Fin n, rowAt gram i = first.map (dot (rowAt columns i))) :
    rowMatrix (n := n) gram = (columnMatrix columns)ᵀ * columnMatrix first := by
  ext i j
  change read (rowAt gram i) j = ∑ k, read (rowAt columns i) k * read (rowAt first j) k
  rw [exactRows i, read_map first firstLength]
  exact dot_eq_sum _ _ (columnLengths i) (firstLengths j)

def absSum (row : List Int) : Int := (row.map abs).sum

theorem absSum_ofFn {n : Nat} (a : Fin n → Int) :
    absSum (List.ofFn a) = ∑ i, |a i| := by
  induction n with
  | zero => simp [absSum]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [absSum, List.map_cons, List.sum_cons, Fin.sum_univ_succ]
    exact congrArg (fun z => |a 0| + z) (ih (fun i => a i.succ))

theorem absSum_eq_sum {n : Nat} (row : List Int) (length : row.length = n) :
    absSum row = ∑ i : Fin n, |read row i| := by
  calc
    _ = absSum (List.ofFn (read (n := n) row)) := by rw [ofFn_read row length]
    _ = _ := absSum_ofFn _

def margin {n : Nat} (row : List Int) (i : Fin n) : Int := 2*read row i - absSum row

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
