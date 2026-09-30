import H0mework.Chemistry.LAlanineRefinementDensity.SharedContractions

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceLocalDot

open SourceFiniteData SourceGaussianModel SourceJetIncidence SourceLaplaceSharedTables
open scoped BigOperators

noncomputable section

def dot (left right : Array Nat) : Nat := (left.toList.zipWith (· * ·) right.toList).sum

theorem dot_eq_sum (left right : Array Nat) (hl : left.size = 98) (hr : right.size = 98) :
    dot left right = ∑ j : Basis, left[j.val]! * right[j.val]! := by
  unfold dot
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_zipWith, Array.length_toList, hl, hr, min_self, List.length_ofFn]
  · intro i hi hj
    have inside : i < 98 := by
      simpa only [List.length_zipWith, Array.length_toList, hl, hr, min_self] using hi
    have hleft : i < left.size := by simpa only [hl] using inside
    have hright : i < right.size := by simpa only [hr] using inside
    simp only [List.getElem_zipWith, Array.getElem_toList, List.getElem_ofFn,
      getElem!_pos, hleft, hright]

def matrixRow (i : Basis) : Array Nat := matrixRows[i.val]!
def orbitalRow (d : JetIndex) : Array Nat := orbitalRows[d.val]!

theorem matrixRow_size (i : Basis) : (matrixRow i).size = 98 := by
  fin_cases i <;> rfl

theorem orbitalRow_size (d : JetIndex) : (orbitalRow d).size = 98 := by
  fin_cases d <;> rfl

def bilinear (left right : JetIndex) (i : Basis) : Nat :=
  orbital left i * dot (matrixRow i) (orbitalRow right)

theorem bilinear_eq_shared (left right : MultiIndex) (i : Basis) :
    bilinear (sourceJetIndex left) (sourceJetIndex right) i =
      SourceLaplaceSharedContractions.rowBilinear left right i := by
  rw [bilinear, dot_eq_sum _ _ (matrixRow_size i) (orbitalRow_size _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [matrixRow, orbitalRow, matrix, SourceLaplaceSharedTables.orbital]
  ring

def fourth : SourceLaplaceRowData.Direction → Basis → Nat := ![
  fun i => bilinear 20 0 i + 4 * bilinear 10 1 i + 6 * bilinear 4 4 i + 4 * bilinear 1 10 i + bilinear 0 20 i,
  fun i => bilinear 23 0 i + 2 * bilinear 11 2 i + bilinear 4 7 i + 2 * bilinear 13 1 i +
    4 * bilinear 5 5 i + 2 * bilinear 1 13 i + bilinear 7 4 i + 2 * bilinear 2 11 i + bilinear 0 23 i,
  fun i => bilinear 25 0 i + 2 * bilinear 12 3 i + bilinear 4 9 i + 2 * bilinear 15 1 i +
    4 * bilinear 6 6 i + 2 * bilinear 1 15 i + bilinear 9 4 i + 2 * bilinear 3 12 i + bilinear 0 25 i,
  fun i => bilinear 30 0 i + 4 * bilinear 16 2 i + 6 * bilinear 7 7 i + 4 * bilinear 2 16 i + bilinear 0 30 i,
  fun i => bilinear 32 0 i + 2 * bilinear 17 3 i + bilinear 7 9 i + 2 * bilinear 18 2 i +
    4 * bilinear 8 8 i + 2 * bilinear 2 18 i + bilinear 9 7 i + 2 * bilinear 3 17 i + bilinear 0 32 i,
  fun i => bilinear 34 0 i + 4 * bilinear 19 3 i + 6 * bilinear 9 9 i + 4 * bilinear 3 19 i + bilinear 0 34 i]

attribute [local irreducible] bilinear in
theorem fourth_commutes (direction : SourceLaplaceRowData.Direction) (i : Basis) :
    fourth direction i = SourceLaplaceIntegers.rowFourth
      (SourceLaplaceRowData.innerAxis direction) (SourceLaplaceRowData.outerAxis direction) i := by
  rw [← SourceLaplaceSharedContractions.fourth_commutes]
  simp only [SourceLaplaceSharedContractions.rowFourth, SourceLaplaceSharedContractions.rowSecond,
    ← bilinear_eq_shared]
  unfold fourth
  generalize bilinear = response
  fin_cases direction <;>
    norm_num [SourceLaplaceRowData.innerAxis, SourceLaplaceRowData.outerAxis,
      sourceJetIndex, sourceJetCode, raise, Function.update, Fin.ext_iff] <;> ring_nf <;> rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceLocalDot
