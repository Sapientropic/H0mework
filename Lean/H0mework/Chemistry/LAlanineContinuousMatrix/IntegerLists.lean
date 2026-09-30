import H0mework.Chemistry.LAlanineContinuousMatrix.IntegerGrid

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerGrid

open SourceSignedEvaluator SourceExponential
open scoped BigOperators

theorem point_grid (n : ℤ) : point ((n : ℚ) / scale) = grid (n, n) := by
  have hs : scale ≠ 0 := ne_of_gt scale_positive
  simp only [point, roundDown, roundUp, grid, mul_div_cancel₀ _ hs,
    Int.floor_intCast, Int.ceil_intCast]

def listCentre (a b : List Interval) : ℤ := (a.zipWith (fun x y => mid x * mid y) b).sum
def listRadius (a b : List Interval) : ℤ := (a.zipWith productRad b).sum
def dotList (a b : List Interval) : Interval :=
  ((listCentre a b - listRadius a b) / denominator,
    -((-(listCentre a b + listRadius a b)) / denominator))

theorem zipSum_eq_finSum (f : Interval → Interval → ℤ) (a b : List Interval)
    (n : ℕ) (ha : a.length = n) (hb : b.length = n) :
    (a.zipWith f b).sum = ∑ i : Fin n, f a[i.val]! b[i.val]! := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_zipWith, ha, hb, min_self, List.length_ofFn]
  · intro i hi _
    have inside : i < n := by
      simpa only [List.length_zipWith, ha, hb, min_self] using hi
    have hleft : i < a.length := by simpa only [ha] using inside
    have hright : i < b.length := by simpa only [hb] using inside
    simp only [List.getElem_zipWith, List.getElem_ofFn,
      getElem!_pos, hleft, hright]

theorem dotList_eq_dot (a b : List Interval) (n : ℕ)
    (ha : a.length = n) (hb : b.length = n) :
    dotList a b = dot (fun i : Fin n => a[i.val]!) (fun i : Fin n => b[i.val]!) := by
  unfold dotList dot listCentre listRadius centre radiusSum
  rw [zipSum_eq_finSum _ a b n ha hb, zipSum_eq_finSum _ a b n ha hb]

theorem dotList_commutes (a b : List Interval) (n : ℕ)
    (ha : a.length = n) (hb : b.length = n) :
    grid (dotList a b) = dotPair (fun i : Fin n => grid a[i.val]!)
      (fun i : Fin n => grid b[i.val]!) := by
  rw [dotList_eq_dot a b n ha hb]
  exact dot_commutes _ _

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerGrid
