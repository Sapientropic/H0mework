import H0mework.Chemistry.LAlanineContinuousMatrix.IntegerLists

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices

open SourceIntegerGrid

def pointIntervals (values : List ℤ) : List Interval := values.map fun n => (n, n)
def scalarDot (a b : List ℤ) : ℤ := (a.zipWith (· * ·) b).sum
def pointDot (am ar d : List ℤ) : Interval :=
  let c := scalarDot am d
  let r := scalarDot ar (d.map fun n => |n|)
  ((c - r) / denominator, -((-(c + r)) / denominator))

theorem mid_point (n : ℤ) : mid (n, n) = n := by unfold mid; omega
theorem rad_point (n : ℤ) : rad (n, n) = 0 := by simp [rad, mid_point]
theorem productRad_point (a : Interval) (n : ℤ) : productRad a (n, n) = rad a * |n| := by
  simp [productRad, mid_point, rad_point]

theorem centre_point_list (a : List Interval) (d : List ℤ) :
    a.zipWith (fun x y => mid x * mid y) (pointIntervals d) = (a.map mid).zipWith (· * ·) d := by
  induction a generalizing d with
  | nil => cases d <;> rfl
  | cons x xs ih => cases d <;> simp_all [pointIntervals, mid_point]

theorem radius_point_list (a : List Interval) (d : List ℤ) :
    a.zipWith productRad (pointIntervals d) = (a.map rad).zipWith (· * ·) (d.map fun n => |n|) := by
  induction a generalizing d with
  | nil => cases d <;> rfl
  | cons x xs ih => cases d <;> simp_all [pointIntervals, productRad_point]

theorem pointDot_commutes (a : List Interval) (d : List ℤ) :
    pointDot (a.map mid) (a.map rad) d = dotList a (pointIntervals d) := by
  unfold pointDot dotList listCentre listRadius scalarDot
  rw [centre_point_list, radius_point_list]

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices
