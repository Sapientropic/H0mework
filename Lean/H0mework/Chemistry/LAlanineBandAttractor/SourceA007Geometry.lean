import H0mework.Chemistry.LAlanineBandAttractor.SourceA007PointData
import H0mework.Chemistry.LAlanineBandAttractor.SourceA007HullData

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAttractor.Atom007
open SourceGaussianModel SourceSignedEvaluator SourceIntegerGrid
open Metric
open scoped NNReal
noncomputable section

def centreRat (i : Fin 3) : ℚ := (Point.rawCenter[i.val]! : ℚ) / SourceExponential.scale
def centre : SourceGaussianModel.Point := fun i => (centreRat i : ℝ)
def radiusRat : ℚ := 1/1048576
def radius : ℝ := (radiusRat : ℝ)
def alpha : ℝ := 1/150000
def contraction : ℝ≥0 := 1/10

theorem radius_positive : 0 < radius := by norm_num [radius,radiusRat]
theorem alpha_positive : 0 < alpha := by norm_num [alpha]
theorem contraction_lt_one : contraction < 1 := by norm_num [contraction]

theorem point_box (i : Fin 3) : Point.localBox i = (centreRat i,centreRat i) := by
  fin_cases i <;> decide +kernel

theorem hull_box (i : Fin 3) : Hull.localBox i = (centreRat i-radiusRat,centreRat i+radiusRat) := by
  fin_cases i <;> decide +kernel

theorem centre_in_point : InRectangle Point.localBox centre := by
  intro i
  rw [point_box]
  exact ⟨le_rfl,le_rfl⟩

theorem closedBall_in_hull (x : SourceGaussianModel.Point) (inside : x ∈ closedBall centre radius) :
    InRectangle Hull.localBox x := by
  have distance := Metric.mem_closedBall.mp inside
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg radius_positive.le] at distance
  intro i
  rw [hull_box]
  have h := abs_le.mp (distance i)
  change -(radiusRat : ℝ) ≤ x i - (centreRat i : ℝ) ∧
    x i - (centreRat i : ℝ) ≤ (radiusRat : ℝ) at h
  simp only [Holds,Rat.cast_sub,Rat.cast_add]
  constructor <;> linarith [h.1,h.2]

end
end LAlanine40K2025.BasinRefinement.WholeBandAttractor.Atom007
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
