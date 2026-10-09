import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A000.Geometry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A000.Point.Assembly
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A000.Hull.Assembly
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandAttractor.SourceFieldBounds

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAttractor.Atom000
open SourceGaussianModel SourceSignedEvaluator ContinuousGradient IntervalParameterMap WholeBandGenerated
open Metric
noncomputable section

def pointField : FieldBox := evaluatedField Point.densityRows
def hullField : FieldBox := evaluatedField Hull.densityRows

theorem point_actual : FieldHolds pointField centre :=
  evaluatedField_contains Point.densityRows centre (fun j => Point.actual_density j centre centre_in_point)

theorem hull_actual (x : SourceGaussianModel.Point) (inside : x ∈ closedBall centre radius) :
    FieldHolds hullField x := evaluatedField_contains Hull.densityRows x
      (fun j => Hull.actual_density j x (closedBall_in_hull x inside))

theorem gradient_numeric (i : Fin 3) : Taylor.absolutePair (pointField.gradient i) ≤ (1/1000000000 : ℚ) := by
  fin_cases i <;> decide +kernel

theorem actual_gradient_small : ‖sourceGradient centre‖ ≤ (1/1000000000 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/1000000000)).mpr
  intro i
  exact (Taylor.absolutePair_bound _ _ (point_actual.1 i)).trans (by
    have casted : (Taylor.absolutePair (pointField.gradient i) : ℝ) ≤ ((1/1000000000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (gradient_numeric i)
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast] at casted
    exact casted)

def shiftedPair (i j : Fin 3) : Pair :=
  add (point (if i = j then 1 else 0)) (mul (point (1/642000)) (hullField.hessian i j))

theorem shifted_numeric (i j : Fin 3) : Taylor.absolutePair (shiftedPair i j) ≤ (1/30 : ℚ) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem shifted_actual (x : SourceGaussianModel.Point) (inside : x ∈ closedBall centre radius)
    (i j : Fin 3) : Holds (shiftedPair i j) ((if i = j then 1 else 0) + alpha * sourceHessian x i j) := by
  have h := add_holds _ _ _ _ (point_holds (if i = j then (1 : ℚ) else 0))
    (mul_holds _ _ _ _ (point_holds (1/642000)) ((hull_actual x inside).2 i j))
  by_cases same : i = j <;> simpa [shiftedPair,alpha,same] using h

theorem actual_shifted_hessian (x : SourceGaussianModel.Point) (inside : x ∈ closedBall centre radius) :
    ‖ContinuousLinearMap.id ℝ SourceGaussianModel.Point + alpha • sourceHessianLinear x‖ ≤ (contraction : ℝ) := by
  apply shifted_hessian_norm x alpha contraction contraction.coe_nonneg
  intro i j
  have h := (Taylor.absolutePair_bound _ _ (shifted_actual x inside i j)).trans
    (show (Taylor.absolutePair (shiftedPair i j) : ℝ) ≤ 1/30 by
      have casted : (Taylor.absolutePair (shiftedPair i j) : ℝ) ≤ ((1/30 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (shifted_numeric i j)
      norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast] at casted
      exact casted)
  convert! h using 1; norm_num [contraction]

theorem actual_budget : alpha * ‖sourceGradient centre‖ + (contraction : ℝ) * radius < radius := by
  have h := actual_gradient_small
  norm_num [alpha,contraction,radius,radiusRat] at *
  linarith

end
end LAlanine40K2025.BasinRefinement.WholeBandAttractor.Atom000
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
