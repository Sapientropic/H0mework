import H0mework.Physics.Fluid.Differential
import Mathlib.Analysis.Calculus.Deriv.Shift

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fluid

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineCanonicalCauchyState StageNineP286ActionCauchySplit
open scoped ContDiff

noncomputable section

/-- Coordinate-line differentiation does not require differentiability in the other directions. -/
def coordinateLineDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : BasePoint → E) (direction : Fin 4) (point : BasePoint) : E :=
  deriv (fun parameter : ℝ => field (point + parameter • coordinateDirection direction)) 0

theorem coordinateLine_hasDerivAt (point : BasePoint) (direction : Fin 4) (parameter : ℝ) :
    HasDerivAt (fun step : ℝ => point + step • coordinateDirection direction)
      (coordinateDirection direction) parameter := by
  simpa only [one_smul, id_eq] using
    ((hasDerivAt_id parameter).smul_const (coordinateDirection direction)).const_add point

theorem coordinateLineDerivative_eq_of_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : BasePoint → E} {point : BasePoint}
    (differentiable : DifferentiableAt ℝ field point) (direction : Fin 4) :
    coordinateLineDerivative field direction point = coordinateDerivative field direction point := by
  have derivative := differentiable.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (coordinateLine_hasDerivAt point direction 0) (by simp)
  exact derivative.deriv

theorem coordinateLineDerivative_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : BasePoint → E} (smooth : ContDiff ℝ ∞ field) (direction : Fin 4) :
    coordinateLineDerivative field direction = coordinateDerivative field direction := by
  funext point
  exact coordinateLineDerivative_eq_of_differentiableAt
    ((smooth.differentiable (by simp)) point) direction

def lineCurl (field : BasePoint → StageNineSpatialPoint) (point : BasePoint) : StageNineSpatialPoint :=
  WithLp.toLp 2 ![coordinateLineDerivative field 2 point 2 - coordinateLineDerivative field 3 point 1,
    coordinateLineDerivative field 3 point 0 - coordinateLineDerivative field 1 point 2,
    coordinateLineDerivative field 1 point 1 - coordinateLineDerivative field 2 point 0]

theorem lineCurl_eq {field : BasePoint → StageNineSpatialPoint}
    (smooth : ContDiff ℝ ∞ field) : lineCurl field = curl field := by
  funext point
  simp only [lineCurl, coordinateLineDerivative_eq smooth, curl]

def lineLaplacian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : BasePoint → E) (point : BasePoint) : E :=
  ∑ direction : Fin 3,
    coordinateLineDerivative (coordinateLineDerivative field direction.succ) direction.succ point

theorem lineLaplacian_eq {field : BasePoint → StageNineSpatialPoint}
    (smooth : ContDiff ℝ ∞ field) : lineLaplacian field = laplacian field := by
  funext point
  simp only [lineLaplacian, coordinateLineDerivative_eq smooth,
    coordinateLineDerivative_eq (coordinateDerivative_contDiff smooth _), laplacian]

theorem canonicalSlice_timeLine (time parameter : ℝ) (space : StageNineSpatialPoint) :
    canonicalCauchySlicePoint time space + parameter • coordinateDirection 0 =
      canonicalCauchySlicePoint (time + parameter) space := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, coordinateDirection, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem canonicalSlice_spatialLine (time parameter : ℝ) (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    canonicalCauchySlicePoint time space + parameter • coordinateDirection direction.succ =
      canonicalCauchySlicePoint time (space + parameter • EuclideanSpace.single direction 1) := by
  apply PiLp.ext
  intro output
  fin_cases direction <;> fin_cases output <;>
    simp [canonicalCauchySlicePoint, coordinateDirection, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem coordinateLineDerivative_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : BasePoint → E) (time : ℝ) (space : StageNineSpatialPoint) :
    coordinateLineDerivative field 0 (canonicalCauchySlicePoint time space) =
      deriv (fun parameter : ℝ => field (canonicalCauchySlicePoint (time + parameter) space)) 0 := by
  simp only [coordinateLineDerivative, canonicalSlice_timeLine]

theorem coordinateLineDerivative_time_eq_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : BasePoint → E) (time : ℝ) (space : StageNineSpatialPoint) :
    coordinateLineDerivative field 0 (canonicalCauchySlicePoint time space) =
      deriv (fun sample : ℝ => field (canonicalCauchySlicePoint sample space)) time := by
  rw [coordinateLineDerivative_time]
  simpa only [add_zero] using
    deriv_comp_const_add (fun sample : ℝ => field (canonicalCauchySlicePoint sample space)) time 0

theorem coordinateLineDerivative_spatial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : BasePoint → E) (time : ℝ) (space : StageNineSpatialPoint) (direction : Fin 3) :
    coordinateLineDerivative field direction.succ (canonicalCauchySlicePoint time space) =
      deriv (fun parameter : ℝ => field
        (canonicalCauchySlicePoint time (space + parameter • EuclideanSpace.single direction 1))) 0 := by
  simp only [coordinateLineDerivative, canonicalSlice_spatialLine]

/-- Only the fixed spatial slice is differentiated; no spacetime regularity is assumed. -/
theorem coordinateLineDerivative_spatial_of_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : BasePoint → E} {time : ℝ} {space : StageNineSpatialPoint}
    (differentiable : DifferentiableAt ℝ (fun place => field (canonicalCauchySlicePoint time place)) space)
    (direction : Fin 3) :
    coordinateLineDerivative field direction.succ (canonicalCauchySlicePoint time space) =
      fderiv ℝ (fun place => field (canonicalCauchySlicePoint time place)) space
        (EuclideanSpace.single direction 1) := by
  rw [coordinateLineDerivative_spatial]
  have line : HasDerivAt (fun parameter : ℝ => space + parameter • EuclideanSpace.single direction 1)
      (EuclideanSpace.single direction 1) 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single direction 1)).const_add space
  exact (differentiable.hasFDerivAt.comp_hasDerivAt_of_eq 0 line (by simp)).deriv

end
end SaturationMonoid.PhysicsCore.Stage9CU.Fluid
