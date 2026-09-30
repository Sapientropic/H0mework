import H0mework.Physics.Fluid.Fields

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fluid

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineCanonicalCauchyState StageNineDynamicBreakingVacuum
open DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineConjugateMatterVariation
open MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

def coordinateDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : BasePoint → E) (direction : Fin 4) (point : BasePoint) : E :=
  fderiv ℝ field point (coordinateDirection direction)

theorem coordinateDerivative_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : BasePoint → E} (smooth : ContDiff ℝ ∞ field) (direction : Fin 4) :
    ContDiff ℝ ∞ (coordinateDerivative field direction) :=
  (smooth.fderiv_right (by simp)).clm_apply contDiff_const

def curl (field : BasePoint → StageNineSpatialPoint) (point : BasePoint) : StageNineSpatialPoint :=
  WithLp.toLp 2 ![coordinateDerivative field 2 point 2 - coordinateDerivative field 3 point 1,
    coordinateDerivative field 3 point 0 - coordinateDerivative field 1 point 2,
    coordinateDerivative field 1 point 1 - coordinateDerivative field 2 point 0]

theorem curl_contDiff {field : BasePoint → StageNineSpatialPoint}
    (smooth : ContDiff ℝ ∞ field) : ContDiff ℝ ∞ (curl field) := by
  have each (direction : Fin 4) (coordinate : Fin 3) :
      ContDiff ℝ ∞ (fun point => coordinateDerivative field direction point coordinate) :=
    (contDiff_piLp 2).mp (coordinateDerivative_contDiff smooth direction) coordinate
  apply (contDiff_piLp 2).2
  intro coordinate
  fin_cases coordinate <;> first
    | exact (each 2 2).sub (each 3 1)
    | exact (each 3 0).sub (each 1 2)
    | exact (each 1 1).sub (each 2 0)

def laplacian (field : BasePoint → StageNineSpatialPoint) (point : BasePoint) : StageNineSpatialPoint :=
  ∑ direction : Fin 3, coordinateDerivative (coordinateDerivative field direction.succ) direction.succ point

theorem laplacian_contDiff {field : BasePoint → StageNineSpatialPoint}
    (smooth : ContDiff ℝ ∞ field) : ContDiff ℝ ∞ (laplacian field) :=
  ContDiff.sum fun direction _ => coordinateDerivative_contDiff (coordinateDerivative_contDiff smooth direction.succ) direction.succ

def cross (left right : BasePoint → StageNineSpatialPoint) (point : BasePoint) : StageNineSpatialPoint :=
  WithLp.toLp 2 ![left point 1 * right point 2 - left point 2 * right point 1,
    left point 2 * right point 0 - left point 0 * right point 2,
    left point 0 * right point 1 - left point 1 * right point 0]

theorem cross_contDiff {left right : BasePoint → StageNineSpatialPoint}
    (smoothLeft : ContDiff ℝ ∞ left) (smoothRight : ContDiff ℝ ∞ right) :
    ContDiff ℝ ∞ (cross left right) := by
  have componentLeft := (contDiff_piLp 2).mp smoothLeft
  have componentRight := (contDiff_piLp 2).mp smoothRight
  apply (contDiff_piLp 2).2
  intro coordinate
  fin_cases coordinate <;> first
    | exact ((componentLeft 1).mul (componentRight 2)).sub ((componentLeft 2).mul (componentRight 1))
    | exact ((componentLeft 2).mul (componentRight 0)).sub ((componentLeft 0).mul (componentRight 2))
    | exact ((componentLeft 0).mul (componentRight 1)).sub ((componentLeft 1).mul (componentRight 0))


end
end SaturationMonoid.PhysicsCore.Stage9CU.Fluid
