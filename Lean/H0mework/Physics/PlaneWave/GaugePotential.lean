import H0mework.Physics.GaugeAction.P286BracketCalculus
import H0mework.Physics.Holonomic.HolonomicGaugeCurvatureTransport

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Dynamics.PlaneWave

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286BracketCalculus SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite P286CoordinateIndex
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def nullGaugeCovector (direction : LorentzianIndex) : ℝ :=
  if direction = 0 then 1 else if direction = 3 then -1 else 0

/-- A full P286 profile in the source contact's common null direction.
Its transverse coordinate is the global AdS logarithmic coordinate. -/
def nullGaugeWrite (current : StageNineHolonomicConfiguration)
    (profile : ℝ → P286CoordinateCarrier) : StageNineHolonomicConfiguration :=
  { current with gaugeConnection := fun point direction =>
      p286CoordinateEquiv.symm (nullGaugeCovector direction • profile (point 2)) }

theorem nullGaugeWrite_bracket_zero (current : StageNineHolonomicConfiguration)
    (profile : ℝ → P286CoordinateCarrier) (point : BasePoint)
    (first second : LorentzianIndex) :
    p286LieBracket ((nullGaugeWrite current profile).gaugeConnection point first)
      ((nullGaugeWrite current profile).gaugeConnection point second) = 0 := by
  change p286LieBracket (p286CoordinateEquiv.symm (_ • _))
    (p286CoordinateEquiv.symm (_ • _)) = 0
  rw [map_smul, map_smul, p286LieBracket_smul_left, p286LieBracket_smul_right]
  have self (value : P286LieBlockData) : p286LieBracket value value = 0 := by
    apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, suLieBracket]
    · apply Prod.ext
      · apply Subtype.ext
        simp [p286LieBracket, suLieBracket]
      · rfl
  rw [self, smul_zero, smul_zero]

theorem nullGaugeWrite_directionalDerivative
    (current : StageNineHolonomicConfiguration) (profile : ℝ → P286CoordinateCarrier)
    (point : BasePoint) (velocity : P286CoordinateCarrier)
    (derivative : HasDerivAt profile velocity (point 2))
    (derivativeDirection formDirection : LorentzianIndex) :
    p286ConnectionDerivative (nullGaugeWrite current profile) point
        derivativeDirection formDirection =
      p286CoordinateEquiv.symm
        ((if derivativeDirection = 2 then (1 : ℝ) else 0) •
          (nullGaugeCovector formDirection • velocity)) := by
  unfold p286ConnectionDerivative fieldDirectionalDerivative
  have composed := (derivative.hasFDerivAt.comp point
    (EuclideanSpace.proj (2 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
      ).const_smul (nullGaugeCovector formDirection)
  change HasFDerivAt (fun candidate : BasePoint =>
    nullGaugeCovector formDirection • profile (candidate 2)) _ point at composed
  have fieldEq : (fun candidate : BasePoint => p286CoordinateEquiv
      ((nullGaugeWrite current profile).gaugeConnection candidate formDirection)) =
      fun candidate => nullGaugeCovector formDirection • profile (candidate 2) := by
    funext candidate
    exact p286CoordinateEquiv.apply_symm_apply _
  rw [fieldEq, composed.fderiv]
  apply congrArg p286CoordinateEquiv.symm
  change nullGaugeCovector formDirection •
      ((coordinateDirection derivativeDirection) 2 • velocity) = _
  simp only [coordinateDirection, PiLp.single_apply]
  by_cases same : derivativeDirection = 2
  · subst derivativeDirection
    simp only [ite_true, one_smul]
  · simp only [same, Ne.symm same, ite_false, zero_smul, smul_zero]

theorem nullGaugeWrite_curvature
    (current : StageNineHolonomicConfiguration) (profile : ℝ → P286CoordinateCarrier)
    (point : BasePoint) (velocity : P286CoordinateCarrier)
    (derivative : HasDerivAt profile velocity (point 2)) (pair : Fin 6) :
    holonomicGaugeCurvature (nullGaugeWrite current profile) point pair =
      p286CoordinateEquiv.symm
        (((if pairFirst pair = 2 then 1 else 0) * nullGaugeCovector (pairSecond pair) -
          (if pairSecond pair = 2 then 1 else 0) * nullGaugeCovector (pairFirst pair)) •
            velocity) := by
  unfold holonomicGaugeCurvature
  rw [nullGaugeWrite_directionalDerivative current profile point velocity derivative,
    nullGaugeWrite_directionalDerivative current profile point velocity derivative,
    nullGaugeWrite_bracket_zero, add_zero, ← map_sub]
  congr 1
  simp only [smul_smul, sub_smul]

theorem nullGaugeWrite_curvature_array
    (current : StageNineHolonomicConfiguration) (profile : ℝ → P286CoordinateCarrier)
    (point : BasePoint) (velocity : P286CoordinateCarrier)
    (derivative : HasDerivAt profile velocity (point 2)) :
    holonomicGaugeCurvature (nullGaugeWrite current profile) point =
      fun pair => (![0,-1,0,-1,0,0] : Fin 6 → ℝ) pair •
        p286CoordinateEquiv.symm velocity := by
  funext pair
  rw [nullGaugeWrite_curvature current profile point velocity derivative]
  fin_cases pair <;> simp [nullGaugeCovector, pairFirst, pairSecond]
  all_goals exact (neg_one_smul ℝ _).symm

end
end SaturationMonoid.PhysicsCore.Stage9C.Dynamics.PlaneWave
