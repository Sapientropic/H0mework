import H0mework.Physics.MotherProgrammesFormationCurrent.Consumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction

open StageNineSourceGeneratedMotherTimeCauchyFlow StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource StageNineHolonomicField SU7MotherLieAlgebra
open DiracExteriorMatterAction
open GaugeProjection

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData := ActualInitial.p286ModuleFinite
local instance : Fintype P286CoordinateIndex := ActualInitial.p286CoordinateFintype
local instance : Fintype MatterCoordinateIndex := Fintype.ofFinite _

def colorLinear (group : SU3Gauge) : SU3BlockLieMatrix →ₗ[ℝ] SU3BlockLieMatrix where
  toFun := colorGaugeConjugate group
  map_add' first second := by
    apply Subtype.ext
    simp [colorGaugeConjugate, mul_add, add_mul]
  map_smul' scalar value := by
    apply Subtype.ext
    simp [colorGaugeConjugate]

def p286Linear (source : SmoothUnifiedSource) (time : ℝ) :
    P286LieBlockData →ₗ[ℝ] P286LieBlockData where
  toFun := sourceGeneratedMotherTimeP286Adjoint source time
  map_add' first second := by
    exact Prod.ext ((colorLinear (sourceMotherTimeColorElement source time)).map_add _ _) rfl
  map_smul' scalar value := by
    exact Prod.ext ((colorLinear (sourceMotherTimeColorElement source time)).map_smul scalar _) rfl

def gaugeCoordinates (source : SmoothUnifiedSource) (time : ℝ) :
    P286CoordinateCarrier →ₗ[ℝ] P286CoordinateCarrier :=
  p286CoordinateEquiv.toLinearMap.comp
    ((p286Linear source time).comp p286CoordinateEquiv.symm.toLinearMap)

def scalarCoordinates (source : SmoothUnifiedSource) (time : ℝ) :
    ScalarCoordinateCarrier →ₗ[ℂ] ScalarCoordinateCarrier :=
  scalarCoordinateEquiv.toLinearMap.comp
    ((SU7ExteriorBreakingYukawa.exteriorBreakingScalarRepresentation
      (sourceGeneratedMotherTimeTransport source time)).comp scalarCoordinateEquiv.symm.toLinearMap)

def matterCoordinates (source : SmoothUnifiedSource) (time : ℝ) :
    MatterCoordinateCarrier →ₗ[ℂ] MatterCoordinateCarrier :=
  matterCoordinateEquiv.toLinearMap.comp
    ((diracExteriorMatterGaugeRepresentation (sourceGeneratedMotherTimeTransport source time)).comp
      matterCoordinateEquiv.symm.toLinearMap)

/-- The independent dual is acted on by the original inverse representation. -/
def dualCoordinates (source : SmoothUnifiedSource) (time : ℝ) :
    (MatterCoordinateIndex → ℂ) →ₗ[ℂ] (MatterCoordinateIndex → ℂ) where
  toFun coefficients index :=
    CurrentMaterial.coordinateDual coefficients
      (diracExteriorMatterGaugeRepresentation (sourceGeneratedMotherTimeTransport source time)⁻¹
        (matterCoordinateEquiv.symm (EuclideanSpace.single index 1)))
  map_add' first second := by
    funext index
    simp [CurrentMaterial.coordinateDual, mul_add, Finset.sum_add_distrib]
  map_smul' scalar coefficients := by
    funext index
    simp [CurrentMaterial.coordinateDual, Finset.mul_sum, mul_left_comm]

theorem gauge_coordinates_actual (source : SmoothUnifiedSource) (time : ℝ)
    (value : P286LieBlockData) :
    gaugeCoordinates source time (p286CoordinateEquiv value) =
      p286CoordinateEquiv (sourceGeneratedMotherTimeP286Adjoint source time value) := by
  change p286CoordinateEquiv (sourceGeneratedMotherTimeP286Adjoint source time
    (p286CoordinateEquiv.symm (p286CoordinateEquiv value))) = _
  rw [p286CoordinateEquiv.symm_apply_apply]

theorem scalar_coordinates_actual (source : SmoothUnifiedSource) (time : ℝ)
    (value : ScalarCoordinateCarrier) :
    scalarCoordinates source time value =
      scalarCoordinateAction (sourceGeneratedMotherTimeTransport source time) value := rfl

theorem matter_coordinates_actual (source : SmoothUnifiedSource) (time : ℝ)
    (value : DiracExteriorMatterCarrier) :
    matterCoordinates source time (matterCoordinateEquiv value) =
      matterCoordinateEquiv (diracExteriorMatterGaugeRepresentation
        (sourceGeneratedMotherTimeTransport source time) value) := by
  change matterCoordinateEquiv (diracExteriorMatterGaugeRepresentation
    (sourceGeneratedMotherTimeTransport source time)
    (matterCoordinateEquiv.symm (matterCoordinateEquiv value))) = _
  rw [matterCoordinateEquiv.symm_apply_apply]

theorem dual_coordinates_actual (source : SmoothUnifiedSource) (time : ℝ)
    (value : Module.Dual ℂ DiracExteriorMatterCarrier) :
    dualCoordinates source time
        (fun index => value (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))) =
      fun index => value
        (diracExteriorMatterGaugeRepresentation (sourceGeneratedMotherTimeTransport source time)⁻¹
          (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))) := by
  funext index
  change CurrentMaterial.coordinateDual _ _ = _
  rw [CurrentMaterial.coordinateDual_recovers]

theorem gauge_continuous (source : SmoothUnifiedSource) (time : ℝ) :
    Continuous (gaugeCoordinates source time) :=
  (gaugeCoordinates source time).continuous_of_finiteDimensional

theorem scalar_continuous (source : SmoothUnifiedSource) (time : ℝ) :
    Continuous (scalarCoordinates source time) :=
  (scalarCoordinates source time).continuous_of_finiteDimensional

theorem matter_continuous (source : SmoothUnifiedSource) (time : ℝ) :
    Continuous (matterCoordinates source time) :=
  (matterCoordinates source time).continuous_of_finiteDimensional

theorem dual_continuous (source : SmoothUnifiedSource) (time : ℝ) :
    Continuous (dualCoordinates source time) :=
  (dualCoordinates source time).continuous_of_finiteDimensional

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction
