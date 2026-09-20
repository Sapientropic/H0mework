import H0mework.Physics.Holonomic.HolonomicField
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace SaturationMonoid.PhysicsCore.StageNineCompactSupportIntegrationByParts

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField
open MeasureTheory
open scoped ContDiff

noncomputable section

/-- A genuine compactly supported smooth variation.  The support and
smoothness are properties of a function, not a stored stationarity receipt.
-/
structure CompactlySupportedSmoothVariation
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  toFun : BasePoint → V
  smooth : ContDiff ℝ ∞ toFun
  compactSupport : HasCompactSupport toFun

instance {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    CoeFun (CompactlySupportedSmoothVariation V) fun _ => BasePoint → V :=
  ⟨CompactlySupportedSmoothVariation.toFun⟩

theorem hasCompactSupport_bilinear_right
    {F G W : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : F →L[ℝ] G →L[ℝ] W)
    (first : BasePoint → F) (second : BasePoint → G)
    (secondCompact : HasCompactSupport second) :
    HasCompactSupport fun point => B (first point) (second point) := by
  rw [hasCompactSupport_iff_eventuallyEq] at secondCompact ⊢
  filter_upwards [secondCompact] with point pointZero
  simp [pointZero]

theorem compactVariation_directionalDerivative_compact
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (variation : CompactlySupportedSmoothVariation V)
    (direction : LorentzianIndex) :
    HasCompactSupport fun point =>
      fderiv ℝ variation point (coordinateDirection direction) :=
  variation.compactSupport.fderiv_apply (𝕜 := ℝ)
    (coordinateDirection direction)

theorem compactVariation_directionalDerivative_continuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (variation : CompactlySupportedSmoothVariation V)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      fderiv ℝ variation point (coordinateDirection direction) := by
  have derivativeContinuous : Continuous (fderiv ℝ variation) :=
    (variation.smooth.fderiv_right (m := 0) (by simp)).continuous
  exact derivativeContinuous.clm_apply continuous_const

/-- Actual four-dimensional integration by parts over `BasePoint`.  Compact
support discharges the boundary term and all three integrability obligations;
none of them is supplied to the theorem. -/
theorem compactSupport_integrationByParts
    {F G W : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : F →L[ℝ] G →L[ℝ] W)
    (background : BasePoint → F)
    (variation : CompactlySupportedSmoothVariation G)
    (backgroundSmooth : ContDiff ℝ ∞ background)
    (direction : LorentzianIndex) :
    (∫ point : BasePoint,
        B (background point)
          (fderiv ℝ variation point (coordinateDirection direction))) =
      -(∫ point : BasePoint,
        B (fderiv ℝ background point (coordinateDirection direction))
          (variation point)) := by
  let v := coordinateDirection direction
  have backgroundDerivativeContinuous : Continuous (fderiv ℝ background) :=
    (backgroundSmooth.fderiv_right (m := 0) (by simp)).continuous
  have backgroundDirectionalContinuous : Continuous fun point =>
      fderiv ℝ background point v :=
    backgroundDerivativeContinuous.clm_apply continuous_const
  have variationDirectionalContinuous : Continuous fun point =>
      fderiv ℝ variation point v := by
    simpa [v] using
      compactVariation_directionalDerivative_continuous variation direction
  have backgroundContinuous : Continuous background := backgroundSmooth.continuous
  have variationContinuous : Continuous variation := variation.smooth.continuous
  have firstTermContinuous : Continuous fun point =>
      B (fderiv ℝ background point v) (variation point) :=
    (B.continuous.comp backgroundDirectionalContinuous).clm_apply
      variationContinuous
  have secondTermContinuous : Continuous fun point =>
      B (background point) (fderiv ℝ variation point v) :=
    (B.continuous.comp backgroundContinuous).clm_apply
      variationDirectionalContinuous
  have productContinuous : Continuous fun point =>
      B (background point) (variation point) :=
    (B.continuous.comp backgroundContinuous).clm_apply variationContinuous
  have variationDerivativeCompact : HasCompactSupport fun point =>
      fderiv ℝ variation point v := by
    simpa [v] using
      compactVariation_directionalDerivative_compact variation direction
  have firstTermCompact : HasCompactSupport fun point =>
      B (fderiv ℝ background point v) (variation point) :=
    hasCompactSupport_bilinear_right B _ _ variation.compactSupport
  have secondTermCompact : HasCompactSupport fun point =>
      B (background point) (fderiv ℝ variation point v) :=
    hasCompactSupport_bilinear_right B _ _ variationDerivativeCompact
  have productCompact : HasCompactSupport fun point =>
      B (background point) (variation point) :=
    hasCompactSupport_bilinear_right B _ _ variation.compactSupport
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume)
    (firstTermContinuous.integrable_of_hasCompactSupport firstTermCompact)
    (secondTermContinuous.integrable_of_hasCompactSupport secondTermCompact)
    (productContinuous.integrable_of_hasCompactSupport productCompact)
    (fun _ _ => (backgroundSmooth.differentiable (by simp)).differentiableAt)
    (fun _ _ => (variation.smooth.differentiable (by simp)).differentiableAt)

def unitCompactBump : ContDiffBump (0 : BasePoint) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def nonzeroCompactScalarVariation :
    CompactlySupportedSmoothVariation ℝ where
  toFun := unitCompactBump
  smooth := unitCompactBump.contDiff
  compactSupport := unitCompactBump.hasCompactSupport

/-- Non-vacuity: the compact-support variation class contains an explicit
nonzero smooth bump. -/
theorem nonzeroCompactScalarVariation_ne_zero :
    nonzeroCompactScalarVariation.toFun ≠ 0 := by
  intro variationZero
  have centerZero := congrFun variationZero 0
  have centerOne : unitCompactBump (0 : BasePoint) = 1 := by
    apply unitCompactBump.one_of_mem_closedBall
    exact Metric.mem_closedBall_self unitCompactBump.rIn_pos.le
  simp [nonzeroCompactScalarVariation, centerOne] at centerZero

end

end SaturationMonoid.PhysicsCore.StageNineCompactSupportIntegrationByParts
