import H0mework.Physics.Lorentz.LorentzConnectionAlgebraicCurrentRegularity
import H0mework.Physics.Lorentz.LorentzTemporalGaussResidualTangency

/-!
# Stage-9 Lorentz temporal-Gauss first variation

This module extracts the reusable differential core behind the C3h202 exact
obstruction.  For any already generated smooth, nondegenerate actual it
constructs the canonical-contact temporal-Gauss first-variation carrier:

```text
gravity-BF algebraic derivative
+ matter-spin derivative
+ mixed BF-momentum derivative.
```

The sum is proved to be the genuine `HasDerivAt` coefficient of the same
actual's temporal-Gauss residual time trace.  No residual value, target zero,
response, repair, branch, endpoint, or equation certificate is accepted.
This is an actual readout/diagnostic API; exact producer modules must supply
their own actual and provenance.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineLorentzTemporalGaussFirstVariation

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConnectionSectorSourceBalance
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLorentzActionCauchySplit
open StageNineLorentzConnectionAlgebraicCurrentRegularity
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineLorentzTemporalGaussResidualTangency
open StageNineP286ActionCauchySplit
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- A directional derivative of a smooth real field is again smooth. -/
theorem fieldDirectionalDerivative_contDiff
    {field : BasePoint → ℝ}
    (smooth : ContDiff ℝ ∞ field)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      fieldDirectionalDerivative field point direction := by
  unfold fieldDirectionalDerivative
  simpa [Function.comp_def] using
    (smooth.contDiff_fderiv_apply (m := ∞) (by simp)).comp
      (contDiff_prodMk_left (coordinateDirection direction))

/-- The complete spatial BF-momentum divergence is smooth on every smooth,
nondegenerate actual. -/
theorem lorentzConnectionSpatialBFMomentumDivergence_contDiff
    (actual : StageNineHolonomicConfiguration)
    (smooth : actual.Smooth)
    (nondegenerate : actual.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    ContDiff ℝ ∞
      (StageNineLorentzActionCauchySplit.lorentzConnectionSpatialBFMomentumDivergence
        actual direction) := by
  unfold
    StageNineLorentzActionCauchySplit.lorentzConnectionSpatialBFMomentumDivergence
  exact
    ((fieldDirectionalDerivative_contDiff
      (lorentzConnectionBFDifferentialMomentum_contDiff actual smooth
        nondegenerate
        (lorentzConnectionExteriorDerivativeDirection 1 direction)) 1).add
      (fieldDirectionalDerivative_contDiff
        (lorentzConnectionBFDifferentialMomentum_contDiff actual smooth
          nondegenerate
          (lorentzConnectionExteriorDerivativeDirection 2 direction)) 2)).add
      (fieldDirectionalDerivative_contDiff
        (lorentzConnectionBFDifferentialMomentum_contDiff actual smooth
          nondegenerate
          (lorentzConnectionExteriorDerivativeDirection 3 direction)) 3)

private theorem canonicalCauchyTimeLine_hasDerivAt_origin :
    HasDerivAt
      (fun time : ℝ =>
        canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
      (coordinateDirection canonicalLorentzianTimeDirection) 0 := by
  rw [show
    (fun time : ℝ =>
      canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) =
        fun time =>
          time • coordinateDirection canonicalLorentzianTimeDirection by
    funext time
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, coordinateDirection,
        canonicalLorentzianTimeDirection, Fin.sum_univ_three]]
  simpa using
    (hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const
      (coordinateDirection canonicalLorentzianTimeDirection)

/-- Chain rule from a smooth field on spacetime to the canonical contact
time line. -/
theorem hasDerivAt_canonicalTimeTrace_origin
    {field : BasePoint → ℝ}
    (smooth : ContDiff ℝ ∞ field) :
    HasDerivAt
      (fun time =>
        field (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)))
      (fieldDirectionalDerivative field 0
        canonicalLorentzianTimeDirection)
      0 := by
  have outer :
      HasFDerivAt field (fderiv ℝ field 0)
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
    rw [canonicalCauchySlicePoint_zero_zero]
    exact
      (smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  simpa [Function.comp_def, fieldDirectionalDerivative] using
    outer.comp_hasDerivAt 0 canonicalCauchyTimeLine_hasDerivAt_origin

/-! ## Generic component-indexed obstruction -/

def lorentzTemporalGaussGravityBFTangencyTerm
    (actual : StageNineHolonomicConfiguration)
    (component : LorentzTemporalBivectorDirection) : ℝ :=
  fieldDirectionalDerivative
    (lorentzGravityBFAlgebraicCoefficient actual
      (canonicalLorentzTemporalBivectorOneForm component))
    0 canonicalLorentzianTimeDirection

def lorentzTemporalGaussMatterSpinTangencyTerm
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (component : LorentzTemporalBivectorDirection) : ℝ :=
  fieldDirectionalDerivative
    (lorentzMatterSpinSourceCoefficient source actual
      (canonicalLorentzTemporalBivectorOneForm component))
    0 canonicalLorentzianTimeDirection

def lorentzTemporalGaussMixedBFTangencyTerm
    (actual : StageNineHolonomicConfiguration)
    (component : LorentzTemporalBivectorDirection) : ℝ :=
  -fieldDirectionalDerivative
    (StageNineLorentzActionCauchySplit.lorentzConnectionSpatialBFMomentumDivergence
      actual (canonicalLorentzTemporalBivectorOneForm component))
    0 canonicalLorentzianTimeDirection

/-- Actual three-sector tangency obstruction of one already generated
configuration. -/
def lorentzTemporalGaussTangencyObstruction
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration) :
    LorentzTemporalGaussResidualCarrier :=
  fun component =>
    fieldDirectionalDerivative
        (lorentzConnectionAlgebraicSpinCurrentCoefficient source actual
          (canonicalLorentzTemporalBivectorOneForm component))
        0 canonicalLorentzianTimeDirection -
      fieldDirectionalDerivative
        (StageNineLorentzActionCauchySplit.lorentzConnectionSpatialBFMomentumDivergence
          actual (canonicalLorentzTemporalBivectorOneForm component))
        0 canonicalLorentzianTimeDirection

/-- The obstruction keeps gravity-BF, matter-spin, and mixed-BF
responsibilities separate. -/
theorem lorentzTemporalGaussTangencyObstruction_eq_sectors
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (smooth : actual.Smooth)
    (nondegenerate : actual.Nondegenerate)
    (component : LorentzTemporalBivectorDirection) :
    lorentzTemporalGaussTangencyObstruction source actual component =
      lorentzTemporalGaussGravityBFTangencyTerm actual component +
        lorentzTemporalGaussMatterSpinTangencyTerm source actual component +
        lorentzTemporalGaussMixedBFTangencyTerm actual component := by
  have gravitySmooth :=
    lorentzGravityBFAlgebraicCoefficient_contDiff actual smooth
      nondegenerate (canonicalLorentzTemporalBivectorOneForm component)
  have matterSmooth :=
    lorentzMatterSpinSourceCoefficient_contDiff source actual smooth
      nondegenerate (canonicalLorentzTemporalBivectorOneForm component)
  have algebraicEq :
      lorentzConnectionAlgebraicSpinCurrentCoefficient source actual
          (canonicalLorentzTemporalBivectorOneForm component) =
        fun point =>
          lorentzGravityBFAlgebraicCoefficient actual
              (canonicalLorentzTemporalBivectorOneForm component) point +
            lorentzMatterSpinSourceCoefficient source actual
              (canonicalLorentzTemporalBivectorOneForm component) point := by
    funext point
    exact lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors
      source actual (canonicalLorentzTemporalBivectorOneForm component) point
  unfold lorentzTemporalGaussTangencyObstruction
    lorentzTemporalGaussGravityBFTangencyTerm
    lorentzTemporalGaussMatterSpinTangencyTerm
    lorentzTemporalGaussMixedBFTangencyTerm
  rw [algebraicEq]
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add
    (gravitySmooth.differentiable (by simp) 0)
    (matterSmooth.differentiable (by simp) 0)]
  rfl

/-- The obstruction is the genuine derivative coefficient of the same
actual's temporal-Gauss residual trace. -/
theorem lorentzTemporalGaussResidualTimeTrace_hasDerivAt_obstruction
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (smooth : actual.Smooth)
    (nondegenerate : actual.Nondegenerate)
    (component : LorentzTemporalBivectorDirection) :
    HasDerivAt
      (lorentzTemporalGaussResidualTimeTrace source actual 0 component)
      (lorentzTemporalGaussTangencyObstruction source actual component)
      0 := by
  rw [show
    lorentzTemporalGaussResidualTimeTrace source actual 0 component =
      fun time =>
        lorentzConnectionAlgebraicSpinCurrentCoefficient source actual
            (canonicalLorentzTemporalBivectorOneForm component)
            (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) -
          StageNineLorentzActionCauchySplit.lorentzConnectionSpatialBFMomentumDivergence
            actual (canonicalLorentzTemporalBivectorOneForm component)
            (canonicalCauchySlicePoint time
              (0 : StageNineSpatialPoint)) by
    funext time
    exact lorentzTemporalGaussResidualTimeTrace_apply
      source actual 0 component time]
  exact
    (hasDerivAt_canonicalTimeTrace_origin
      (lorentzConnectionAlgebraicSpinCurrentCoefficient_contDiff
        source actual smooth nondegenerate
        (canonicalLorentzTemporalBivectorOneForm component))).sub
      (hasDerivAt_canonicalTimeTrace_origin
        (lorentzConnectionSpatialBFMomentumDivergence_contDiff
          actual smooth nondegenerate
          (canonicalLorentzTemporalBivectorOneForm component)))

end

end
  SaturationMonoid.PhysicsCore.StageNineLorentzTemporalGaussFirstVariation
