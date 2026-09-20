import H0mework.Physics.Cauchy.CanonicalCauchyState
import H0mework.Physics.Cauchy.LorentzActionCauchySplit

/-!
# Stage-9 Lorentz temporal-Gauss residual and time trace

Canonical Lorentz Gauss is a zero-fiber condition on the six temporal
connection tests.  This module exposes the complete residual carrier and its
canonical time trace without assuming smoothness and without selecting a
repair, endpoint, source certificate, or target tangent.

The trace reads one already constructed actual.  Later `HasDerivAt` theorems
can therefore generate its genuine tangency obstruction without relying on
the totalized value of `deriv` or `fderiv`.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineLorentzTemporalGaussResidualTangency

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLorentzActionCauchySplit
open StageNineLorentzConnectionPointwiseEquation

noncomputable section

set_option autoImplicit false

/-- Complete six-component Lorentz temporal-Gauss residual carrier. -/
abbrev LorentzTemporalGaussResidualCarrier :=
  LorentzTemporalBivectorDirection → ℝ

/-- Pointwise temporal-Gauss residual of one already generated actual. -/
def lorentzTemporalGaussResidualAt
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    LorentzTemporalGaussResidualCarrier :=
  fun component =>
    lorentzTemporalGaussResidual source actual point component

@[simp] theorem lorentzTemporalGaussResidualAt_apply
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (component : LorentzTemporalBivectorDirection) :
    lorentzTemporalGaussResidualAt source actual point component =
      lorentzConnectionAlgebraicSpinCurrentCoefficient source actual
          (canonicalLorentzTemporalBivectorOneForm component) point -
        lorentzConnectionSpatialBFMomentumDivergence actual
          (canonicalLorentzTemporalBivectorOneForm component) point := by
  exact lorentzTemporalGaussResidual_eq_algebraic_sub_spatial
    source actual point component

/-- The carrier zero fiber is exactly canonical Lorentz temporal Gauss. -/
theorem lorentzTemporalGaussResidualAt_eq_zero_iff
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    lorentzTemporalGaussResidualAt source actual point = 0 ↔
      CanonicalLorentzTemporalGaussConstraintAt source actual point := by
  constructor
  · intro residualZero component
    exact congrFun residualZero component
  · intro gauss
    funext component
    exact gauss component

/-- Restriction of one residual component to the canonical time line through
one spatial contact.  It remains a readout of the same actual. -/
def lorentzTemporalGaussResidualTimeTrace
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (component : LorentzTemporalBivectorDirection)
    (time : ℝ) : ℝ :=
  lorentzTemporalGaussResidualAt source actual
    (canonicalCauchySlicePoint time space) component

@[simp] theorem lorentzTemporalGaussResidualTimeTrace_apply
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (component : LorentzTemporalBivectorDirection)
    (time : ℝ) :
    lorentzTemporalGaussResidualTimeTrace source actual space component time =
      lorentzConnectionAlgebraicSpinCurrentCoefficient source actual
          (canonicalLorentzTemporalBivectorOneForm component)
          (canonicalCauchySlicePoint time space) -
        lorentzConnectionSpatialBFMomentumDivergence actual
          (canonicalLorentzTemporalBivectorOneForm component)
          (canonicalCauchySlicePoint time space) := by
  exact lorentzTemporalGaussResidual_eq_algebraic_sub_spatial
    source actual (canonicalCauchySlicePoint time space) component

end

end
  SaturationMonoid.PhysicsCore.StageNineLorentzTemporalGaussResidualTangency
