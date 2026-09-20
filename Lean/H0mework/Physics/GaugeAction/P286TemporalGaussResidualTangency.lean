import H0mework.Physics.Cauchy.CanonicalCauchyState
import H0mework.Physics.Cauchy.P286ActionCauchySplit

/-!
# Stage-9 P286 temporal-Gauss residual and time trace

Canonical P286 Gauss is a zero-fiber condition on the temporal connection
tests.  This module exposes that residual without assuming smoothness and
without selecting a repair, endpoint, quotient representative, or source
certificate:

```text
G(U, x)(c) =
  J_A(U, x; dt ⊗ c) - div_space P_B(U, x; dt ⊗ c).
```

The time trace below only reads this residual on one already constructed
actual.  A later `HasDerivAt` theorem can therefore state genuine zero-fiber
tangency without relying on the totalized value of `deriv` or `fderiv`.
This file contains no producer and no tangency claim.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP286TemporalGaussResidualTangency

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionPointwiseEquation

noncomputable section

set_option autoImplicit false

/-- Full finite P286 temporal-Gauss residual carrier.  Its argument is an
actual P286 coordinate, not a chosen basis label or a stored Boolean. -/
abbrev P286TemporalGaussResidualCarrier :=
  P286CoordinateCarrier → ℝ

/-- Pointwise temporal-Gauss residual of one already generated actual. -/
def p286TemporalGaussResidualAt
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    P286TemporalGaussResidualCarrier :=
  fun component =>
    p286GaugeConnectionAlgebraicCurrentCoefficient source actual
        (p286TemporalGaugeOneForm component) point -
      p286GaugeConnectionSpatialBFMomentumDivergence actual
        (p286TemporalGaugeOneForm component) point

@[simp] theorem p286TemporalGaussResidualAt_apply
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (component : P286CoordinateCarrier) :
    p286TemporalGaussResidualAt source actual point component =
      p286GaugeConnectionAlgebraicCurrentCoefficient source actual
          (p286TemporalGaugeOneForm component) point -
        p286GaugeConnectionSpatialBFMomentumDivergence actual
          (p286TemporalGaugeOneForm component) point :=
  rfl

/-- The residual has exactly the canonical Gauss zero fiber.  This is an
extensional identity of the full carrier, not a selected-coordinate test. -/
theorem p286TemporalGaussResidualAt_eq_zero_iff
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    p286TemporalGaussResidualAt source actual point = 0 ↔
      CanonicalP286GaugeGaussConstraintAt source actual point := by
  constructor
  · intro residualZero component
    have componentZero := congrFun residualZero component
    simpa [p286TemporalGaussResidualAt, sub_eq_zero] using componentZero
  · intro gauss
    funext component
    simpa [p286TemporalGaussResidualAt, sub_eq_zero] using gauss component

/-- Restriction of one residual component to the canonical time line through
one spatial contact.  It remains a readout of the same actual. -/
def p286TemporalGaussResidualTimeTrace
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (component : P286CoordinateCarrier)
    (time : ℝ) : ℝ :=
  p286TemporalGaussResidualAt source actual
    (canonicalCauchySlicePoint time space) component

@[simp] theorem p286TemporalGaussResidualTimeTrace_apply
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (component : P286CoordinateCarrier)
    (time : ℝ) :
    p286TemporalGaussResidualTimeTrace source actual space component time =
      p286GaugeConnectionAlgebraicCurrentCoefficient source actual
          (p286TemporalGaugeOneForm component)
          (canonicalCauchySlicePoint time space) -
        p286GaugeConnectionSpatialBFMomentumDivergence actual
          (p286TemporalGaugeOneForm component)
          (canonicalCauchySlicePoint time space) :=
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineP286TemporalGaussResidualTangency
