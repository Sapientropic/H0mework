import H0mework.Physics.Exterior.FullSynchronizedActionResponseOperator
import H0mework.Physics.ConnectionJets.CurrentP286CompleteActionResponseFirstJet

/-!
# Stage-9 full synchronized complete P286 action-response operator

This module composes two already action-generated actual operators in their
dependency order:

```text
(source, current actual)
→ full synchronized action response
→ current-action complete P286 auxiliary response
→ one composed whole actual.
```

The outer P286 operator is faithful only at the distinguished origin relative
to the intermediate full synchronized actual.  The composition is therefore
not claimed to preserve the input actual, a whole Cauchy slice, or a whole
history.  In particular, this constructor is not a fixed-point theorem,
restart map, time-update law, flow, or semigroup action.

The canonical Cauchy path below is only the restriction of the already
generated composed actual.  It does not reconstruct that actual from
residual fields and it does not assert Cauchy fidelity to the input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFullSynchronizedCompleteP286ActionResponseOperator

open StageNineCanonicalCauchyState
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

/-! ## Action-first whole-actual composition -/

/-- Apply the complete P286 response only after the full synchronized actual
has been generated from the same proof-free source and current actual. -/
def fullSynchronizedCompleteP286ActionResponseOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  currentP286CompleteActionResponseOperator source
    (fullSynchronizedActionResponseOperator source current)

/-- The outer P286 update preserves the origin point field of the intermediate
full synchronized actual.  No input-current or whole-slice fidelity is
asserted. -/
theorem
    fullSynchronizedCompleteP286ActionResponseOperator_pointField_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    toContinuumPointField
        (fullSynchronizedCompleteP286ActionResponseOperator source current) 0 =
      toContinuumPointField
        (fullSynchronizedActionResponseOperator source current) 0 := by
  exact
    currentP286CompleteActionResponseOperator_pointField_origin source
      (fullSynchronizedActionResponseOperator source current)

/-- The P286 action current at the common origin is read from the intermediate
full synchronized actual that generated the outer response. -/
theorem
    fullSynchronizedCompleteP286ActionResponseOperator_actionCurrent_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source
        (fullSynchronizedCompleteP286ActionResponseOperator source current)
        direction 0 =
      currentP286FullActionTarget source
        (fullSynchronizedActionResponseOperator source current) direction := by
  exact
    currentP286CompleteActionResponseOperator_actionCurrent_origin source
      (fullSynchronizedActionResponseOperator source current) direction

/-! ## Canonical restriction of the generated actual -/

/-- The canonical Cauchy path of the already generated composed actual. -/
def fullSynchronizedCompleteP286CanonicalCauchyPath
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ) :
    StageNineCauchyState :=
  canonicalCauchyRestriction time
    (fullSynchronizedCompleteP286ActionResponseOperator source current)

@[simp] theorem fullSynchronizedCompleteP286CanonicalCauchyPath_apply
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ) :
    fullSynchronizedCompleteP286CanonicalCauchyPath source current time =
      canonicalCauchyRestriction time
        (fullSynchronizedCompleteP286ActionResponseOperator source current) :=
  rfl

/-- At time zero the path is exactly the time-zero restriction of its own
generated actual; this is not a fidelity statement about the input current. -/
theorem fullSynchronizedCompleteP286CanonicalCauchyPath_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    fullSynchronizedCompleteP286CanonicalCauchyPath source current 0 =
      canonicalCauchyRestriction 0
        (fullSynchronizedCompleteP286ActionResponseOperator source current) :=
  rfl

/-! ## Forward first-jet response of the composed actual -/

/-- Under the fixed identity-coframe principal on the intermediate actual,
the composed actual has the generated temporal BF response. -/
theorem
    fullSynchronizedCompleteP286ActionResponseOperator_temporalBFMomentumResponse
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne :
      ∀ point,
        (fullSynchronizedActionResponseOperator source current).coframe point =
          1)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionTemporalBFMomentumDerivative
        (fullSynchronizedCompleteP286ActionResponseOperator source current)
        direction 0 =
      currentP286SpatialActionTarget source
        (fullSynchronizedActionResponseOperator source current)
        (fun index => direction index.succ) := by
  exact
    currentP286CompleteActionResponseOperator_temporalBFMomentumResponse
      source (fullSynchronizedActionResponseOperator source current)
      coframeOne direction

/-- Under the same principal, the composed actual has the generated spatial
Gauss response. -/
theorem
    fullSynchronizedCompleteP286ActionResponseOperator_spatialBFMomentumResponse
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne :
      ∀ point,
        (fullSynchronizedActionResponseOperator source current).coframe point =
          1)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        (fullSynchronizedCompleteP286ActionResponseOperator source current)
        direction 0 =
      currentP286TemporalActionTarget source
        (fullSynchronizedActionResponseOperator source current)
        (direction canonicalLorentzianTimeDirection) := by
  exact
    currentP286CompleteActionResponseOperator_spatialBFMomentumResponse
      source (fullSynchronizedActionResponseOperator source current)
      coframeOne direction

/-- Re-substitution of the response generated from the intermediate action
dual is producer consistency, not a new constraint or a stationarity receipt. -/
theorem
    fullSynchronizedCompleteP286ActionResponseOperator_connectionProducerConsistency
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne :
      ∀ point,
        (fullSynchronizedActionResponseOperator source current).coframe point =
          1)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient source
        (fullSynchronizedCompleteP286ActionResponseOperator source current)
        direction 0 =
      0 := by
  exact
    currentP286CompleteActionResponseOperator_connectionEquation_origin
      source (fullSynchronizedActionResponseOperator source current)
      coframeOne direction

end

end
  SaturationMonoid.PhysicsCore.StageNineFullSynchronizedCompleteP286ActionResponseOperator
