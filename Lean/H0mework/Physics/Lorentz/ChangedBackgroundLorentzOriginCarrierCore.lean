import H0mework.Physics.Gauge.ConnectionSectorSourceBalance
import H0mework.Physics.GravitySource.NormalizedAffineConnectionGerm

/-!
# Dependency-light changed-background Lorentz origin carrier

This module contains only the deterministic normalized-affine connection
installer and the exact response channels that are insensitive to that
connection replacement.  It does not classify a response fiber, accept a
target residual, choose an inverse image, or assert a zero-fiber theorem.

The declarations retain their historical namespace so the C3h75 diagnostic
classifier and later source/action producers consume one implementation.
-/

namespace SaturationMonoid.PhysicsCore.StageNineChangedBackgroundLorentzOriginResponseFiber

open ProofFreeRicherAnholonomicSource
open StageNineConnectionSectorSourceBalance
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Actual fixed-background origin carrier -/

/-- The normalized-affine connection carrier with origin value `q` and
target curvature read from the supplied background actual. -/
def changedBackgroundLorentzOriginConnection
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm) : LorentzConnectionField :=
  normalizedAffineLorentzConnectionField
    (lorentzSkewConnectionOfBivectorOneForm q)
    (holonomicGravityCurvature configuration 0)

/-- Replace only the primitive Lorentz connection field. -/
def changedBackgroundLorentzOriginCarrier
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm) : StageNineHolonomicConfiguration :=
  { configuration with
    gravityConnection := changedBackgroundLorentzOriginConnection
      configuration q }

@[simp] theorem changedBackgroundLorentzOriginCarrier_coframe
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm) :
    (changedBackgroundLorentzOriginCarrier configuration q).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem changedBackgroundLorentzOriginCarrier_gravityAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm) :
    (changedBackgroundLorentzOriginCarrier configuration q).gravityAuxiliary =
      configuration.gravityAuxiliary :=
  rfl

@[simp] theorem changedBackgroundLorentzOriginCarrier_matter
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm) :
    (changedBackgroundLorentzOriginCarrier configuration q).matter =
      configuration.matter :=
  rfl

@[simp] theorem changedBackgroundLorentzOriginCarrier_conjugateMatter
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm) :
    (changedBackgroundLorentzOriginCarrier configuration q).conjugateMatter =
      configuration.conjugateMatter :=
  rfl

@[simp] theorem changedBackgroundLorentzOriginConnection_origin
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm) :
    changedBackgroundLorentzOriginConnection configuration q 0 =
      lorentzSkewConnectionOfBivectorOneForm q :=
  normalizedAffineLorentzConnectionField_zero _ _

@[simp] theorem changedBackgroundLorentzOriginCarrier_connection_origin
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm) :
    (changedBackgroundLorentzOriginCarrier configuration q).gravityConnection
        0 =
      lorentzSkewConnectionOfBivectorOneForm q :=
  changedBackgroundLorentzOriginConnection_origin configuration q

/-- The representative connection field is smooth for every coordinate. -/
theorem changedBackgroundLorentzOriginConnection_smooth
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm) :
    SmoothLorentzConnectionField
      (changedBackgroundLorentzOriginConnection configuration q) :=
  normalizedAffineLorentzConnectionField_smooth _ _

/-- The representative connection remains Lorentz-skew at every point. -/
theorem changedBackgroundLorentzOriginConnection_lorentzSkew
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm)
    (point : BasePoint) :
    LorentzSkew
      (changedBackgroundLorentzOriginConnection configuration q point) := by
  exact normalizedAffineLorentzConnectionField_lorentzSkew _ _
    (lorentzSkewConnectionOfBivectorOneForm_lorentzSkew q) point

/-- The actual `dω + ω∧ω` readout retains the supplied background
curvature at the common origin; no curvature receipt is stored in the carrier. -/
theorem changedBackgroundLorentzOriginCarrier_curvature_origin
    (configuration : StageNineHolonomicConfiguration)
    (q : LorentzBivectorOneForm) :
    holonomicGravityCurvature
        (changedBackgroundLorentzOriginCarrier configuration q) 0 =
      holonomicGravityCurvature configuration 0 := by
  change holonomicGravityCurvature
      (normalizedAffineConfiguration
        (lorentzSkewConnectionOfBivectorOneForm q)
        (holonomicGravityCurvature configuration 0)) 0 =
    holonomicGravityCurvature configuration 0
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

/-! ## Exact connection-insensitive response transport -/

theorem changedBackgroundLorentzCarrier_spinResponse_eq_background
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (q direction : LorentzBivectorOneForm) :
    lorentzMatterSpinSourceCoefficient source
        (changedBackgroundLorentzOriginCarrier configuration q) direction 0 =
      lorentzMatterSpinSourceCoefficient source configuration direction 0 := by
  unfold lorentzMatterSpinSourceCoefficient generatedVolumeDensity
    toContinuumPointField holonomicMatterLorentzConnectionVariation
  rfl

theorem changedBackgroundLorentzCarrier_divergenceResponse_eq_background
    (configuration : StageNineHolonomicConfiguration)
    (q direction : LorentzBivectorOneForm) :
    lorentzConnectionBFDifferentialMomentumDivergence
        (changedBackgroundLorentzOriginCarrier configuration q) direction 0 =
      lorentzConnectionBFDifferentialMomentumDivergence configuration
        direction 0 := by
  unfold lorentzConnectionBFDifferentialMomentumDivergence
    lorentzConnectionBFDifferentialMomentum generatedVolumeDensity
    toContinuumPointField
  rfl

end

end SaturationMonoid.PhysicsCore.StageNineChangedBackgroundLorentzOriginResponseFiber
