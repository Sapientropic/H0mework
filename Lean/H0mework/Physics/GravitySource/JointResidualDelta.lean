import H0mework.Physics.GravitySource.NormalizedAffineConnectionGerm

/-!
# S9-C3g7e: induced joint-residual delta of the normalized gravity mouth

Residual transport is upstream of every configuration realization:

`r' = K r`, `r = K r + (I-K) r`, and
`trace = (I-K) r`.

C3g7c subsequently installs a source-derived normalized affine Lorentz
connection.  This module audits that downstream operation against the complete
nine-coordinate current joint-shell residual.  Four coordinates are
definitionally unchanged.  The full readout delta is supported on five typed
connection-sensitive coordinates, without claiming that all five are nonzero
for every prior configuration.

The gravity-auxiliary coordinate is exact:
`ΔR_B = F_after - F_before`.  If the prior configuration actually realizes
the old positive-source curvature, C3g6b's already forced split gives
`ΔR_B = -trace ≠ 0`.  Thus responsibility is transported into the
configuration readout rather than disappearing into a third sink.

This remains a readout/support checkpoint.  It is not a new residual source,
does not make the configuration lift a premise of residual transport, and
does not assert a full source template, joint stationarity, global extension,
or terminal zero fiber.
-/

namespace SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthJointResidualDelta

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineBlockwiseConstitutive
open StageNineGravityAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineScalarPointwiseEquation
open StageNineMatterPointwiseEquation
open StageNineConjugateMatterVariation
open StageNineCoframeLocalDifferentiability
open StageNineJointShellResidualCarrier
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNinePositiveSourceGravityMouthSpinOrbitCarrier
open StageNinePositiveSourceGravityMouthTransportCurvature

noncomputable section

set_option autoImplicit false

abbrev CurrentSmoothUnifiedSource :=
  StageNineJointShellResidualCarrier.CurrentSmoothUnifiedSource

def installedConfiguration
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installPositiveSourceGravityMouthNormalizedAffineConnection configuration

/-- The nine-channel pointwise delta `installed residual - prior residual`,
stored in the already-typed joint residual carrier.  No equation witness is
stored in this definition. -/
def installedJointResidualDelta
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : CurrentPointwiseJointShellResidualCarrier where
  algebraic :=
    { gravitySimplicity :=
        (currentPointwiseJointShellResidual source
            (installedConfiguration configuration) point).algebraic.gravitySimplicity -
          (currentPointwiseJointShellResidual source configuration
            point).algebraic.gravitySimplicity
      gravityAuxiliary :=
        (currentPointwiseJointShellResidual source
            (installedConfiguration configuration) point).algebraic.gravityAuxiliary -
          (currentPointwiseJointShellResidual source configuration
            point).algebraic.gravityAuxiliary
      p286GaugeAuxiliary :=
        (currentPointwiseJointShellResidual source
            (installedConfiguration configuration) point).algebraic.p286GaugeAuxiliary -
          (currentPointwiseJointShellResidual source configuration
            point).algebraic.p286GaugeAuxiliary }
  eulerLagrange :=
    { lorentzConnection := fun direction =>
        (currentPointwiseJointShellResidual source
            (installedConfiguration configuration) point).eulerLagrange.lorentzConnection direction -
          (currentPointwiseJointShellResidual source configuration
            point).eulerLagrange.lorentzConnection direction
      p286GaugeConnection := fun direction =>
        (currentPointwiseJointShellResidual source
            (installedConfiguration configuration) point).eulerLagrange.p286GaugeConnection direction -
          (currentPointwiseJointShellResidual source configuration
            point).eulerLagrange.p286GaugeConnection direction
      scalar := fun direction =>
        (currentPointwiseJointShellResidual source
            (installedConfiguration configuration) point).eulerLagrange.scalar direction -
          (currentPointwiseJointShellResidual source configuration
            point).eulerLagrange.scalar direction
      matter := fun direction =>
        (currentPointwiseJointShellResidual source
            (installedConfiguration configuration) point).eulerLagrange.matter direction -
          (currentPointwiseJointShellResidual source configuration
            point).eulerLagrange.matter direction
      conjugateMatter := fun direction =>
        (currentPointwiseJointShellResidual source
            (installedConfiguration configuration) point).eulerLagrange.conjugateMatter direction -
          (currentPointwiseJointShellResidual source configuration
            point).eulerLagrange.conjugateMatter direction
      coframe :=
        (currentPointwiseJointShellResidual source
            (installedConfiguration configuration) point).eulerLagrange.coframe -
          (currentPointwiseJointShellResidual source configuration
            point).eulerLagrange.coframe }

theorem installed_toContinuumPointField_primitive_readouts
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    let before := toContinuumPointField configuration point
    let after := toContinuumPointField (installedConfiguration configuration) point
    after.coframe = before.coframe ∧
      after.gravityAuxiliary = before.gravityAuxiliary ∧
      after.gravitySimplicityMultiplier = before.gravitySimplicityMultiplier ∧
      after.gaugeCurvature = before.gaugeCurvature ∧
      after.gaugeAuxiliary = before.gaugeAuxiliary ∧
      after.scalar = before.scalar ∧
      after.scalarCovariantDerivative = before.scalarCovariantDerivative ∧
      after.matter = before.matter ∧
      after.conjugateMatter = before.conjugateMatter := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact derived-jet boundary: changing the primitive Lorentz connection can
flow into the continuum point field only through actual gravity curvature and
the matter covariant derivative. -/
theorem installed_toContinuumPointField_eq_twoJetUpdate
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    toContinuumPointField (installedConfiguration configuration) point =
      { toContinuumPointField configuration point with
        gravityCurvature :=
          holonomicGravityCurvature (installedConfiguration configuration) point
        matterCovariantDerivative :=
          holonomicMatterCovariantDerivative
            (installedConfiguration configuration) point } := by
  rfl

theorem installed_matterCovariantDerivative_eq_of_connection_eq
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (connectionAtPoint : configuration.gravityConnection point =
      positiveSourceGravityMouthNormalizedAffineConnectionField point) :
    holonomicMatterCovariantDerivative
        (installedConfiguration configuration) point =
      holonomicMatterCovariantDerivative configuration point := by
  unfold holonomicMatterCovariantDerivative installedConfiguration
    installPositiveSourceGravityMouthNormalizedAffineConnection
  rw [connectionAtPoint]

theorem installed_gravitySimplicity_unchanged
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentPointwiseJointShellResidual source
        (installedConfiguration configuration) point).algebraic.gravitySimplicity =
      (currentPointwiseJointShellResidual source configuration
        point).algebraic.gravitySimplicity := by
  rfl

theorem installed_gravitySimplicity_delta_zero
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (installedJointResidualDelta source configuration point).algebraic.gravitySimplicity = 0 := by
  change _ - _ = 0
  rw [installed_gravitySimplicity_unchanged]
  exact sub_self _

theorem installed_p286GaugeAuxiliary_unchanged
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentPointwiseJointShellResidual source
        (installedConfiguration configuration) point).algebraic.p286GaugeAuxiliary =
      (currentPointwiseJointShellResidual source configuration
        point).algebraic.p286GaugeAuxiliary := by
  rfl

theorem installed_p286GaugeAuxiliary_delta_zero
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (installedJointResidualDelta source configuration point).algebraic.p286GaugeAuxiliary = 0 := by
  change _ - _ = 0
  rw [installed_p286GaugeAuxiliary_unchanged]
  exact sub_self _

theorem installed_p286GaugeConnection_unchanged
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentPointwiseJointShellResidual source
        (installedConfiguration configuration) point).eulerLagrange.p286GaugeConnection =
      (currentPointwiseJointShellResidual source configuration
        point).eulerLagrange.p286GaugeConnection := by
  funext direction
  rfl

theorem installed_p286GaugeConnection_delta_zero
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (installedJointResidualDelta source configuration point).eulerLagrange.p286GaugeConnection = 0 := by
  funext direction
  change _ - _ = 0
  rw [congrFun (installed_p286GaugeConnection_unchanged source configuration point)
    direction]
  exact sub_self _

/-- This is stronger than preservation of only the scalar-potential term:
the current scalar EL channel as a whole is independent of the primitive
Lorentz connection. -/
theorem installed_scalar_unchanged
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentPointwiseJointShellResidual source
        (installedConfiguration configuration) point).eulerLagrange.scalar =
      (currentPointwiseJointShellResidual source configuration
        point).eulerLagrange.scalar := by
  funext direction
  rfl

theorem installed_scalar_delta_zero
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (installedJointResidualDelta source configuration point).eulerLagrange.scalar = 0 := by
  funext direction
  change _ - _ = 0
  rw [congrFun (installed_scalar_unchanged source configuration point) direction]
  exact sub_self _

/-- The five residual coordinates not definitionally protected by changing
only the primitive Lorentz connection.  The word `sensitive` does not assert
that each delta is nonzero for every prior configuration. -/
structure InstalledGravityConnectionSensitiveResidualDeltaCarrier where
  gravityAuxiliary : PhysicalBivector
  lorentzConnection : LorentzBivectorOneForm → ℝ
  matter : MatterCoordinateCarrier → ℝ
  conjugateMatter : MatterCoordinateCarrier → ℝ
  coframe : LorentzianCoframe →L[ℝ] ℝ

def installedSensitiveResidualDelta
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    InstalledGravityConnectionSensitiveResidualDeltaCarrier where
  gravityAuxiliary :=
    (installedJointResidualDelta source configuration point).algebraic.gravityAuxiliary
  lorentzConnection :=
    (installedJointResidualDelta source configuration point).eulerLagrange.lorentzConnection
  matter :=
    (installedJointResidualDelta source configuration point).eulerLagrange.matter
  conjugateMatter :=
    (installedJointResidualDelta source configuration point).eulerLagrange.conjugateMatter
  coframe :=
    (installedJointResidualDelta source configuration point).eulerLagrange.coframe

def embedInstalledSensitiveResidualDelta
    (delta : InstalledGravityConnectionSensitiveResidualDeltaCarrier) :
    CurrentPointwiseJointShellResidualCarrier where
  algebraic :=
    { gravitySimplicity := 0
      gravityAuxiliary := delta.gravityAuxiliary
      p286GaugeAuxiliary := 0 }
  eulerLagrange :=
    { lorentzConnection := delta.lorentzConnection
      p286GaugeConnection := 0
      scalar := 0
      matter := delta.matter
      conjugateMatter := delta.conjugateMatter
      coframe := delta.coframe }

/-- The full nine-channel delta is supported on exactly the five typed
connection-sensitive coordinates; this is a support/readout theorem, not a
claim that those five values are all nonzero. -/
theorem installedJointResidualDelta_eq_embed_sensitive
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    installedJointResidualDelta source configuration point =
      embedInstalledSensitiveResidualDelta
        (installedSensitiveResidualDelta source configuration point) := by
  apply CurrentPointwiseJointShellResidualCarrier.ext
  · apply CurrentPointwiseAlgebraicResidualCarrier.ext
    · exact installed_gravitySimplicity_delta_zero source configuration point
    · rfl
    · exact installed_p286GaugeAuxiliary_delta_zero source configuration point
  · apply CurrentPointwiseEulerLagrangeResidualCarrier.ext
    · rfl
    · exact installed_p286GaugeConnection_delta_zero source configuration point
    · exact installed_scalar_delta_zero source configuration point
    · rfl
    · rfl
    · rfl

theorem installed_gravityAuxiliary_delta_eq_curvature_delta
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (installedJointResidualDelta source configuration point).algebraic.gravityAuxiliary =
      holonomicGravityCurvature (installedConfiguration configuration) point -
        holonomicGravityCurvature configuration point := by
  change
    (holonomicGravityCurvature (installedConfiguration configuration) point -
        gravityInternalDualEquiv (configuration.gravityAuxiliary point)) -
      (holonomicGravityCurvature configuration point -
        gravityInternalDualEquiv (configuration.gravityAuxiliary point)) = _
  abel

theorem installed_gravityAuxiliary_delta_origin
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (installedJointResidualDelta source configuration 0).algebraic.gravityAuxiliary =
      positiveSourceGravityMouthRequiredCurvature -
        holonomicGravityCurvature configuration 0 := by
  rw [installed_gravityAuxiliary_delta_eq_curvature_delta]
  exact congrArg
    (fun curvature => curvature - holonomicGravityCurvature configuration 0)
    (installPositiveSourceGravityMouthNormalizedAffineConnection_curvature_origin
      configuration)

/-- If the prior configuration really realizes the old positive-source
curvature, the installation delta is exactly the negative of the already
forced Layer-1 trace.  This reads responsibility into the configuration
delta; it does not make the configuration lift a premise of residual
transport. -/
theorem installed_gravityAuxiliary_delta_eq_neg_forcedTrace
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (priorCurvature : holonomicGravityCurvature configuration 0 =
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin) :
    (installedJointResidualDelta source configuration 0).algebraic.gravityAuxiliary =
      - (linearResidualTrace
          positiveSourceGravityMouthSpinOrbitResponsibilityKeep
          carriedPositiveSourceGravityMouthSpinOrbitObstruction).1 := by
  rw [installed_gravityAuxiliary_delta_origin, priorCurvature,
    positiveSourceGravityMouthSourceCurvature_eq_required_add_trace]
  abel

theorem installed_gravityAuxiliary_delta_ne_zero_of_priorSourceCurvature
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (priorCurvature : holonomicGravityCurvature configuration 0 =
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin) :
    (installedJointResidualDelta source configuration 0).algebraic.gravityAuxiliary ≠ 0 := by
  rw [installed_gravityAuxiliary_delta_eq_neg_forcedTrace source configuration
    priorCurvature]
  apply neg_ne_zero.mpr
  intro traceValueZero
  apply carriedPositiveSourceGravityMouthSpinOrbitObstruction_trace_ne_zero
  apply Subtype.ext
  exact traceValueZero

end

end SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthJointResidualDelta
