import H0mework.Physics.Matter.GeneratedMatter
import H0mework.Physics.Geometry.JointStateLiftDefect

/-!
# S9-C3h14: direct Stage-8 matter first-jet transport no-go

This module audits the whole class of Stage-9 configurations that directly
identify the actual Stage-8 matter source value and four finite target
differences with the continuum matter value and first directional derivatives
at the origin.  It imposes no affine or higher-jet ansatz.

Every member of this class has the same actual conjugate-matter residual `1`
on a canonical probe direction.  Hence it cannot close the pointwise joint
shell.  More importantly for the framework root, any update whose two
endpoints both retain this direct identification leaves that residual fixed,
while the active source keep requires `r' = K r`; the full transport square
cannot commute.

This rejects only the direct finite-difference/continuum-first-jet bridge.  It
does not empty the matter shell, use stationarity or a zero fiber to construct
an update, prescribe a replacement bridge, or authorize new source data.
-/

namespace SaturationMonoid.PhysicsCore.StageNineStageEightMatterFirstJetTransportNoGo

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageEightSourceGeneratedMatter
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellResidualTransportRoot
open StageNineJointStateLiftDefect
open StageNineConjugateMatterVariation
open StageNineMatterVariation
open StageNineP286GaugeConnectionVariationDensity
open DiracExteriorMatterAction
open DiracExteriorMatterLocalGaugeLink
open DiracCliffordRepresentation

noncomputable section

set_option autoImplicit false

/-- Exact direct-identification class under audit.  It stores no equation,
stationarity receipt, transport certificate, or higher-jet choice. -/
structure MatchesPositiveStageEightMatterFirstJetAtOrigin
    (configuration : StageNineHolonomicConfiguration) : Prop where
  coframeOrigin : configuration.coframe 0 = 1
  matterOrigin : configuration.matter 0 =
    (sourceGeneratedMatterJet canonicalSource).sourceField
  matterFirstJet : ∀ direction : LorentzianIndex,
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (configuration.matter point))
        0 direction =
      matterCoordinateEquiv
        ((sourceGeneratedMatterJet canonicalSource).targetField direction -
          (sourceGeneratedMatterJet canonicalSource).sourceField)

/-- On the direct-identification class, both primitive connection actions
vanish at the zero source value, so the actual covariant derivative is the
finite target field itself. -/
theorem matchingFirstJet_matterCovariantDerivative_origin
    (configuration : StageNineHolonomicConfiguration)
    (matching : MatchesPositiveStageEightMatterFirstJetAtOrigin configuration)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative configuration 0 direction =
      (sourceGeneratedMatterJet canonicalSource).targetField direction := by
  unfold holonomicMatterCovariantDerivative
  rw [matching.matterOrigin, matching.matterFirstJet]
  simp [sourceGeneratedMatterJet]

/-- The direct first jet forces a fixed nonzero Dirac--Yukawa vector at the
origin, independently of higher jets and of both primitive connections. -/
theorem matchingFirstJet_generatedContinuumMatterVector_origin
    (configuration : StageNineHolonomicConfiguration)
    (matching : MatchesPositiveStageEightMatterFirstJetAtOrigin configuration) :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField configuration 0) =
      Complex.I • diracSpinZeroMatterProbe := by
  unfold generatedContinuumMatterVector
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart, matterFrameRelative_zeroChart]
  rw [matching.coframeOrigin]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl]
  simp_rw [matchingFirstJet_matterCovariantDerivative_origin
    configuration matching]
  rw [matching.matterOrigin]
  simp [positiveSmoothUnifiedSource, sourceGeneratedMatterJet,
    sourceMatterAmplitude, inverseCoframeDiracGamma_identity,
    Fin.sum_univ_four, diracGamma,
    show (1 : LorentzianIndex) ≠ 0 by decide,
    show (2 : LorentzianIndex) ≠ 0 by decide,
    show (3 : LorentzianIndex) ≠ 0 by decide,
    diracGammaZero_maps_spinTwoProbe]

def positiveFirstJetConjugateResidualProbeDirection :
    MatterCoordinateCarrier :=
  matterDualCoordinates
    ((-Complex.I) • diracSpinZeroMatterCoordinate)

theorem matchingFirstJet_conjugateResidual_origin_eq_one
    (configuration : StageNineHolonomicConfiguration)
    (matching : MatchesPositiveStageEightMatterFirstJetAtOrigin configuration) :
    conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        configuration positiveFirstJetConjugateResidualProbeDirection 0 = 1 := by
  unfold conjugateMatterDirectionalCoefficient
  rw [matchingFirstJet_generatedContinuumMatterVector_origin
    configuration matching]
  unfold positiveFirstJetConjugateResidualProbeDirection
  rw [matterDualOfCoordinates_surjective]
  simp [generatedVolumeDensity, toContinuumPointField,
    matching.coframeOrigin]

/-- Direct finite-to-first-jet identification cannot close the actual
pointwise joint shell at the source endpoint.  This is a judgment on the
declared class, never a premise used to choose a configuration. -/
theorem matchingFirstJet_not_pointwiseJointZeroFiber
    (configuration : StageNineHolonomicConfiguration)
    (matching : MatchesPositiveStageEightMatterFirstJetAtOrigin configuration) :
    ¬ OnCurrentPointwiseJointShellZeroFiber positiveSmoothUnifiedSource
      configuration 0 := by
  intro jointZero
  have eulerZero := congrArg
    CurrentPointwiseJointShellResidualCarrier.eulerLagrange jointZero
  have conjugateZero := congrArg
    CurrentPointwiseEulerLagrangeResidualCarrier.conjugateMatter eulerZero
  have atProbe := congrFun conjugateZero
    positiveFirstJetConjugateResidualProbeDirection
  change conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
    configuration positiveFirstJetConjugateResidualProbeDirection 0 = 0
      at atProbe
  rw [matchingFirstJet_conjugateResidual_origin_eq_one configuration matching]
      at atProbe
  norm_num at atProbe

/-- Root-law version: if both endpoints retain the direct Stage-8 first-jet
identification, their conjugate residual stays `1`; active `K` transport
requires it to move, so no such update lifts `R(Ux)=K(Rx)`. -/
theorem matchingFirstJetPair_not_fullJointTransport
    (initial terminal : StageNineHolonomicConfiguration)
    (initialMatching :
      MatchesPositiveStageEightMatterFirstJetAtOrigin initial)
    (terminalMatching :
      MatchesPositiveStageEightMatterFirstJetAtOrigin terminal)
    (update : CurrentJointShellStateUpdate)
    (updateInitial : update initial = terminal) :
    ¬ CurrentJointShellResidualTransportLiftAt
      positiveSmoothUnifiedSource update initial := by
  intro lift
  have pointLift := congrFun lift 0
  have conjugateLift := congrArg
    (fun residual : CurrentPointwiseJointShellResidualCarrier =>
      residual.eulerLagrange.conjugateMatter
        positiveFirstJetConjugateResidualProbeDirection) pointLift
  rw [updateInitial] at conjugateLift
  change
    conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        terminal positiveFirstJetConjugateResidualProbeDirection 0 =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) *
        conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
          initial positiveFirstJetConjugateResidualProbeDirection 0
      at conjugateLift
  rw [matchingFirstJet_conjugateResidual_origin_eq_one terminal terminalMatching,
    matchingFirstJet_conjugateResidual_origin_eq_one initial initialMatching]
      at conjugateLift
  linarith [positiveSmoothUnifiedSource.legacy.sigma_pos]

end

end SaturationMonoid.PhysicsCore.StageNineStageEightMatterFirstJetTransportNoGo
