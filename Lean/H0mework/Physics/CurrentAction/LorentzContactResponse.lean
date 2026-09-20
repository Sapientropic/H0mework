import H0mework.Physics.CurrentAction.LorentzStateResponse

/-!
# Stage-9 complete full-action response at one canonical contact

The C3h198 whole-slice law assumes an identity coframe at every spatial
contact.  A source-generated spatial profile need not satisfy that global
restriction even when its canonical origin is exactly the identity coframe.
This module extracts the honest contact-local authority:

```text
(source, current, contact with e = 1)
→ current-state full-action local actual
→ complete ten-field origin tangent
→ Lorentz/P286/primal/adjoint action responses at that same contact.
```

The current is retained as a whole spatial field.  In particular, this
interface does not constantize it and therefore does not erase spatial
derivatives used by the Lorentz BF-momentum action.  It is a response law, not
a flow, a constraint-propagation receipt, or a temporal-Gauss certificate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzContactResponse

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionPointwiseEquation
open StageNineMatterActionTimeVelocity
open StageNineConjugateMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-- Contact-local C3h198 authority.  The identity-coframe assumption is made
only at the selected contact; the rest of the current remains untouched. -/
structure StageNineCurrentCanonicalFullActionLorentzContactResponseLaw
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) : Prop where
  identityCoframeAt : current.coframe space = 1
  localActualGenerated :
    currentCanonicalFullActionLorentzActualFirstJetLift source current space =
      { currentCanonicalGravityPreservingActual source current space with
        gravityAuxiliary := fun point =>
          (currentCanonicalGravityPreservingActual source current
            space).gravityAuxiliary point +
          localBaseCoordinate canonicalLorentzianTimeDirection point •
            currentCanonicalFullActionLorentzAuxiliaryVelocity source current
              space }
  localActualSmooth :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
      space).Smooth
  localActualNondegenerate :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
      space).Nondegenerate
  localPathGenerated : forall time,
    currentCanonicalFullActionLorentzStateResponseLocalPath source current
        space time =
      canonicalCauchyRestriction time
        (currentCanonicalFullActionLorentzActualFirstJetLift source current
          space)
  coframeTimeJet : forall internal coordinate,
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source current
            time).coframe space internal coordinate)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).coframe internal coordinate
  gravityConnectionTimeJet : forall formDirection internalPair,
    deriv
        (fun time : Real =>
          loweredLorentzConnectionCoefficient
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).gravityConnection space)
            formDirection internalPair)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).gravityConnection formDirection internalPair
  gravityAuxiliaryTimeJet : forall internalPair spacetimePair,
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source current
            time).gravityAuxiliary space internalPair spacetimePair)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).gravityAuxiliary internalPair spacetimePair
  multiplierTimeJet : forall internalPair spacetimePair,
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source current
            time).gravitySimplicityMultiplier space internalPair
              spacetimePair)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).gravitySimplicityMultiplier internalPair spacetimePair
  p286ConnectionTimeJet : forall formDirection,
    deriv
        (fun time : Real =>
          p286CoordinateEquiv
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).gaugeConnection space formDirection))
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).p286Connection formDirection
  p286AuxiliaryTimeJet : forall pair,
    deriv
        (fun time : Real =>
          p286CoordinateEquiv
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).gaugeAuxiliary space pair))
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).p286Auxiliary pair
  scalarTimeJet :
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source current
            time).scalar space)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).scalar
  scalarVelocityTimeJet :
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source current
            time).scalarVelocity space)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).scalarVelocity
  matterTimeJet :
    deriv
        (fun time : Real =>
          matterCoordinateEquiv
            ((currentCanonicalFullActionLorentzStateResponseUpdate source
              current time).matter space))
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).matter
  conjugateMatterTimeJet : forall matter,
    deriv
        (fun time : Real =>
          (currentCanonicalFullActionLorentzStateResponseUpdate source current
            time).conjugateMatter space matter)
        0 =
      (currentCanonicalFullActionLorentzStateResponse source current
        space).conjugateMatter matter
  lorentzResponse : forall direction,
    gravityAuxiliaryHodgePairingPolynomial 1
        ((currentCanonicalFullActionLorentzStateResponse source current
          space).gravityAuxiliary)
        (lorentzConnectionExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalLorentzSpatialBivectorOneForm direction)) =
      currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source
        current space direction
  p286Response :
    p286SpatialBFLegendreDualOperator
        (currentP286SpatialAuxiliaryVelocity source
          (currentCanonicalFullActionBaseActual source current space)) =
      currentP286SpatialActionTarget source
        (currentCanonicalFullActionBaseActual source current space)
  primalProjection :
    (currentCanonicalFullActionLorentzStateResponse source current
      space).matter =
      matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity current space)
  primalResponse :
    IdentityCoframeMatterTimeActionLaw current space
      (currentCanonicalFullActionLorentzStateMatterCovariantResponse current
        space)
  primalUnique : forall candidate,
    IdentityCoframeMatterTimeActionLaw current space candidate ->
      candidate =
        currentCanonicalFullActionLorentzStateMatterCovariantResponse current
          space
  adjointProjection :
    (currentCanonicalFullActionLorentzStateResponse source current
      space).conjugateMatter =
      currentCanonicalFullActionLorentzStateAdjointResponse current space
  adjointResponse :
    IdentityCoframeConjugateMatterTimeActionLaw current space
      (currentCanonicalFullActionLorentzStateAdjointResponse current space)
  adjointUnique : forall candidate,
    IdentityCoframeConjugateMatterTimeActionLaw current space candidate ->
      candidate =
        currentCanonicalFullActionLorentzStateAdjointResponse current space

/-- Every identity-coframe contact generates its complete local response.
No global identity-coframe premise is required. -/
theorem currentCanonicalFullActionLorentzContactResponse_realizes
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframeAt : current.coframe space = 1) :
    StageNineCurrentCanonicalFullActionLorentzContactResponseLaw
      source current space where
  identityCoframeAt := identityCoframeAt
  localActualGenerated := rfl
  localActualSmooth :=
    currentCanonicalFullActionLorentzActualFirstJetLift_smooth
      source current space
  localActualNondegenerate :=
    currentCanonicalFullActionLorentzActualFirstJetLift_nondegenerate
      source current space identityCoframeAt
  localPathGenerated := fun _ => rfl
  coframeTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_coframeTangent
      source current space
  gravityConnectionTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_gravityConnectionTangent
      source current space
  gravityAuxiliaryTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_gravityAuxiliaryTangent
      source current space
  multiplierTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_multiplierTangent
      source current space
  p286ConnectionTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_p286ConnectionTangent
      source current space
  p286AuxiliaryTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_p286AuxiliaryTangent
      source current space
  scalarTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_scalarTangent
      source current space
  scalarVelocityTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_scalarVelocityTangent
      source current space
  matterTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_matterTangent
      source current space
  conjugateMatterTimeJet :=
    currentCanonicalFullActionLorentzStateResponseUpdate_conjugateMatterTangent
      source current space
  lorentzResponse :=
    currentCanonicalFullActionLorentzStateResponse_lorentzPairing
      source current space
  p286Response :=
    currentCanonicalFullActionLorentzStateResponse_p286Response
      source current space
  primalProjection :=
    currentCanonicalFullActionLorentzStateResponse_matter
      source current space
  primalResponse :=
    currentCanonicalFullActionLorentzStateResponse_primalLaw
      source current space
  primalUnique := fun candidate candidateLaw =>
    currentCanonicalFullActionLorentzStateResponse_primalUnique
      source current space candidate candidateLaw
  adjointProjection :=
    currentCanonicalFullActionLorentzStateResponse_conjugateMatter
      source current space
  adjointResponse :=
    currentCanonicalFullActionLorentzStateResponse_adjointLaw
      source current space
  adjointUnique := fun candidate candidateLaw =>
    currentCanonicalFullActionLorentzStateResponse_adjointUnique
      source current space candidate candidateLaw

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzContactResponse
