import H0mework.Physics.CurrentAction.LorentzActualFirstJetLift
import H0mework.Physics.ConnectionJets.CurrentP286CompleteActionResponseFirstJet

/-!
# C3h200a: current-state restart P286 Gauss generation

This module proves a dependency-light generic fact about the complete
current-state actualizer.  For an identity-coframe current, the direct P286
response first generates the complete P286 connection equation at the new
contact origin.  The later matter first-germ and Lorentz-auxiliary installers
preserve every field consumed by that equation there.  Its temporal tests
then structurally project to canonical P286 Gauss.

The result is restart producer-soundness.  It does not transport a prior
Gauss certificate, prove that an unrestarted actual remains on the Gauss
surface at shifted local time, or prove that the full vector field is tangent
to that surface.  Those propagation statements remain separate gates.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzRestartP286Gauss

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open SU7MotherGaugeTheory

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ## Structural temporal projection -/

/-- Point-local temporal P286 Euler tests imply canonical Gauss.  This is the
minimal structural projection needed by a current-state restart; it does not
require or manufacture a global pointwise-equation receipt. -/
theorem p286TemporalEulerAt_implies_gauss
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : actual.Nondegenerate)
    (temporalEuler : forall component : P286CoordinateCarrier,
      p286GaugeConnectionEulerLagrangeCoefficient source actual
          (p286TemporalGaugeOneForm component) point =
        0) :
    CanonicalP286GaugeGaussConstraintAt source actual point := by
  intro component
  have pointEquation := temporalEuler component
  rw [p286GaugeConnectionEulerLagrangeCoefficient,
    p286GaugeConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial,
    p286GaugeConnectionTemporalBFMomentumDerivative_temporal_eq_zero
      actual nondegenerate] at pointEquation
  linarith

/-! ## Generic complete-actual producer consistency -/

private theorem currentCanonicalFullActionBaseActual_coframe_one
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : current.coframe space = 1)
    (point : BasePoint) :
    (currentCanonicalFullActionBaseActual source current space).coframe point =
      1 := by
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      source current space).coframe point =
      1
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe,
    identityCoframe]

private theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_coframe_eq_directP286
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).coframe =
      (currentCanonicalGravityPreservingP286Actual source current
        space).coframe := by
  rfl

private theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_gaugeConnection_eq_directP286
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).gaugeConnection =
      (currentCanonicalGravityPreservingP286Actual source current
        space).gaugeConnection := by
  rfl

private theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_gaugeAuxiliary_eq_directP286
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).gaugeAuxiliary =
      (currentCanonicalGravityPreservingP286Actual source current
        space).gaugeAuxiliary := by
  rfl

private theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_scalar_eq_directP286
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).scalar =
      (currentCanonicalGravityPreservingP286Actual source current
        space).scalar := by
  rfl

private theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_conjugateMatter_eq_directP286
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).conjugateMatter =
      (currentCanonicalGravityPreservingP286Actual source current
        space).conjugateMatter := by
  rfl

private theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_matter_origin_eq_directP286
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space).matter 0 =
      (currentCanonicalGravityPreservingP286Actual source current
        space).matter 0 := by
  change
    (actionGeneratedMatterCompleteFirstGermActual source
      (actionGeneratedMatterTemporalFirstGermActual source
        (currentCanonicalGravityPreservingP286Actual source current
          space))).matter 0 =
      (currentCanonicalGravityPreservingP286Actual source current
        space).matter 0
  rw [actionGeneratedMatterCompleteFirstGermActual_matter_origin,
    actionGeneratedMatterTemporalFirstGermActual_matter_origin]

private theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_scalarCovariantDerivative_origin_eq_directP286
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative
        (currentCanonicalFullActionLorentzActualFirstJetLift source current
          space) 0 =
      holonomicScalarCovariantDerivative
        (currentCanonicalGravityPreservingP286Actual source current space)
        0 := by
  unfold holonomicScalarCovariantDerivative
  rw [currentCanonicalFullActionLorentzActualFirstJetLift_scalar_eq_directP286,
    currentCanonicalFullActionLorentzActualFirstJetLift_gaugeConnection_eq_directP286]

private theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_p286AlgebraicCurrent_origin_eq_directP286
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source
        (currentCanonicalFullActionLorentzActualFirstJetLift source current
          space)
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient source
        (currentCanonicalGravityPreservingP286Actual source current space)
        direction 0 := by
  exact p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contact
    source
    (currentCanonicalFullActionLorentzActualFirstJetLift source current space)
    (currentCanonicalGravityPreservingP286Actual source current space)
    0
    (congrFun
      (currentCanonicalFullActionLorentzActualFirstJetLift_coframe_eq_directP286
        source current space) 0)
    (congrFun
      (currentCanonicalFullActionLorentzActualFirstJetLift_gaugeConnection_eq_directP286
        source current space) 0)
    (congrFun
      (currentCanonicalFullActionLorentzActualFirstJetLift_gaugeAuxiliary_eq_directP286
        source current space) 0)
    (congrFun
      (currentCanonicalFullActionLorentzActualFirstJetLift_scalar_eq_directP286
        source current space) 0)
    (currentCanonicalFullActionLorentzActualFirstJetLift_scalarCovariantDerivative_origin_eq_directP286
      source current space)
    (currentCanonicalFullActionLorentzActualFirstJetLift_matter_origin_eq_directP286
      source current space)
    (congrFun
      (currentCanonicalFullActionLorentzActualFirstJetLift_conjugateMatter_eq_directP286
        source current space) 0)
    direction

private theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_p286BFMomentum_eq_directP286
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        (currentCanonicalFullActionLorentzActualFirstJetLift source current
          space)
        direction =
      p286GaugeConnectionBFDifferentialMomentum
        (currentCanonicalGravityPreservingP286Actual source current space)
        direction := by
  rfl

private theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_p286BFDivergence_origin_eq_directP286
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        (currentCanonicalFullActionLorentzActualFirstJetLift source current
          space)
        direction 0 =
      p286GaugeConnectionBFDifferentialMomentumDivergence
        (currentCanonicalGravityPreservingP286Actual source current space)
        direction 0 := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [currentCanonicalFullActionLorentzActualFirstJetLift_p286BFMomentum_eq_directP286]

/-- The full P286 connection equation is regenerated at the origin of every
identity-coframe current-state actual.  This is producer consistency: the
response operator solves the equation it was built from. -/
theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_p286ConnectionEquation_origin_producerConsistency
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : current.coframe space = 1)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient source
        (currentCanonicalFullActionLorentzActualFirstJetLift source current
          space)
        direction 0 =
      0 := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [currentCanonicalFullActionLorentzActualFirstJetLift_p286AlgebraicCurrent_origin_eq_directP286,
    currentCanonicalFullActionLorentzActualFirstJetLift_p286BFDivergence_origin_eq_directP286]
  exact currentP286CompleteActionResponseOperator_connectionEquation_origin
    source (currentCanonicalFullActionBaseActual source current space)
    (currentCanonicalFullActionBaseActual_coframe_one
      source current space identityCoframe)
    direction

/-- Canonical P286 Gauss at the newly generated contact origin.  The theorem
does not accept a Gauss witness; it projects the temporal tests of the actual
P286 equation produced immediately above. -/
theorem
    currentCanonicalFullActionLorentzActualFirstJetLift_p286Gauss_origin
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : current.coframe space = 1) :
    CanonicalP286GaugeGaussConstraintAt source
      (currentCanonicalFullActionLorentzActualFirstJetLift source current
        space)
      0 := by
  apply p286TemporalEulerAt_implies_gauss source _ 0
  · exact currentCanonicalFullActionLorentzActualFirstJetLift_nondegenerate
      source current space identityCoframe
  · intro component
    exact
      currentCanonicalFullActionLorentzActualFirstJetLift_p286ConnectionEquation_origin_producerConsistency
        source current space identityCoframe
        (p286TemporalGaugeOneForm component)

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzRestartP286Gauss
