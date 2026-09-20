import H0mework.Physics.Geometry.JointStateLiftDefect

/-!
# Stage-9 joint residual response snapshot

This module packages a sufficient pointwise response snapshot for the current
nine-coordinate joint-shell residual.  It is the endpoint response carrier
used to compare the physical lift `r ↦ K r`: equality of endpoint snapshots
forces equality of the lifted endpoint residual and hence equality of `D_U`
when the old configuration is fixed.

The snapshot is a readout of an already existing holonomic configuration.  It
is not a new dynamical or constitutive field, not a source producer, and not a
stationarity receipt.  No minimality or injectivity claim is made.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineJointResidualResponseSnapshot

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointStateLiftDefect
open StageNineGravityAuxiliaryVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineScalarPointwiseEquation
open StageNineMatterPointwiseEquation
open StageNineConjugateMatterVariation
open StageNineCoframeLocalDifferentiability

noncomputable section

set_option autoImplicit false

abbrev CurrentSmoothUnifiedSource :=
  StageNineJointShellResidualCarrier.CurrentSmoothUnifiedSource

/-- A sufficient generated endpoint-response snapshot for reconstructing the
current pointwise joint residual.  The divergence entries are higher-jet
readouts, not primitive source slots. -/
structure PointwiseResidualResponseSnapshot where
  actionJet : StageNineContinuumPointField
  lorentzAlgebraicResponse : LorentzBivectorOneForm → ℝ
  lorentzBFDifferentialMomentumDivergence :
    LorentzBivectorOneForm → ℝ
  p286AlgebraicResponse : P286GaugeOneForm → ℝ
  p286BFDifferentialMomentumDivergence : P286GaugeOneForm → ℝ
  scalarAlgebraicResponse : ScalarCoordinateCarrier → ℝ
  scalarDifferentialMomentumDivergence : ScalarCoordinateCarrier → ℝ
  matterAlgebraicResponse : MatterCoordinateCarrier → ℝ
  matterDifferentialMomentumDivergence : MatterCoordinateCarrier → ℝ

/-- Canonical response snapshot read from one actual holonomic configuration. -/
def pointwiseResidualResponseSnapshot
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : PointwiseResidualResponseSnapshot where
  actionJet := toContinuumPointField configuration point
  lorentzAlgebraicResponse := fun direction =>
    lorentzConnectionAlgebraicSpinCurrentCoefficient source configuration
      direction point
  lorentzBFDifferentialMomentumDivergence := fun direction =>
    lorentzConnectionBFDifferentialMomentumDivergence configuration direction
      point
  p286AlgebraicResponse := fun direction =>
    p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
      direction point
  p286BFDifferentialMomentumDivergence := fun direction =>
    p286GaugeConnectionBFDifferentialMomentumDivergence configuration direction
      point
  scalarAlgebraicResponse := fun direction =>
    scalarAlgebraicDirectionalCoefficient source configuration direction point
  scalarDifferentialMomentumDivergence := fun direction =>
    scalarDifferentialMomentumDivergence source configuration direction point
  matterAlgebraicResponse := fun direction =>
    matterAlgebraicDirectionalCoefficient source configuration direction point
  matterDifferentialMomentumDivergence := fun direction =>
    matterDifferentialMomentumDivergence source configuration direction point

/-- Reconstruct the current nine-coordinate pointwise residual from one
endpoint response snapshot.  This is a response readout for the physical lift,
not a configuration-field or source constructor. -/
def pointwiseJointResidualOfResponseSnapshot
    (source : CurrentSmoothUnifiedSource)
    (point : BasePoint)
    (snapshot : PointwiseResidualResponseSnapshot) :
    CurrentPointwiseJointShellResidualCarrier where
  algebraic :=
    { gravitySimplicity :=
        generatedGravitySimplicityResidual snapshot.actionJet
      gravityAuxiliary := gravityAuxiliaryEquationResidual snapshot.actionJet
      p286GaugeAuxiliary :=
        p286CoordinateGaugeAuxiliaryEquationResidual
          (coframeGaugeSpacetimeHodgeLinear snapshot.actionJet.coframe)
          ((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ)
          (fun pair =>
            p286CoordinateEquiv (snapshot.actionJet.gaugeCurvature pair))
          (fun pair =>
            p286CoordinateEquiv (snapshot.actionJet.gaugeAuxiliary pair)) }
  eulerLagrange :=
    { lorentzConnection := fun direction =>
        snapshot.lorentzAlgebraicResponse direction -
          snapshot.lorentzBFDifferentialMomentumDivergence direction
      p286GaugeConnection := fun direction =>
        snapshot.p286AlgebraicResponse direction -
          snapshot.p286BFDifferentialMomentumDivergence direction
      scalar := fun direction =>
        snapshot.scalarAlgebraicResponse direction -
          snapshot.scalarDifferentialMomentumDivergence direction
      matter := fun direction =>
        snapshot.matterAlgebraicResponse direction -
          snapshot.matterDifferentialMomentumDivergence direction
      conjugateMatter := fun direction =>
        generatedVolumeDensity snapshot.actionJet *
          (matterDualOfCoordinates direction
            (generatedContinuumMatterVector source 0 point
              snapshot.actionJet)).re
      coframe := coframeLocalStressCovector source point snapshot.actionJet }

/-- The canonical response snapshot reconstructs exactly the actual current
pointwise joint residual of its configuration. -/
theorem pointwiseJointResidualOfResponseSnapshot_of_configuration
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    pointwiseJointResidualOfResponseSnapshot source point
        (pointwiseResidualResponseSnapshot source configuration point) =
      currentPointwiseJointShellResidual source configuration point := by
  rfl

/-- Equality of canonical response snapshots is sufficient for equality of all
nine current pointwise residual coordinates. -/
theorem currentPointwiseJointShellResidual_eq_of_responseSnapshot_eq
    (source : CurrentSmoothUnifiedSource)
    {first second : StageNineHolonomicConfiguration}
    {point : BasePoint}
    (snapshotEq :
      pointwiseResidualResponseSnapshot source first point =
        pointwiseResidualResponseSnapshot source second point) :
    currentPointwiseJointShellResidual source first point =
      currentPointwiseJointShellResidual source second point := by
  calc
    currentPointwiseJointShellResidual source first point =
        pointwiseJointResidualOfResponseSnapshot source point
          (pointwiseResidualResponseSnapshot source first point) :=
      (pointwiseJointResidualOfResponseSnapshot_of_configuration
        source first point).symm
    _ = pointwiseJointResidualOfResponseSnapshot source point
          (pointwiseResidualResponseSnapshot source second point) :=
      congrArg (pointwiseJointResidualOfResponseSnapshot source point) snapshotEq
    _ = currentPointwiseJointShellResidual source second point :=
      pointwiseJointResidualOfResponseSnapshot_of_configuration
        source second point

/-- With the old configuration fixed, equality of generated endpoint response
snapshots implies equality of the complete physical-lift defect `D_U`. -/
theorem currentJointShellStateLiftDefect_point_eq_of_endpointSnapshot_eq
    (source : CurrentSmoothUnifiedSource)
    (firstUpdate secondUpdate : CurrentJointShellStateUpdate)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (endpointSnapshotEq :
      pointwiseResidualResponseSnapshot source
          (firstUpdate configuration) point =
        pointwiseResidualResponseSnapshot source
          (secondUpdate configuration) point) :
    currentJointShellStateLiftDefect source firstUpdate configuration point =
      currentJointShellStateLiftDefect source secondUpdate configuration point := by
  unfold currentJointShellStateLiftDefect
  change
    currentPointwiseJointShellResidual source (firstUpdate configuration) point -
        _ =
      currentPointwiseJointShellResidual source (secondUpdate configuration)
          point - _
  rw [currentPointwiseJointShellResidual_eq_of_responseSnapshot_eq source
    endpointSnapshotEq]

end
end SaturationMonoid.PhysicsCore.StageNineJointResidualResponseSnapshot
