import H0mework.Physics.ActualGerms.FixedZeroSliceCoframe
import H0mework.Physics.DualVariation.PointwiseActionJetCarrier

/-!
# Canonical generated-actual pointwise action jet

The fixed P506/L0 canonical P286 successor is first exposed as one complete
pointwise action jet.  Its point field is obtained by applying the generated
quadratic connection write to the final common current and then recomputing
the P286 auxiliary through the authoritative constitutive inverse.  The
nine-channel residual is only a downstream readout of this action-owned jet.

No residual coordinate, support branch, target field, or zero-fiber witness
enters the normal form below.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualPointwiseActionJet

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualFirstGerm
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterPointwiseEquation
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286HolonomicSecondJetCurvatureSymbol
open StageNineScalarPointwiseEquation
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

local instance canonicalPointwiseActionJetP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance canonicalPointwiseActionJetP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance canonicalPointwiseActionJetP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev CanonicalInput : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalActionInput

private abbrev CanonicalConnectionActual : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalConnectionCandidate
    fixedP506L0P286CanonicalGeneratedWrite

private abbrev CanonicalActual : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

/-- Ordinary-smooth counterpart of the compact-support point-field helper.
Compact support belongs to integrated variation mouths; the generated global
quadratic write only needs its actual `ContDiff` provenance here. -/
private theorem toContinuumPointField_varyP286GaugeConnectionCoordinate_of_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : BasePoint → P286GaugeOneForm)
    (variationSmooth : ContDiff ℝ ∞ variation)
    (parameter : ℝ) (point : BasePoint) :
    toContinuumPointField
        (varyP286GaugeConnectionCoordinate configuration variation parameter)
        point =
      withP286GaugeConnectionJets
        (toContinuumPointField configuration point)
        (variedP286CurvatureCoordinate configuration variation parameter point)
        (variedP286ScalarCovariantDerivative configuration variation parameter
          point)
        (variedP286MatterCovariantDerivative configuration variation parameter
          point) := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  · funext pair
    apply p286CoordinateEquiv.injective
    simp only [toContinuumPointField, withP286GaugeConnectionJets,
      p286CoordinateEquiv.apply_symm_apply]
    change
      holonomicP286GaugeCurvatureCoordinate
          (varyP286GaugeConnectionCoordinate configuration variation parameter)
          point pair =
        variedP286CurvatureCoordinate configuration variation parameter point
          pair
    have curvatureExpansion := congrFun
      (holonomicP286GaugeCurvatureCoordinate_expansion_of_contDiff
        configuration smooth variation variationSmooth parameter point) pair
    simpa [variedP286CurvatureCoordinate] using curvatureExpansion
  · funext direction
    exact holonomicScalarCovariantDerivative_gaugeConnection_expansion
      configuration variation parameter point direction
  · funext direction
    exact holonomicMatterCovariantDerivative_gaugeConnection_expansion
      configuration variation parameter point direction

/-- The exact homogeneous-quadratic connection field already selected by the
canonical action pairing. -/
def fixedP506L0P286CanonicalGeneratedQuadraticVariation :
    BasePoint → P286GaugeOneForm :=
  p286HolonomicSecondJetQuadraticRealization
    (p286CanonicalDiagonalResponseSecondJet
      fixedP506L0P286CanonicalGeneratedWrite)

/-- Explicit all-spacetime polynomial selected by the canonical action
pairing.  This is a normal form of the existing write, not an ansatz. -/
def fixedP506L0P286CanonicalGeneratedQuadraticVariationNormalForm
    (point : BasePoint) : P286GaugeOneForm :=
  ∑ diagonalDirection : LorentzianIndex,
    ((1 / 2 : ℝ) * (point diagonalDirection) ^ 2) •
      p286CanonicalDiagonalResponseOneForm
        fixedP506L0P286CanonicalGeneratedWrite diagonalDirection

theorem fixedP506L0P286CanonicalGeneratedQuadraticVariation_normalForm
    (point : BasePoint) :
    fixedP506L0P286CanonicalGeneratedQuadraticVariation point =
      fixedP506L0P286CanonicalGeneratedQuadraticVariationNormalForm point := by
  funext formDirection
  fin_cases formDirection <;>
    simp [fixedP506L0P286CanonicalGeneratedQuadraticVariation,
      fixedP506L0P286CanonicalGeneratedQuadraticVariationNormalForm,
      p286HolonomicSecondJetQuadraticRealization,
      p286CanonicalDiagonalResponseSecondJet,
      p286CanonicalDiagonalResponseSecondJetAmbient,
      ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply,
      p286CanonicalDiagonalResponseOneForm, Fin.sum_univ_four] <;>
    module

/-- Complete first jet of the same all-spacetime polynomial. -/
def fixedP506L0P286CanonicalGeneratedQuadraticFirstJetNormalForm
    (point : BasePoint) : LorentzianIndex → P286GaugeOneForm :=
  fun derivativeDirection =>
    (point derivativeDirection) •
      p286CanonicalDiagonalResponseOneForm
        fixedP506L0P286CanonicalGeneratedWrite derivativeDirection

theorem fixedP506L0P286CanonicalGeneratedQuadraticVariation_firstJet_normalForm
    (point : BasePoint) :
    (fun derivativeDirection =>
      fieldDirectionalDerivative
        fixedP506L0P286CanonicalGeneratedQuadraticVariation point
        derivativeDirection) =
      fixedP506L0P286CanonicalGeneratedQuadraticFirstJetNormalForm point := by
  funext derivativeDirection formDirection
  unfold fixedP506L0P286CanonicalGeneratedQuadraticVariation
  rw [p286HolonomicSecondJetQuadraticRealization_directionalDerivative]
  fin_cases derivativeDirection <;>
    simp [fixedP506L0P286CanonicalGeneratedQuadraticFirstJetNormalForm,
      p286CanonicalDiagonalResponseSecondJet,
      p286CanonicalDiagonalResponseSecondJetAmbient,
      ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply,
      coordinateDirection, Fin.sum_univ_four]

/-- Point-field normal form after the action-owned connection write and the
live constitutive readout.  Every slot is computed from the same input,
write, and spacetime occurrence. -/
def fixedP506L0P286CanonicalGeneratedPointFieldNormalForm
    (point : BasePoint) : StageNineContinuumPointField :=
  let connectionField :=
    withP286GaugeConnectionJets
      (toContinuumPointField CanonicalInput point)
      (variedP286CurvatureCoordinate CanonicalInput
        fixedP506L0P286CanonicalGeneratedQuadraticVariation 1 point)
      (variedP286ScalarCovariantDerivative CanonicalInput
        fixedP506L0P286CanonicalGeneratedQuadraticVariation 1 point)
      (variedP286MatterCovariantDerivative CanonicalInput
        fixedP506L0P286CanonicalGeneratedQuadraticVariation 1 point)
  withFormNativeP286GaugeAuxiliary connectionField
    (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (CanonicalInput.coframe point)
      (holonomicGaugeCurvature CanonicalConnectionActual point))

theorem fixedP506L0P286CanonicalGeneratedActual_pointField_normalForm
    (point : BasePoint) :
    toContinuumPointField CanonicalActual point =
      fixedP506L0P286CanonicalGeneratedPointFieldNormalForm point := by
  rw [show
    CanonicalActual =
        formNativeP286GaugeConstitutiveReadout positiveSmoothUnifiedSource
          CanonicalConnectionActual by rfl]
  rw [toContinuumPointField_formNativeP286GaugeConstitutiveReadout]
  have connectionPointField :
      toContinuumPointField CanonicalConnectionActual point =
      withP286GaugeConnectionJets
        (toContinuumPointField CanonicalInput point)
        (variedP286CurvatureCoordinate CanonicalInput
          fixedP506L0P286CanonicalGeneratedQuadraticVariation 1 point)
        (variedP286ScalarCovariantDerivative CanonicalInput
          fixedP506L0P286CanonicalGeneratedQuadraticVariation 1 point)
        (variedP286MatterCovariantDerivative CanonicalInput
          fixedP506L0P286CanonicalGeneratedQuadraticVariation 1 point) := by
    change
      toContinuumPointField
          (varyP286GaugeConnectionCoordinate CanonicalInput
            fixedP506L0P286CanonicalGeneratedQuadraticVariation 1) point = _
    exact
      toContinuumPointField_varyP286GaugeConnectionCoordinate_of_contDiff
        CanonicalInput (fixedP506L0FinalCommonActionActual_smooth 0)
        fixedP506L0P286CanonicalGeneratedQuadraticVariation
        (p286HolonomicSecondJetQuadraticRealization_contDiff
          (p286CanonicalDiagonalResponseSecondJet
            fixedP506L0P286CanonicalGeneratedWrite))
        1 point
  rw [connectionPointField]
  rfl

/-- One whole-carrier action-jet normal form.  The two differential response
slots which genuinely read the post-write configuration remain literal
action derivatives; the matter momentum divergence is transported from the
unchanged coframe/adjoint fields by its proved whole-function equality. -/
def fixedP506L0P286CanonicalGeneratedPointwiseActionJetNormalForm
    (point : BasePoint) : DiracDualFormNativePointwiseActionJetCarrier :=
  { pointField :=
      fixedP506L0P286CanonicalGeneratedPointFieldNormalForm point
    gravityConnection := CanonicalInput.gravityConnection point
    p286GaugeConnection := CanonicalConnectionActual.gaugeConnection point
    gravityAuxiliaryExteriorCovariantDerivative :=
      holonomicGravityAuxiliaryExteriorCovariantDerivative CanonicalInput point
    p286GaugeAuxiliaryExteriorCovariantDerivative :=
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative CanonicalActual
        point
    scalarDifferentialMomentumDivergence := fun direction =>
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        CanonicalActual direction point
    matterDifferentialMomentumDivergence := fun direction =>
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        CanonicalInput direction point }

/-- The generated successor's complete action jet is exactly the normal form
assembled from its source/action-owned write. -/
theorem fixedP506L0P286CanonicalGeneratedActual_pointwiseActionJet_normalForm
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet
        positiveSmoothUnifiedSource CanonicalActual point =
      fixedP506L0P286CanonicalGeneratedPointwiseActionJetNormalForm point := by
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · exact fixedP506L0P286CanonicalGeneratedActual_pointField_normalForm point
  · exact congrFun canonicalGeneratedActual_gravityConnection point
  · rfl
  · change
      holonomicGravityAuxiliaryExteriorCovariantDerivative CanonicalActual
          point =
        holonomicGravityAuxiliaryExteriorCovariantDerivative CanonicalInput
          point
    unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
      holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
    rw [canonicalGeneratedActual_gravityAuxiliary,
      canonicalGeneratedActual_gravityConnection]
  · change
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative CanonicalActual
          point =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative CanonicalActual
          point
    rfl
  · funext direction
    rfl
  · funext direction
    exact congrFun
      (canonicalGeneratedActual_matterDifferentialMomentumDivergence_eq
        direction) point

/-- Whole pointwise residual naturality for the canonical successor.  This
theorem changes no field: it factors the existing residual through the one
action jet generated above. -/
theorem fixedP506L0P286CanonicalGeneratedActual_pointwiseResidual_actionJet
    (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        CanonicalActual point =
      diracDualFormNativeJointResidualOfActionJet
        positiveSmoothUnifiedSource point
        (fixedP506L0P286CanonicalGeneratedPointwiseActionJetNormalForm point) := by
  rw [diracDualFormNativePointwiseJointResidual_eq_actionJetReadout,
    fixedP506L0P286CanonicalGeneratedActual_pointwiseActionJet_normalForm]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualPointwiseActionJet
