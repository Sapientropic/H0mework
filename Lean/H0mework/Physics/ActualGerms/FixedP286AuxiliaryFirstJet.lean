import H0mework.Physics.ActualGerms.FixedPointwiseActionJet
import H0mework.Physics.Coframe.CoframeGravityGaugeRegularity
import H0mework.Physics.Constitutive.P286GaugeConstitutiveEliminationRegularity

/-!
# Canonical generated P286 auxiliary first jet

The canonical action-owned quadratic connection write already supplies its
global value and first-jet normal forms.  This module assembles the resulting
non-Abelian curvature, transports the joint coframe/curvature first jet
through the authoritative constitutive inverse, and packages the resulting
`D_A B` at every nondegenerate occurrence of the same generated actual.

The nondegeneracy hypothesis is exactly the local differentiability domain of
the live inverse-coframe Hodge operator.  No residual coordinate, residual
support, correction, target field, branch, or zero-fiber witness enters any
constructor below.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualP286AuxiliaryFirstJet

open ProofFreeRicherAnholonomicSource
open EmpiricalReferenceScaleCouplingBoundary
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualPointwiseActionJet
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286HolonomicSecondJetCurvatureSymbol
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

local instance canonicalAuxiliaryFirstJetP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance canonicalAuxiliaryFirstJetP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance canonicalAuxiliaryFirstJetP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev CanonicalInput : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalActionInput

private abbrev CanonicalConnectionActual : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalConnectionCandidate
    fixedP506L0P286CanonicalGeneratedWrite

private abbrev CanonicalActual : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

private abbrev CanonicalBoundary : EmpiricalReferenceScaleCouplings :=
  sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource

/-! ## Action-owned connection and curvature normal forms -/

/-- Global connection value obtained by adding the generated quadratic write
to the fixed action input. -/
def fixedP506L0P286CanonicalGeneratedGaugeConnectionCoordinateNormalForm
    (point : BasePoint) : P286GaugeOneForm :=
  holonomicP286GaugeConnectionCoordinate CanonicalInput point +
    fixedP506L0P286CanonicalGeneratedQuadraticVariationNormalForm point

theorem
    fixedP506L0P286CanonicalGeneratedActual_gaugeConnectionCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate CanonicalActual point =
      fixedP506L0P286CanonicalGeneratedGaugeConnectionCoordinateNormalForm
        point := by
  change
    holonomicP286GaugeConnectionCoordinate
        (varyP286GaugeConnectionCoordinate CanonicalInput
          fixedP506L0P286CanonicalGeneratedQuadraticVariation 1) point = _
  rw [holonomicP286GaugeConnectionCoordinate_vary,
    fixedP506L0P286CanonicalGeneratedQuadraticVariation_normalForm]
  simp [fixedP506L0P286CanonicalGeneratedGaugeConnectionCoordinateNormalForm]

/-- Complete first jet of the same post-write connection. -/
def fixedP506L0P286CanonicalGeneratedGaugeConnectionFirstJetNormalForm
    (point : BasePoint) : LorentzianIndex → P286GaugeOneForm :=
  fun derivativeDirection formDirection =>
    p286GaugeConnectionCoordinateDerivative CanonicalInput point
        derivativeDirection formDirection +
      fixedP506L0P286CanonicalGeneratedQuadraticFirstJetNormalForm point
        derivativeDirection formDirection

private theorem
    fixedP506L0P286CanonicalGeneratedQuadraticVariation_componentDerivative
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeVariationCoordinateDerivative
        fixedP506L0P286CanonicalGeneratedQuadraticVariation point
        derivativeDirection formDirection =
      fixedP506L0P286CanonicalGeneratedQuadraticFirstJetNormalForm point
        derivativeDirection formDirection := by
  let jet := p286CanonicalDiagonalResponseSecondJet
    fixedP506L0P286CanonicalGeneratedWrite
  calc
    p286GaugeVariationCoordinateDerivative
        fixedP506L0P286CanonicalGeneratedQuadraticVariation point
        derivativeDirection formDirection =
        p286HolonomicSecondJetComponentLinear jet derivativeDirection
          formDirection point := by
      exact p286HolonomicSecondJetQuadraticRealization_variationDerivative
        jet point derivativeDirection formDirection
    _ = (fieldDirectionalDerivative
          fixedP506L0P286CanonicalGeneratedQuadraticVariation point
          derivativeDirection) formDirection := by
      rw [fixedP506L0P286CanonicalGeneratedQuadraticVariation]
      rw [p286HolonomicSecondJetQuadraticRealization_directionalDerivative]
      rfl
    _ = fixedP506L0P286CanonicalGeneratedQuadraticFirstJetNormalForm point
          derivativeDirection formDirection := by
      exact congrFun
        (congrFun
          (fixedP506L0P286CanonicalGeneratedQuadraticVariation_firstJet_normalForm
            point)
          derivativeDirection)
        formDirection

theorem
    fixedP506L0P286CanonicalGeneratedActual_gaugeConnectionFirstJet_normalForm
    (point : BasePoint) :
    (fun derivativeDirection formDirection =>
      p286GaugeConnectionCoordinateDerivative CanonicalActual point
        derivativeDirection formDirection) =
      fixedP506L0P286CanonicalGeneratedGaugeConnectionFirstJetNormalForm
        point := by
  funext derivativeDirection formDirection
  change
    p286GaugeConnectionCoordinateDerivative
        (varyP286GaugeConnectionCoordinate CanonicalInput
          fixedP506L0P286CanonicalGeneratedQuadraticVariation 1)
        point derivativeDirection formDirection = _
  rw [p286GaugeConnectionCoordinateDerivative_vary_of_contDiff
    CanonicalInput (fixedP506L0FinalCommonActionActual_smooth 0)
    fixedP506L0P286CanonicalGeneratedQuadraticVariation
    (p286HolonomicSecondJetQuadraticRealization_contDiff
      (p286CanonicalDiagonalResponseSecondJet
        fixedP506L0P286CanonicalGeneratedWrite))]
  rw [fixedP506L0P286CanonicalGeneratedQuadraticVariation_componentDerivative]
  simp [fixedP506L0P286CanonicalGeneratedGaugeConnectionFirstJetNormalForm]

/-- Exact non-Abelian curvature assembled from the global post-write
connection value and first jet. -/
def fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm
    (point : BasePoint) : FormNativeP286GaugeCoordinateTwoForm :=
  fun pair =>
    fixedP506L0P286CanonicalGeneratedGaugeConnectionFirstJetNormalForm point
          (pairFirst pair) (pairSecond pair) -
      fixedP506L0P286CanonicalGeneratedGaugeConnectionFirstJetNormalForm point
          (pairSecond pair) (pairFirst pair) +
      p286CoordinateLieBracket
        (fixedP506L0P286CanonicalGeneratedGaugeConnectionCoordinateNormalForm
          point (pairFirst pair))
        (fixedP506L0P286CanonicalGeneratedGaugeConnectionCoordinateNormalForm
          point (pairSecond pair))

theorem
    fixedP506L0P286CanonicalGeneratedActual_gaugeCurvatureCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate CanonicalActual point =
      fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm
        point := by
  funext pair
  rw [holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket]
  have connection :=
    fixedP506L0P286CanonicalGeneratedActual_gaugeConnectionCoordinate_normalForm
      point
  have firstJet :=
    fixedP506L0P286CanonicalGeneratedActual_gaugeConnectionFirstJet_normalForm
      point
  rw [congrFun (congrFun firstJet (pairFirst pair)) (pairSecond pair),
    congrFun (congrFun firstJet (pairSecond pair)) (pairFirst pair),
    congrFun connection (pairFirst pair),
    congrFun connection (pairSecond pair)]
  rfl

/-- Complete first jet of the explicit post-write curvature normal form. -/
def fixedP506L0P286CanonicalGeneratedGaugeCurvatureFirstJetNormalForm
    (point : BasePoint) :
    LorentzianIndex → FormNativeP286GaugeCoordinateTwoForm :=
  fun direction =>
    fieldDirectionalDerivative
      fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm
      point direction

theorem
    fixedP506L0P286CanonicalGeneratedActual_gaugeCurvatureFirstJet_normalForm
    (point : BasePoint) :
    (fun direction =>
      fieldDirectionalDerivative
        (holonomicP286GaugeCurvatureCoordinate CanonicalActual) point
        direction) =
      fixedP506L0P286CanonicalGeneratedGaugeCurvatureFirstJetNormalForm
        point := by
  have curvatureFunction :
      holonomicP286GaugeCurvatureCoordinate CanonicalActual =
        fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm := by
    funext candidate
    exact
      fixedP506L0P286CanonicalGeneratedActual_gaugeCurvatureCoordinate_normalForm
        candidate
  rw [curvatureFunction]
  rfl

/-! ## Live constitutive first jet -/

/-- The authoritative constitutive inverse on the faithful joint
coframe/curvature chart. -/
def fixedP506L0P286CanonicalGeneratedConstitutiveInverse
    (joint : LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm) :
    FormNativeP286GaugeCoordinateTwoForm :=
  formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
    CanonicalBoundary joint.1 joint.2

/-- Joint live input assembled from the retained coframe and the action-owned
post-write curvature normal form. -/
def fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm
    (point : BasePoint) :
    LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm :=
  (CanonicalInput.coframe point,
    fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm point)

/-- Complete first jet of the same joint live input. -/
def fixedP506L0P286CanonicalGeneratedCoframeCurvatureFirstJetNormalForm
    (point : BasePoint) :
    LorentzianIndex →
      LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm :=
  fun direction =>
    ((fderiv ℝ CanonicalInput.coframe point)
        (coordinateDirection direction),
      fixedP506L0P286CanonicalGeneratedGaugeCurvatureFirstJetNormalForm
        point direction)

/-- Live post-write auxiliary value obtained only by applying the
authoritative inverse to the generated joint input. -/
def fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryCoordinateNormalForm
    (point : BasePoint) : FormNativeP286GaugeCoordinateTwoForm :=
  fixedP506L0P286CanonicalGeneratedConstitutiveInverse
    (fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm point)

theorem
    fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate CanonicalActual point =
      fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryCoordinateNormalForm
        point := by
  unfold fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryCoordinateNormalForm
    fixedP506L0P286CanonicalGeneratedConstitutiveInverse
    fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm
    holonomicP286GaugeAuxiliaryCoordinate
  change
    formNativeP286GaugeActualToCoordinateLinear
        (formNativeP286GaugeEliminatedAuxiliaryAtBoundary CanonicalBoundary
          (CanonicalInput.coframe point)
          (holonomicGaugeCurvature CanonicalConnectionActual point)) =
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        CanonicalBoundary (CanonicalInput.coframe point)
        (fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm
          point)
  unfold formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
  rw [←
    fixedP506L0P286CanonicalGeneratedActual_gaugeCurvatureCoordinate_normalForm]
  apply congrArg formNativeP286GaugeActualToCoordinateLinear
  apply congrArg
    (formNativeP286GaugeEliminatedAuxiliaryAtBoundary CanonicalBoundary
      (CanonicalInput.coframe point))
  calc
    holonomicGaugeCurvature CanonicalConnectionActual point =
        holonomicGaugeCurvature CanonicalActual point :=
      holonomicGaugeCurvature_eq_of_connection_eq_current
        CanonicalConnectionActual CanonicalActual
        fixedP506L0P286CanonicalGeneratedActual_gaugeConnection.symm point
    _ = formNativeP286GaugeCoordinateToActualLinear
          (holonomicP286GaugeCurvatureCoordinate CanonicalActual point) := by
      change
        holonomicGaugeCurvature CanonicalActual point =
          formNativeP286GaugeCoordinateToActualLinear
            (formNativeP286GaugeActualToCoordinateLinear
              (holonomicGaugeCurvature CanonicalActual point))
      exact (formNativeP286GaugeActual_coordinate_actual
        (holonomicGaugeCurvature CanonicalActual point)).symm

/-- The full first jet obtained by differentiating the same action-owned
constitutive inverse at the same live joint input. -/
def fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryFirstJetNormalForm
    (point : BasePoint) :
    LorentzianIndex → FormNativeP286GaugeCoordinateTwoForm :=
  fun direction =>
    (fderiv ℝ fixedP506L0P286CanonicalGeneratedConstitutiveInverse
      (fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm point))
      (fixedP506L0P286CanonicalGeneratedCoframeCurvatureFirstJetNormalForm
        point direction)

private theorem canonicalConnectionActual_smooth :
    CanonicalConnectionActual.Smooth :=
  installP286HolonomicConnectionSecondJet_smooth CanonicalInput
    (fixedP506L0FinalCommonActionActual_smooth 0)
    (p286CanonicalDiagonalResponseSecondJet
      fixedP506L0P286CanonicalGeneratedWrite) 1

private theorem canonicalGeneratedCurvatureNormalForm_differentiableAt
    (point : BasePoint) :
    DifferentiableAt ℝ
      fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm
      point := by
  have curvatureFunction :
      fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm =
        holonomicP286GaugeCurvatureCoordinate CanonicalConnectionActual := by
    funext candidate
    exact
      (fixedP506L0P286CanonicalGeneratedActual_gaugeCurvatureCoordinate_normalForm
        candidate).symm
  rw [curvatureFunction]
  apply differentiableAt_pi.mpr
  intro pair
  exact
    (holonomicGaugeCurvature_coordinate_contDiff CanonicalConnectionActual
      canonicalConnectionActual_smooth pair).differentiable (by simp)
      |>.differentiableAt

/-- The live constitutive P286 coordinate of the canonical generated actual
is genuinely differentiable at every nondegenerate occurrence.  This is the
analytic fact already used by the first-jet normal form, exposed for
whole-field compatibility consumers. -/
theorem
    fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryCoordinate_differentiableAt
    (point : BasePoint)
    (nondegenerate : Matrix.det (CanonicalInput.coframe point) ≠ 0) :
    DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate CanonicalActual) point := by
  have coframeDifferentiable :
      DifferentiableAt ℝ CanonicalInput.coframe point :=
    (holonomicCoframe_contDiff CanonicalInput
      (fixedP506L0FinalCommonActionActual_smooth 0)).differentiable (by simp)
      |>.differentiableAt
  have curvatureDifferentiable :=
    canonicalGeneratedCurvatureNormalForm_differentiableAt point
  have inputDifferentiable :
      DifferentiableAt ℝ
        fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm
        point :=
    coframeDifferentiable.prodMk curvatureDifferentiable
  have outerDifferentiable :
      DifferentiableAt ℝ
        fixedP506L0P286CanonicalGeneratedConstitutiveInverse
        (fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm
          point) :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_differentiableAt
      CanonicalBoundary (CanonicalInput.coframe point) nondegenerate
      (fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm
        point)
  rw [show
    holonomicP286GaugeAuxiliaryCoordinate CanonicalActual =
      fixedP506L0P286CanonicalGeneratedConstitutiveInverse ∘
        fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm by
      funext candidate
      exact
        fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryCoordinate_normalForm
          candidate]
  exact outerDifferentiable.comp point inputDifferentiable

/-- At every actual nondegenerate occurrence, the live auxiliary first jet
is exactly the chain-rule image of the generated coframe/curvature first jet
through the authoritative constitutive inverse. -/
theorem
    fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryFirstJet_normalForm
    (point : BasePoint)
    (nondegenerate : Matrix.det (CanonicalInput.coframe point) ≠ 0) :
    p286GaugeAuxiliaryDirectionalDerivative CanonicalActual point =
      fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryFirstJetNormalForm
        point := by
  have coframeDifferentiable :
      DifferentiableAt ℝ CanonicalInput.coframe point :=
    (holonomicCoframe_contDiff CanonicalInput
      (fixedP506L0FinalCommonActionActual_smooth 0)).differentiable (by simp)
      |>.differentiableAt
  have curvatureDifferentiable :=
    canonicalGeneratedCurvatureNormalForm_differentiableAt point
  have inputDifferentiable :
      DifferentiableAt ℝ
        fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm
        point := by
    exact coframeDifferentiable.prodMk curvatureDifferentiable
  have outerDifferentiable :
      DifferentiableAt ℝ
        fixedP506L0P286CanonicalGeneratedConstitutiveInverse
        (fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm
          point) := by
    exact
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_differentiableAt
        CanonicalBoundary (CanonicalInput.coframe point) nondegenerate
        (fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm
          point)
  have composed := outerDifferentiable.hasFDerivAt.comp point
    inputDifferentiable.hasFDerivAt
  have auxiliaryFunction :
      holonomicP286GaugeAuxiliaryCoordinate CanonicalActual =
        fixedP506L0P286CanonicalGeneratedConstitutiveInverse ∘
          fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm := by
    funext candidate
    exact
      fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryCoordinate_normalForm
        candidate
  have inputDerivative :
      fderiv ℝ
          fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm
          point =
        (fderiv ℝ CanonicalInput.coframe point).prod
          (fderiv ℝ
            fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm
            point) := by
    change
      fderiv ℝ
          (fun candidate =>
            (CanonicalInput.coframe candidate,
              fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm
                candidate)) point = _
    exact coframeDifferentiable.fderiv_prodMk curvatureDifferentiable
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [auxiliaryFunction, composed.fderiv]
  funext direction
  unfold fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryFirstJetNormalForm
  apply congrArg
    (fderiv ℝ fixedP506L0P286CanonicalGeneratedConstitutiveInverse
      (fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm point))
  have applied := congrArg
    (fun derivative : BasePoint →L[ℝ]
        (LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm) =>
      derivative (coordinateDirection direction)) inputDerivative
  change
    (fderiv ℝ
        fixedP506L0P286CanonicalGeneratedCoframeCurvatureInputNormalForm
        point) (coordinateDirection direction) =
      ((fderiv ℝ CanonicalInput.coframe point)
          (coordinateDirection direction),
        (fderiv ℝ
          fixedP506L0P286CanonicalGeneratedGaugeCurvatureCoordinateNormalForm
          point) (coordinateDirection direction))
  exact applied

/-! ## Whole `D_A B` package -/

/-- Whole-carrier normal form of the post-write P286 exterior covariant
derivative. -/
def
    fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryExteriorCovariantDerivativeNormalForm
    (point : BasePoint) : P286GaugeThreeForm :=
  pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    (fixedP506L0P286CanonicalGeneratedGaugeConnectionCoordinateNormalForm
      point)
    (fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryCoordinateNormalForm point)
    (fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryFirstJetNormalForm point)

theorem
    fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryExteriorCovariantDerivative_normalForm
    (point : BasePoint)
    (nondegenerate : Matrix.det (CanonicalInput.coframe point) ≠ 0) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative CanonicalActual
        point =
      fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryExteriorCovariantDerivativeNormalForm
        point := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
  rw [
    fixedP506L0P286CanonicalGeneratedActual_gaugeConnectionCoordinate_normalForm,
    fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryCoordinate_normalForm,
    fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryFirstJet_normalForm
      point nondegenerate]
  rfl

/-- The previously exposed whole action-jet carrier now has its live P286
differential slot filled by the same generated normal form. -/
theorem
    fixedP506L0P286CanonicalGeneratedPointwiseActionJetNormalForm_p286GaugeAuxiliary
    (point : BasePoint)
    (nondegenerate : Matrix.det (CanonicalInput.coframe point) ≠ 0) :
    (fixedP506L0P286CanonicalGeneratedPointwiseActionJetNormalForm point
      ).p286GaugeAuxiliaryExteriorCovariantDerivative =
      fixedP506L0P286CanonicalGeneratedGaugeAuxiliaryExteriorCovariantDerivativeNormalForm
        point := by
  change
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative CanonicalActual
        point = _
  exact
    fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryExteriorCovariantDerivative_normalForm
      point nondegenerate

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualP286AuxiliaryFirstJet
