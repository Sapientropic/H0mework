import H0mework.Physics.ConnectionJets.P286ColorCartanQuadraticConnectionJet
import H0mework.Physics.Cartan.P286ColorCartanOffsetBoundary
import H0mework.Physics.GaugeAction.P286VaryingCurvatureAuxiliaryGraph

/-!
# S9-C3h78b: synchronized P286 constitutive response

This production module follows the existing C3h78a connection second jet
through the already-defined P286 constitutive graph.  At every point the
auxiliary is recomputed from the varied connection's actual `dA + [A,A]`
curvature; it is not frozen at the C3h70 value and is not accepted as source
data.

The real parameter below is only a coordinate for classifying the actual
Euler--Lagrange residual fiber.  The terminal physical configuration must read
its coefficient from that residual and its nonzero response slope.  This file
does not add a source slot, constitutive field, coupling, target, inverse,
branch receipt, or stationarity certificate.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineP286ColorCartanConstitutiveResponse

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineCoframeGravityGaugeRegularity
open StageNineConnectionSectorSourceBalance
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAlgebraicKeepResponseCoframeDefect
open StageNineGravityAlgebraicKeepResponseP286Defect
open StageNineHolonomicField
open StageNineP286ColorCartanOffsetBoundary
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286SourceAffineCurvatureJetNormalForm
open StageNineP286VaryingCurvatureAuxiliaryGraph
open StageNinePositiveSourceNativeAlgebraicEliminationRegularity
open StageNinePositiveSourceNativeAlgebraicEliminationUpdate
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitP286BFBalanceDecision
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Existing constitutive graph synchronized to the actual varied curvature -/

/-- Recompute only the derived P286 auxiliary of an existing configuration.
This is a deterministic constitutive readout, not a new primitive field. -/
def synchronizeP286ConstitutiveAuxiliary
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gaugeAuxiliary := fun point =>
      generatedP286GaugeConstitutiveAuxiliary positiveSmoothUnifiedSource
        (configuration.coframe point)
        (holonomicGaugeCurvature configuration point) }

@[simp] theorem synchronizeP286ConstitutiveAuxiliary_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (synchronizeP286ConstitutiveAuxiliary configuration).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem synchronizeP286ConstitutiveAuxiliary_gaugeConnection
    (configuration : StageNineHolonomicConfiguration) :
    (synchronizeP286ConstitutiveAuxiliary configuration).gaugeConnection =
      configuration.gaugeConnection :=
  rfl

theorem synchronizeP286ConstitutiveAuxiliary_gaugeAuxiliary
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    (synchronizeP286ConstitutiveAuxiliary configuration).gaugeAuxiliary point =
      generatedP286GaugeConstitutiveAuxiliary positiveSmoothUnifiedSource
        (configuration.coframe point)
        (holonomicGaugeCurvature configuration point) :=
  rfl

theorem synchronizeP286ConstitutiveAuxiliary_curvature
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    holonomicGaugeCurvature
        (synchronizeP286ConstitutiveAuxiliary configuration) point =
      holonomicGaugeCurvature configuration point := by
  funext pair
  unfold holonomicGaugeCurvature p286ConnectionDerivative
  rfl

theorem synchronizeP286ConstitutiveAuxiliary_solves
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryEquationResidual positiveSmoothUnifiedSource
        (synchronizeP286ConstitutiveAuxiliary configuration) point = 0 := by
  apply (holonomicP286GaugeAuxiliaryResidual_eq_zero_iff_eq_generated
    positiveSmoothUnifiedSource
    (synchronizeP286ConstitutiveAuxiliary configuration) point
    (by
      simpa only [synchronizeP286ConstitutiveAuxiliary_coframe] using
        nondegenerate point)).2
  rw [synchronizeP286ConstitutiveAuxiliary_gaugeAuxiliary,
    synchronizeP286ConstitutiveAuxiliary_coframe,
    synchronizeP286ConstitutiveAuxiliary_curvature]

/-- Smoothness of the actual curvature after applying the complete
coframe-dependent Hodge operator. -/
theorem synchronizeP286ConstitutiveAuxiliary_hodgeCurvature_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞ fun point =>
      liftGaugeTwoFormOperator
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (fun pair => p286CoordinateEquiv
          (holonomicGaugeCurvature configuration point pair)) := by
  let curvatureCoordinate : BasePoint → Fin 6 → P286CoordinateCarrier :=
    fun point pair =>
      p286CoordinateEquiv (holonomicGaugeCurvature configuration point pair)
  have curvatureSmooth : ContDiff ℝ ∞ curvatureCoordinate := by
    apply contDiff_pi'
    intro pair
    exact holonomicGaugeCurvature_coordinate_contDiff
      configuration smooth pair
  change ContDiff ℝ ∞ fun point =>
    liftGaugeTwoFormOperator
      (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
      (curvatureCoordinate point)
  apply contDiff_pi'
  intro output
  unfold liftGaugeTwoFormOperator
  apply ContDiff.sum
  intro input _
  have coefficientSmooth : ContDiff ℝ ∞ fun point =>
      gaugeOperatorCoefficient
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        output input := by
    let basis : GaugeTwoForm := fun candidate =>
      if candidate = input then 1 else 0
    have actual := holonomicGaugeSpacetimeHodge_apply_contDiff
      configuration smooth nondegenerate (fun _ => basis) contDiff_const
    exact contDiff_pi.mp actual output
  exact coefficientSmooth.smul (contDiff_pi.mp curvatureSmooth input)

theorem synchronizeP286ConstitutiveAuxiliary_gaugeAuxiliary_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ∀ pair,
      ContDiff ℝ ∞ fun point =>
        p286CoordinateEquiv
          ((synchronizeP286ConstitutiveAuxiliary
            configuration).gaugeAuxiliary point pair) := by
  have hodgeSmooth :=
    synchronizeP286ConstitutiveAuxiliary_hodgeCurvature_smooth
      configuration smooth nondegenerate
  have coordinateAuxiliarySmooth : ContDiff ℝ ∞ fun point =>
      p286GaugeConstitutiveAuxiliaryCoordinate
        positiveSmoothUnifiedSource
        (configuration.coframe point)
        (fun pair => p286CoordinateEquiv
          (holonomicGaugeCurvature configuration point pair)) := by
    simpa [p286GaugeConstitutiveAuxiliaryCoordinate] using
      ((contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
          (((sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)⁻¹))
        |>.smul hodgeSmooth |>.neg)
  intro pair
  simpa [synchronizeP286ConstitutiveAuxiliary,
    generatedP286GaugeConstitutiveAuxiliary] using
      (contDiff_pi.mp coordinateAuxiliarySmooth pair)

theorem synchronizeP286ConstitutiveAuxiliary_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    (synchronizeP286ConstitutiveAuxiliary configuration).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, _oldGaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    gravityMultiplierSmooth, gaugeConnectionSmooth,
    synchronizeP286ConstitutiveAuxiliary_gaugeAuxiliary_smooth
      configuration
      ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
        gravityMultiplierSmooth, gaugeConnectionSmooth,
        _oldGaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
        conjugateMatterSmooth⟩
      nondegenerate,
    scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

/-- Follow the C3h78a primitive connection jet through the existing
constitutive graph. -/
def colorCartanQuadraticConstitutiveResponse (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  synchronizeP286ConstitutiveAuxiliary
    (colorCartanQuadraticKinematic parameter)

@[simp] theorem colorCartanQuadraticConstitutiveResponse_coframe
    (parameter : ℝ) :
    (colorCartanQuadraticConstitutiveResponse parameter).coframe =
      canonicalResponse.coframe :=
  rfl

@[simp] theorem colorCartanQuadraticConstitutiveResponse_gaugeConnection
    (parameter : ℝ) :
    (colorCartanQuadraticConstitutiveResponse parameter).gaugeConnection =
      (colorCartanQuadraticKinematic parameter).gaugeConnection :=
  rfl

theorem colorCartanQuadraticConstitutiveResponse_gaugeAuxiliary
    (parameter : ℝ) (point : BasePoint) :
    (colorCartanQuadraticConstitutiveResponse parameter).gaugeAuxiliary point =
      generatedP286GaugeConstitutiveAuxiliary positiveSmoothUnifiedSource
        ((colorCartanQuadraticKinematic parameter).coframe point)
        (holonomicGaugeCurvature
          (colorCartanQuadraticKinematic parameter) point) :=
  synchronizeP286ConstitutiveAuxiliary_gaugeAuxiliary _ point

theorem colorCartanQuadraticConstitutiveResponse_auxiliaryCoordinate
    (parameter : ℝ) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (colorCartanQuadraticConstitutiveResponse parameter) point =
      p286GaugeConstitutiveAuxiliaryCoordinate
        positiveSmoothUnifiedSource
        (canonicalPhysicalSource.coframeAt point)
        (holonomicP286GaugeCurvatureCoordinate
          (colorCartanQuadraticConstitutiveResponse parameter) point) := by
  funext pair
  simp only [holonomicP286GaugeAuxiliaryCoordinate,
    colorCartanQuadraticConstitutiveResponse_gaugeAuxiliary,
    generatedP286GaugeConstitutiveAuxiliary,
    p286CoordinateEquiv.apply_symm_apply]
  have coframeEquality :
      (colorCartanQuadraticKinematic parameter).coframe point =
        canonicalPhysicalSource.coframeAt point := by
    have synchronized := congrFun
      (synchronizeP286ConstitutiveAuxiliary_coframe
        (colorCartanQuadraticKinematic parameter)) point
    have responseCoframe := congrFun
      (colorCartanQuadraticConstitutiveResponse_coframe parameter) point
    have canonicalCoframe :
        canonicalResponse.coframe point =
          canonicalPhysicalSource.coframeAt point := by
      rfl
    exact synchronized.symm.trans
      (responseCoframe.trans canonicalCoframe)
  have curvatureEquality :
      (fun candidate => p286CoordinateEquiv
        (holonomicGaugeCurvature
          (colorCartanQuadraticKinematic parameter) point candidate)) =
        holonomicP286GaugeCurvatureCoordinate
          (colorCartanQuadraticConstitutiveResponse parameter) point := by
    funext candidate
    exact congrArg p286CoordinateEquiv
      (congrFun
        (synchronizeP286ConstitutiveAuxiliary_curvature
          (colorCartanQuadraticKinematic parameter) point).symm
        candidate)
  rw [coframeEquality, curvatureEquality]

theorem colorCartanQuadraticConstitutiveResponse_preserves_otherFields
    (parameter : ℝ) :
    (colorCartanQuadraticConstitutiveResponse parameter).gravityConnection =
        canonicalResponse.gravityConnection ∧
      (colorCartanQuadraticConstitutiveResponse parameter).gravityAuxiliary =
        canonicalResponse.gravityAuxiliary ∧
      (colorCartanQuadraticConstitutiveResponse
        parameter).gravitySimplicityMultiplier =
          canonicalResponse.gravitySimplicityMultiplier ∧
      (colorCartanQuadraticConstitutiveResponse parameter).scalar =
        canonicalResponse.scalar ∧
      (colorCartanQuadraticConstitutiveResponse parameter).matter =
        canonicalResponse.matter ∧
      (colorCartanQuadraticConstitutiveResponse parameter).conjugateMatter =
        canonicalResponse.conjugateMatter := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colorCartanQuadraticConstitutiveResponse_nondegenerate
    (parameter : ℝ) :
    (colorCartanQuadraticConstitutiveResponse parameter).Nondegenerate := by
  intro point
  change Matrix.det (canonicalResponse.coframe point) ≠ 0
  change Matrix.det (positiveSmoothUnifiedSource.legacy.coframeAt point) ≠ 0
  exact canonicalPhysicalSource_globally_nondegenerate point

theorem colorCartanQuadraticConstitutiveResponse_smooth
    (parameter : ℝ) :
    (colorCartanQuadraticConstitutiveResponse parameter).Smooth := by
  apply synchronizeP286ConstitutiveAuxiliary_smooth
  · exact colorCartanQuadraticKinematic_smooth parameter
  · intro point
    change Matrix.det
      (positiveSmoothUnifiedSource.legacy.coframeAt point) ≠ 0
    exact canonicalPhysicalSource_globally_nondegenerate point

theorem colorCartanQuadraticConstitutiveResponse_auxiliaryEquation
    (parameter : ℝ) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryEquationResidual positiveSmoothUnifiedSource
      (colorCartanQuadraticConstitutiveResponse parameter) point = 0 :=
  synchronizeP286ConstitutiveAuxiliary_solves
    (colorCartanQuadraticKinematic parameter)
    (by
      intro basePoint
      change
        Matrix.det
            (positiveSmoothUnifiedSource.legacy.coframeAt basePoint) ≠ 0
      exact canonicalPhysicalSource_globally_nondegenerate basePoint)
    point

theorem colorCartanQuadraticConstitutiveResponse_connection_origin
    (parameter : ℝ) :
    (colorCartanQuadraticConstitutiveResponse parameter).gaugeConnection 0 =
      canonicalResponse.gaugeConnection 0 :=
  colorCartanQuadraticKinematic_gaugeConnection_origin parameter

theorem colorCartanQuadraticConstitutiveResponse_curvature_origin
    (parameter : ℝ) :
    holonomicGaugeCurvature
        (colorCartanQuadraticConstitutiveResponse parameter) 0 =
      holonomicGaugeCurvature canonicalResponse 0 := by
  calc
    holonomicGaugeCurvature
        (colorCartanQuadraticConstitutiveResponse parameter) 0 =
        holonomicGaugeCurvature (colorCartanQuadraticKinematic parameter) 0 := by
      exact synchronizeP286ConstitutiveAuxiliary_curvature _ 0
    _ = holonomicGaugeCurvature canonicalResponse 0 :=
      colorCartanQuadraticKinematic_curvature_origin parameter

theorem colorCartanQuadraticConstitutiveResponse_auxiliary_origin
    (parameter : ℝ) :
    (colorCartanQuadraticConstitutiveResponse parameter).gaugeAuxiliary 0 =
      canonicalResponse.gaugeAuxiliary 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  change
    holonomicP286GaugeAuxiliaryCoordinate
        (colorCartanQuadraticConstitutiveResponse parameter) 0 pair =
      holonomicP286GaugeAuxiliaryCoordinate
        canonicalSourceNativeP286Input 0 pair
  rw [congrFun
      (colorCartanQuadraticConstitutiveResponse_auxiliaryCoordinate parameter 0)
      pair,
    congrFun (actualNativeAuxiliaryCoordinate_eq_constitutive 0) pair]
  have curvatureCoordinateEquality :
      holonomicP286GaugeCurvatureCoordinate
          (colorCartanQuadraticConstitutiveResponse parameter) 0 =
        actualNativeCurvatureCoordinate 0 := by
    funext candidate
    change p286CoordinateEquiv
        (holonomicGaugeCurvature
          (colorCartanQuadraticConstitutiveResponse parameter) 0 candidate) =
      p286CoordinateEquiv
        (holonomicGaugeCurvature canonicalResponse 0 candidate)
    exact congrArg p286CoordinateEquiv
      (congrFun
        (colorCartanQuadraticConstitutiveResponse_curvature_origin parameter)
        candidate)
  rw [curvatureCoordinateEquality]

theorem colorCartanQuadraticConstitutiveResponse_pointField_origin
    (parameter : ℝ) :
    toContinuumPointField
        (colorCartanQuadraticConstitutiveResponse parameter) 0 =
      toContinuumPointField canonicalResponse 0 := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · exact colorCartanQuadraticConstitutiveResponse_curvature_origin parameter
  · exact colorCartanQuadraticConstitutiveResponse_auxiliary_origin parameter
  · rfl
  · funext direction
    change holonomicScalarCovariantDerivative
        (colorCartanQuadraticConstitutiveResponse parameter) 0 direction =
      holonomicScalarCovariantDerivative canonicalResponse 0 direction
    unfold holonomicScalarCovariantDerivative
    rw [colorCartanQuadraticConstitutiveResponse_connection_origin parameter]
    rfl
  · rfl
  · funext direction
    change holonomicMatterCovariantDerivative
        (colorCartanQuadraticConstitutiveResponse parameter) 0 direction =
      holonomicMatterCovariantDerivative canonicalResponse 0 direction
    unfold holonomicMatterCovariantDerivative
    rw [colorCartanQuadraticConstitutiveResponse_connection_origin parameter]
    rfl
  · rfl

theorem colorCartanQuadraticConstitutiveResponse_p286BFAlgebraic_eq_zero
    (parameter : ℝ) :
    p286GaugeBFAlgebraicCoefficient
        (colorCartanQuadraticConstitutiveResponse parameter)
        colorCartanMuZeroDirection 0 = 0 := by
  have coframeEquality :
      (colorCartanQuadraticConstitutiveResponse parameter).coframe 0 =
        canonicalResponse.coframe 0 :=
    congrFun
      (colorCartanQuadraticConstitutiveResponse_coframe parameter) 0
  have auxiliaryCoordinateEquality :
      holonomicP286GaugeAuxiliaryCoordinate
          (colorCartanQuadraticConstitutiveResponse parameter) 0 =
        holonomicP286GaugeAuxiliaryCoordinate canonicalResponse 0 := by
    funext pair
    exact congrArg p286CoordinateEquiv
      (congrFun
        (colorCartanQuadraticConstitutiveResponse_auxiliary_origin parameter)
        pair)
  have algebraicDirectionEquality :
      p286GaugeConnectionAlgebraicCurvatureDirection
          (colorCartanQuadraticConstitutiveResponse parameter)
          colorCartanMuZeroDirection 0 =
        p286GaugeConnectionAlgebraicCurvatureDirection canonicalResponse
          colorCartanMuZeroDirection 0 := by
    funext pair
    unfold p286GaugeConnectionAlgebraicCurvatureDirection
      p286GaugeConnectionAlgebraicCurvatureVariation
      holonomicP286GaugeConnectionCoordinate
    rw [colorCartanQuadraticConstitutiveResponse_connection_origin parameter]
  unfold p286GaugeBFAlgebraicCoefficient
  rw [colorCartanQuadraticConstitutiveResponse_pointField_origin,
    coframeEquality, auxiliaryCoordinateEquality, algebraicDirectionEquality]
  exact canonicalResponse_colorCartanMuZero_p286BFAlgebraic_eq_zero

theorem colorCartanQuadraticConstitutiveResponse_p286ScalarCurrent_eq_zero
    (parameter : ℝ) :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
        (colorCartanQuadraticConstitutiveResponse parameter)
        colorCartanMuZeroDirection 0 = 0 := by
  unfold p286ScalarCurrentCoefficient
  rw [colorCartanQuadraticConstitutiveResponse_pointField_origin]
  change p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
      canonicalResponse colorCartanMuZeroDirection 0 = 0
  exact canonicalResponse_colorCartanMuZero_p286ScalarCurrent_eq_zero

theorem colorCartanQuadraticConstitutiveResponse_p286MatterCurrent_eq_zero
    (parameter : ℝ) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        (colorCartanQuadraticConstitutiveResponse parameter)
        colorCartanMuZeroDirection 0 = 0 := by
  unfold p286MatterCurrentCoefficient
  rw [colorCartanQuadraticConstitutiveResponse_pointField_origin]
  change p286MatterCurrentCoefficient positiveSmoothUnifiedSource
      canonicalResponse colorCartanMuZeroDirection 0 = 0
  exact canonicalResponse_colorCartanMuZero_p286MatterCurrent_eq_zero

/-! ## Constitutive BF momentum for the actual varied curvature -/

theorem colorCartanQuadraticConstitutiveResponse_p286Momentum_normalForm
    (parameter : ℝ) (direction : P286GaugeTwoForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (colorCartanQuadraticConstitutiveResponse parameter)
        direction point =
      2 * ∑ pair : Fin 6,
        lorentzianTwoFormSign pair *
          p286CoordinateLiePairing
            (liftGaugeTwoFormOperator
              (coframeTwoFormLinear
                (canonicalPhysicalSource.coframeAt point))
              (holonomicP286GaugeCurvatureCoordinate
                (colorCartanQuadraticConstitutiveResponse parameter) point)
              pair)
            (liftGaugeTwoFormOperator
              (coframeTwoFormLinear
                (canonicalPhysicalSource.coframeAt point))
              direction pair) := by
  unfold p286GaugeConnectionBFDifferentialMomentum
  change
    abs (Matrix.det
        ((colorCartanQuadraticConstitutiveResponse parameter).coframe point)) *
        p286GaugeAuxiliaryHodgePairingPolynomial
          ((colorCartanQuadraticConstitutiveResponse parameter).coframe point)
          (holonomicP286GaugeAuxiliaryCoordinate
            (colorCartanQuadraticConstitutiveResponse parameter) point)
          direction = _
  have coframeEquality :
      (colorCartanQuadraticConstitutiveResponse parameter).coframe point =
        canonicalPhysicalSource.coframeAt point := by
    have responseCoframe := congrFun
      (colorCartanQuadraticConstitutiveResponse_coframe parameter) point
    have canonicalCoframe :
        canonicalResponse.coframe point =
          canonicalPhysicalSource.coframeAt point := by
      rfl
    exact responseCoframe.trans canonicalCoframe
  rw [coframeEquality,
    colorCartanQuadraticConstitutiveResponse_auxiliaryCoordinate,
    canonicalPhysicalSource_coframeAt_det]
  simp only [abs_one, one_mul]
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  unfold p286GaugeConstitutiveAuxiliaryCoordinate
  have couplingInverse :
      (((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)⁻¹) = 2 := by
    change (positiveSmoothUnifiedSource.legacy.sigma)⁻¹ = 2
    rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half]
    norm_num
  rw [couplingInverse]
  simp_rw [liftGaugeTwoFormOperator_smul_p286]
  simp_rw [liftCoframe_dynamicHodge_p286
    (canonicalPhysicalSource.coframeAt point)
    (canonicalPhysicalSource_globally_nondegenerate point)
    (holonomicP286GaugeCurvatureCoordinate
      (colorCartanQuadraticConstitutiveResponse parameter) point)]
  simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_left]
  let framedCurvature :=
    liftGaugeTwoFormOperator
      (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
      (holonomicP286GaugeCurvatureCoordinate
        (colorCartanQuadraticConstitutiveResponse parameter) point)
  let framedDirection :=
    liftGaugeTwoFormOperator
      (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
      direction
  calc
    (∑ pair : Fin 6,
      lorentzianTwoFormSign pair *
        (-2 * p286CoordinateLiePairing
          (liftGaugeTwoFormOperator lorentzianCoframeHodge
            framedCurvature pair)
          (liftGaugeTwoFormOperator lorentzianCoframeHodge
            framedDirection pair))) =
      -2 * ∑ pair : Fin 6,
        lorentzianTwoFormSign pair *
          p286CoordinateLiePairing
            (liftGaugeTwoFormOperator lorentzianCoframeHodge
              framedCurvature pair)
            (liftGaugeTwoFormOperator lorentzianCoframeHodge
              framedDirection pair) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pair _
        ring
    _ = 2 * ∑ pair : Fin 6,
        lorentzianTwoFormSign pair *
          p286CoordinateLiePairing (framedCurvature pair)
            (framedDirection pair) := by
      rw [p286FixedHodge_pairing_pairing_local]
      ring
    _ = _ := rfl

def colorCartanQuadraticResponseCurvatureCoordinate
    (parameter : ℝ) (point : BasePoint) : P286GaugeTwoForm :=
  holonomicP286GaugeCurvatureCoordinate
    (colorCartanQuadraticConstitutiveResponse parameter) point

theorem colorCartanQuadraticResponseCurvatureCoordinate_eq_kinematic
    (parameter : ℝ) (point : BasePoint) :
    colorCartanQuadraticResponseCurvatureCoordinate parameter point =
      holonomicP286GaugeCurvatureCoordinate
        (colorCartanQuadraticKinematic parameter) point := by
  funext pair
  exact congrArg p286CoordinateEquiv
    (congrFun
      (synchronizeP286ConstitutiveAuxiliary_curvature
        (colorCartanQuadraticKinematic parameter) point)
      pair)

theorem colorCartanQuadraticCoordinate_pairing_self :
    p286CoordinateLiePairing colorCartanQuadraticCoordinate
        colorCartanQuadraticCoordinate = 2 := by
  unfold colorCartanQuadraticCoordinate p286CoordinateLiePairing
  rw [p286CoordinateEquiv.symm_apply_apply]
  simp only [p286LiePairing, colorCartanP286ConnectionDirection]
  rw [colorCartanGenerator_pairing_self]
  simp [specialUnitaryLiePairing, hyperchargeLiePairing]

theorem colorCartanQuadraticMomentum_direction_zero
    (parameter : ℝ) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (colorCartanQuadraticConstitutiveResponse parameter)
        (p286GaugeExteriorDerivativeDirection 0 colorCartanMuZeroDirection)
        point = 0 := by
  rw [colorCartanQuadraticConstitutiveResponse_p286Momentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [p286GaugeExteriorDerivativeDirection, colorCartanMuZeroDirection,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond]

theorem colorCartanQuadraticMomentum_direction_one
    (parameter : ℝ) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (colorCartanQuadraticConstitutiveResponse parameter)
        (p286GaugeExteriorDerivativeDirection 1 colorCartanMuZeroDirection)
        point =
      2 * p286CoordinateLiePairing
        (colorCartanQuadraticResponseCurvatureCoordinate parameter point 0)
        (p286CoordinateEquiv colorCartanP286ConnectionDirection) := by
  rw [colorCartanQuadraticConstitutiveResponse_p286Momentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [colorCartanQuadraticResponseCurvatureCoordinate,
    p286GaugeExteriorDerivativeDirection, colorCartanMuZeroDirection,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

theorem colorCartanQuadraticMomentum_direction_two
    (parameter : ℝ) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (colorCartanQuadraticConstitutiveResponse parameter)
        (p286GaugeExteriorDerivativeDirection 2 colorCartanMuZeroDirection)
        point =
      2 * p286CoordinateLiePairing
        (colorCartanQuadraticResponseCurvatureCoordinate parameter point 1 +
          point 2 •
            colorCartanQuadraticResponseCurvatureCoordinate parameter point 5)
        (p286CoordinateEquiv colorCartanP286ConnectionDirection) := by
  rw [colorCartanQuadraticConstitutiveResponse_p286Momentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [colorCartanQuadraticResponseCurvatureCoordinate,
    p286GaugeExteriorDerivativeDirection, colorCartanMuZeroDirection,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

theorem colorCartanQuadraticMomentum_direction_three
    (parameter : ℝ) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (colorCartanQuadraticConstitutiveResponse parameter)
        (p286GaugeExteriorDerivativeDirection 3 colorCartanMuZeroDirection)
        point =
      2 * p286CoordinateLiePairing
        (colorCartanQuadraticResponseCurvatureCoordinate parameter point 2 -
          point 2 •
            colorCartanQuadraticResponseCurvatureCoordinate parameter point 4)
        (p286CoordinateEquiv colorCartanP286ConnectionDirection) := by
  rw [colorCartanQuadraticConstitutiveResponse_p286Momentum_normalForm,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [colorCartanQuadraticResponseCurvatureCoordinate,
    p286GaugeExteriorDerivativeDirection, colorCartanMuZeroDirection,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

theorem colorCartanQuadraticMomentum_direction_zero_derivative_eq_zero
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 0 colorCartanMuZeroDirection))
        0 0 = 0 := by
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 0 colorCartanMuZeroDirection) =
        fun _ => 0 := by
    funext point
    exact colorCartanQuadraticMomentum_direction_zero parameter point
  rw [momentumFunction]
  simp [fieldDirectionalDerivative]

theorem colorCartanQuadraticResponseCurvature_pair_zero_direction_one
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (fun point =>
          colorCartanQuadraticResponseCurvatureCoordinate parameter point 0)
        0 1 =
      fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeCurvatureCoordinate canonicalResponse point 0)
          0 1 +
        parameter • ((-2 : ℝ) • colorCartanQuadraticCoordinate) := by
  have functionEquality :
      (fun point =>
        colorCartanQuadraticResponseCurvatureCoordinate parameter point 0) =
      fun point =>
        holonomicP286GaugeCurvatureCoordinate
          (colorCartanQuadraticKinematic parameter) point 0 := by
    funext point
    exact congrFun
      (colorCartanQuadraticResponseCurvatureCoordinate_eq_kinematic
        parameter point) 0
  rw [functionEquality]
  exact colorCartanQuadraticKinematic_curvature_pair_zero_direction_one
    parameter

theorem colorCartanQuadraticMomentum_direction_one_derivative
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 1 colorCartanMuZeroDirection))
        0 1 = -1 - 8 * parameter := by
  let curvatureField : BasePoint → P286CoordinateCarrier := fun point =>
    colorCartanQuadraticResponseCurvatureCoordinate parameter point 0
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (curvatureField point)
      colorCartanQuadraticCoordinate
  have curvatureSmooth : ContDiff ℝ ∞ curvatureField := by
    exact holonomicGaugeCurvature_coordinate_contDiff
      (colorCartanQuadraticConstitutiveResponse parameter)
      (colorCartanQuadraticConstitutiveResponse_smooth parameter) 0
  have curvatureDifferentiableAt :
      DifferentiableAt ℝ curvatureField (0 : BasePoint) :=
    (curvatureSmooth.differentiable (by simp)).differentiableAt
  have pairingHasDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear curvatureDifferentiableAt.hasFDerivAt
        (hasFDerivAt_const colorCartanQuadraticCoordinate 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 := by
    exact pairingHasDerivative.differentiableAt
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 1 colorCartanMuZeroDirection) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact colorCartanQuadraticMomentum_direction_one parameter point
  have backgroundPairing :
      p286CoordinateLiePairing
          (fieldDirectionalDerivative
            (fun point =>
              holonomicP286GaugeCurvatureCoordinate canonicalResponse point 0)
            0 1)
          colorCartanQuadraticCoordinate = -(1 / 2 : ℝ) := by
    change p286CoordinateLiePairing
      (fieldDirectionalDerivative
        (fun point => actualNativeCurvatureCoordinate point 0) 0 1)
      (p286CoordinateEquiv colorCartanP286ConnectionDirection) = _
    exact
      actualNativeCurvature_zero_direction_one_pairing_colorCartan_eq_neg_half
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 1 =
    -1 - 8 * parameter
  rw [fieldDirectionalDerivative_pairing_const_local curvatureField
    (fderiv ℝ curvatureField 0) 0 1 colorCartanQuadraticCoordinate
    curvatureDifferentiableAt.hasFDerivAt]
  change 2 * p286CoordinateLiePairing
      (fieldDirectionalDerivative
        (fun point =>
          colorCartanQuadraticResponseCurvatureCoordinate parameter point 0)
        0 1)
      colorCartanQuadraticCoordinate = _
  rw [colorCartanQuadraticResponseCurvature_pair_zero_direction_one,
    p286CoordinateLiePairing_add_left,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_left,
    backgroundPairing,
    colorCartanQuadraticCoordinate_pairing_self]
  ring

theorem colorCartanQuadraticJet_variationDerivative_zero_of_direction_ne_one
    (point : BasePoint) (derivativeDirection : LorentzianIndex)
    (directionNe : derivativeDirection ≠ 1) :
    p286GaugeVariationCoordinateDerivative colorCartanQuadraticJet point
        derivativeDirection 0 = 0 := by
  have functionEquality :
      (fun candidate => colorCartanQuadraticJet candidate 0) =
        fun candidate => colorCartanQuadraticCoefficient candidate •
          colorCartanQuadraticCoordinate := by
    funext candidate
    simp [colorCartanQuadraticJet]
  have derivative :=
    (colorCartanQuadraticCoefficient_hasFDerivAt point).smul_const
      colorCartanQuadraticCoordinate
  unfold p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  rw [functionEquality, derivative.fderiv]
  simp [p286BaseCoordinate_apply, coordinateDirection, directionNe]

theorem colorCartanQuadraticLinearCurvatureVariation_pair_one
    (point : BasePoint) :
    p286GaugeConnectionLinearCurvatureVariation canonicalResponse
        colorCartanQuadraticJet point 1 =
      colorCartanQuadraticCoefficient point •
        p286CoordinateLieBracket colorCartanQuadraticCoordinate
          (actualSourceAffineCoordinate 2 point) := by
  unfold p286GaugeConnectionLinearCurvatureVariation
  change
    p286GaugeVariationCoordinateDerivative colorCartanQuadraticJet point 0 2 -
        p286GaugeVariationCoordinateDerivative colorCartanQuadraticJet
          point 2 0 +
      p286CoordinateLieBracket (colorCartanQuadraticJet point 0)
          (holonomicP286GaugeConnectionCoordinate canonicalResponse point 2) +
      p286CoordinateLieBracket
          (holonomicP286GaugeConnectionCoordinate canonicalResponse point 0)
          (colorCartanQuadraticJet point 2) = _
  rw [colorCartanQuadraticJet_variationDerivative_of_form_ne_zero
      point 0 2 (by decide),
    colorCartanQuadraticJet_variationDerivative_zero_of_direction_ne_one
      point 2 (by decide),
    canonicalResponse_p286ConnectionCoordinate_eq_actual point 2]
  simp [colorCartanQuadraticJet,
    p286CoordinateLieBracket_smul_left]

theorem colorCartanQuadraticLinearCurvatureVariation_pair_two
    (point : BasePoint) :
    p286GaugeConnectionLinearCurvatureVariation canonicalResponse
        colorCartanQuadraticJet point 2 =
      colorCartanQuadraticCoefficient point •
        p286CoordinateLieBracket colorCartanQuadraticCoordinate
          (actualSourceAffineCoordinate 3 point) := by
  unfold p286GaugeConnectionLinearCurvatureVariation
  change
    p286GaugeVariationCoordinateDerivative colorCartanQuadraticJet point 0 3 -
        p286GaugeVariationCoordinateDerivative colorCartanQuadraticJet
          point 3 0 +
      p286CoordinateLieBracket (colorCartanQuadraticJet point 0)
          (holonomicP286GaugeConnectionCoordinate canonicalResponse point 3) +
      p286CoordinateLieBracket
          (holonomicP286GaugeConnectionCoordinate canonicalResponse point 0)
          (colorCartanQuadraticJet point 3) = _
  rw [colorCartanQuadraticJet_variationDerivative_of_form_ne_zero
      point 0 3 (by decide),
    colorCartanQuadraticJet_variationDerivative_zero_of_direction_ne_one
      point 3 (by decide),
    canonicalResponse_p286ConnectionCoordinate_eq_actual point 3]
  simp [colorCartanQuadraticJet,
    p286CoordinateLieBracket_smul_left]

theorem colorCartanQuadraticResponseCurvatureCoordinate_expansion
    (parameter : ℝ) (point : BasePoint) :
    colorCartanQuadraticResponseCurvatureCoordinate parameter point =
      holonomicP286GaugeCurvatureCoordinate canonicalResponse point +
        parameter •
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
            colorCartanQuadraticJet point := by
  rw [colorCartanQuadraticResponseCurvatureCoordinate_eq_kinematic]
  exact colorCartanQuadraticKinematic_curvatureCoordinate_expansion
    parameter point

theorem colorCartanQuadraticLinearCurvature_component_contDiff
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      p286GaugeConnectionLinearCurvatureVariation canonicalResponse
        colorCartanQuadraticJet point pair := by
  have variedSmooth : ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeCurvatureCoordinate
        (colorCartanQuadraticKinematic 1) point pair :=
    holonomicGaugeCurvature_coordinate_contDiff
      (colorCartanQuadraticKinematic 1)
      (colorCartanQuadraticKinematic_smooth 1) pair
  have backgroundSmooth : ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeCurvatureCoordinate canonicalResponse point pair :=
    holonomicGaugeCurvature_coordinate_contDiff canonicalResponse
      canonicalResponse_smooth_local pair
  have functionEquality :
      (fun point =>
        p286GaugeConnectionLinearCurvatureVariation canonicalResponse
          colorCartanQuadraticJet point pair) =
        fun point =>
          holonomicP286GaugeCurvatureCoordinate
              (colorCartanQuadraticKinematic 1) point pair -
            holonomicP286GaugeCurvatureCoordinate
              canonicalResponse point pair := by
    funext point
    have expanded := congrFun
      (colorCartanQuadraticKinematic_curvatureCoordinate_expansion 1 point)
      pair
    simp only [Pi.add_apply, one_smul] at expanded
    rw [eq_sub_iff_add_eq, add_comm]
    exact expanded.symm
  rw [functionEquality]
  exact variedSmooth.sub backgroundSmooth

theorem colorCartanQuadraticLinearCurvature_component_origin
    (pair : Fin 6) :
    p286GaugeConnectionLinearCurvatureVariation canonicalResponse
        colorCartanQuadraticJet 0 pair = 0 :=
  congrFun colorCartanQuadraticLinearCurvatureVariation_origin pair

theorem colorCartanQuadraticLinearCurvature_pair_one_derivative_origin
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
            colorCartanQuadraticJet point 1)
        0 derivativeDirection = 0 := by
  have bracketDerivative :=
    p286CoordinateLieBracketBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        (hasFDerivAt_const colorCartanQuadraticCoordinate (0 : BasePoint))
        (actualSourceAffineCoordinate_hasFDerivAt 2 0)
  have productDerivative :=
    colorCartanQuadraticCoefficient_hasFDerivAt_origin.smul bracketDerivative
  have functionEquality :
      (fun point =>
        p286GaugeConnectionLinearCurvatureVariation canonicalResponse
          colorCartanQuadraticJet point 1) =
        colorCartanQuadraticCoefficient • fun point =>
          p286CoordinateLieBracketBilinear.toContinuousBilinearMap
            colorCartanQuadraticCoordinate
            (actualSourceAffineCoordinate 2 point) := by
    funext point
    rw [colorCartanQuadraticLinearCurvatureVariation_pair_one]
    change
      colorCartanQuadraticCoefficient point •
          p286CoordinateLieBracket colorCartanQuadraticCoordinate
            (actualSourceAffineCoordinate 2 point) =
        colorCartanQuadraticCoefficient point •
          p286CoordinateLieBracket colorCartanQuadraticCoordinate
            (actualSourceAffineCoordinate 2 point)
    rfl
  rw [functionEquality]
  unfold fieldDirectionalDerivative
  rw [productDerivative.fderiv]
  simp [colorCartanQuadraticCoefficient_origin]

theorem colorCartanQuadraticLinearCurvature_pair_two_derivative_origin
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
            colorCartanQuadraticJet point 2)
        0 derivativeDirection = 0 := by
  have bracketDerivative :=
    p286CoordinateLieBracketBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        (hasFDerivAt_const colorCartanQuadraticCoordinate (0 : BasePoint))
        (actualSourceAffineCoordinate_hasFDerivAt 3 0)
  have productDerivative :=
    colorCartanQuadraticCoefficient_hasFDerivAt_origin.smul bracketDerivative
  have functionEquality :
      (fun point =>
        p286GaugeConnectionLinearCurvatureVariation canonicalResponse
          colorCartanQuadraticJet point 2) =
        colorCartanQuadraticCoefficient • fun point =>
          p286CoordinateLieBracketBilinear.toContinuousBilinearMap
            colorCartanQuadraticCoordinate
            (actualSourceAffineCoordinate 3 point) := by
    funext point
    rw [colorCartanQuadraticLinearCurvatureVariation_pair_two]
    change
      colorCartanQuadraticCoefficient point •
          p286CoordinateLieBracket colorCartanQuadraticCoordinate
            (actualSourceAffineCoordinate 3 point) =
        colorCartanQuadraticCoefficient point •
          p286CoordinateLieBracket colorCartanQuadraticCoordinate
            (actualSourceAffineCoordinate 3 point)
    rfl
  rw [functionEquality]
  unfold fieldDirectionalDerivative
  rw [productDerivative.fderiv]
  simp [colorCartanQuadraticCoefficient_origin]

theorem colorCartanQuadraticLinearCurvature_coordinateTwoProduct_derivative
    (pair : Fin 6) (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          point 2 •
            p286GaugeConnectionLinearCurvatureVariation canonicalResponse
              colorCartanQuadraticJet point pair)
        0 derivativeDirection = 0 := by
  have linearDifferentiable : DifferentiableAt ℝ
      (fun point =>
        p286GaugeConnectionLinearCurvatureVariation canonicalResponse
          colorCartanQuadraticJet point pair) 0 :=
    ((colorCartanQuadraticLinearCurvature_component_contDiff pair).differentiable
      (by simp)).differentiableAt
  have productDerivative :=
    (p286BaseCoordinate 2).hasFDerivAt.smul
      linearDifferentiable.hasFDerivAt
  unfold fieldDirectionalDerivative
  have functionEquality :
      (fun point : BasePoint =>
        point 2 •
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
            colorCartanQuadraticJet point pair) =
        (p286BaseCoordinate 2 : BasePoint → ℝ) •
          fun point =>
            p286GaugeConnectionLinearCurvatureVariation canonicalResponse
              colorCartanQuadraticJet point pair := by
    funext point
    change point 2 •
        p286GaugeConnectionLinearCurvatureVariation canonicalResponse
            colorCartanQuadraticJet point pair =
      p286BaseCoordinate 2 point •
        p286GaugeConnectionLinearCurvatureVariation canonicalResponse
          colorCartanQuadraticJet point pair
    rw [p286BaseCoordinate_apply]
  rw [functionEquality, productDerivative.fderiv]
  simp [p286BaseCoordinate_apply,
    colorCartanQuadraticLinearCurvature_component_origin]

theorem colorCartanQuadraticLinearFramedOne_direction_two_eq_zero :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
              colorCartanQuadraticJet point 1 +
            point 2 •
              p286GaugeConnectionLinearCurvatureVariation canonicalResponse
                colorCartanQuadraticJet point 5)
        0 2 = 0 := by
  let firstField : BasePoint → P286CoordinateCarrier := fun point =>
    p286GaugeConnectionLinearCurvatureVariation canonicalResponse
      colorCartanQuadraticJet point 1
  let productField : BasePoint → P286CoordinateCarrier := fun point =>
    point 2 •
      p286GaugeConnectionLinearCurvatureVariation canonicalResponse
        colorCartanQuadraticJet point 5
  have firstSmooth : ContDiff ℝ ∞ firstField :=
    colorCartanQuadraticLinearCurvature_component_contDiff 1
  have productSmooth : ContDiff ℝ ∞ productField := by
    have raw := (p286BaseCoordinate 2).contDiff.smul
      (colorCartanQuadraticLinearCurvature_component_contDiff 5)
    have functionEquality :
        productField =
          (p286BaseCoordinate 2 : BasePoint → ℝ) • fun point =>
            p286GaugeConnectionLinearCurvatureVariation canonicalResponse
              colorCartanQuadraticJet point 5 := by
      funext point
      change point 2 •
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
              colorCartanQuadraticJet point 5 =
        p286BaseCoordinate 2 point •
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
            colorCartanQuadraticJet point 5
      rw [p286BaseCoordinate_apply]
    rw [functionEquality]
    exact raw
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add
    (firstSmooth.differentiable (by simp) 0)
    (productSmooth.differentiable (by simp) 0)]
  change
    fieldDirectionalDerivative firstField 0 2 +
      fieldDirectionalDerivative productField 0 2 = 0
  rw [show fieldDirectionalDerivative firstField 0 2 = 0 by
      exact colorCartanQuadraticLinearCurvature_pair_one_derivative_origin 2,
    show fieldDirectionalDerivative productField 0 2 = 0 by
      exact
        colorCartanQuadraticLinearCurvature_coordinateTwoProduct_derivative
          5 2]
  simp

theorem colorCartanQuadraticLinearFramedTwo_direction_three_eq_zero :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
              colorCartanQuadraticJet point 2 -
            point 2 •
              p286GaugeConnectionLinearCurvatureVariation canonicalResponse
                colorCartanQuadraticJet point 4)
        0 3 = 0 := by
  let firstField : BasePoint → P286CoordinateCarrier := fun point =>
    p286GaugeConnectionLinearCurvatureVariation canonicalResponse
      colorCartanQuadraticJet point 2
  let productField : BasePoint → P286CoordinateCarrier := fun point =>
    point 2 •
      p286GaugeConnectionLinearCurvatureVariation canonicalResponse
        colorCartanQuadraticJet point 4
  have firstSmooth : ContDiff ℝ ∞ firstField :=
    colorCartanQuadraticLinearCurvature_component_contDiff 2
  have productSmooth : ContDiff ℝ ∞ productField := by
    have raw := (p286BaseCoordinate 2).contDiff.smul
      (colorCartanQuadraticLinearCurvature_component_contDiff 4)
    have functionEquality :
        productField =
          (p286BaseCoordinate 2 : BasePoint → ℝ) • fun point =>
            p286GaugeConnectionLinearCurvatureVariation canonicalResponse
              colorCartanQuadraticJet point 4 := by
      funext point
      change point 2 •
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
              colorCartanQuadraticJet point 4 =
        p286BaseCoordinate 2 point •
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
            colorCartanQuadraticJet point 4
      rw [p286BaseCoordinate_apply]
    rw [functionEquality]
    exact raw
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_sub
    (firstSmooth.differentiable (by simp) 0)
    (productSmooth.differentiable (by simp) 0)]
  change
    fieldDirectionalDerivative firstField 0 3 -
      fieldDirectionalDerivative productField 0 3 = 0
  rw [show fieldDirectionalDerivative firstField 0 3 = 0 by
      exact colorCartanQuadraticLinearCurvature_pair_two_derivative_origin 3,
    show fieldDirectionalDerivative productField 0 3 = 0 by
      exact
        colorCartanQuadraticLinearCurvature_coordinateTwoProduct_derivative
          4 3]
  simp

theorem coordinateTwo_smul_contDiff
    (field : BasePoint → P286CoordinateCarrier)
    (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ fun point : BasePoint => point 2 • field point := by
  have raw := (p286BaseCoordinate 2).contDiff.smul smooth
  have functionEquality :
      (fun point : BasePoint => point 2 • field point) =
        (p286BaseCoordinate 2 : BasePoint → ℝ) • field := by
    funext point
    change point 2 • field point =
      p286BaseCoordinate 2 point • field point
    rw [p286BaseCoordinate_apply]
  rw [functionEquality]
  exact raw

theorem colorCartanQuadraticResponseFramedOne_direction_two_eq_zero
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          colorCartanQuadraticResponseCurvatureCoordinate parameter point 1 +
            point 2 •
              colorCartanQuadraticResponseCurvatureCoordinate
                parameter point 5)
        0 2 = 0 := by
  let backgroundField : BasePoint → P286CoordinateCarrier := fun point =>
    holonomicP286GaugeCurvatureCoordinate canonicalResponse point 1 +
      point 2 •
        holonomicP286GaugeCurvatureCoordinate canonicalResponse point 5
  let linearField : BasePoint → P286CoordinateCarrier := fun point =>
    p286GaugeConnectionLinearCurvatureVariation canonicalResponse
        colorCartanQuadraticJet point 1 +
      point 2 •
        p286GaugeConnectionLinearCurvatureVariation canonicalResponse
          colorCartanQuadraticJet point 5
  have backgroundOneSmooth : ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeCurvatureCoordinate canonicalResponse point 1 :=
    holonomicGaugeCurvature_coordinate_contDiff canonicalResponse
      canonicalResponse_smooth_local 1
  have backgroundFiveSmooth : ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeCurvatureCoordinate canonicalResponse point 5 :=
    holonomicGaugeCurvature_coordinate_contDiff canonicalResponse
      canonicalResponse_smooth_local 5
  have backgroundSmooth : ContDiff ℝ ∞ backgroundField :=
    backgroundOneSmooth.add
      (coordinateTwo_smul_contDiff _ backgroundFiveSmooth)
  have linearSmooth : ContDiff ℝ ∞ linearField :=
    (colorCartanQuadraticLinearCurvature_component_contDiff 1).add
      (coordinateTwo_smul_contDiff _
        (colorCartanQuadraticLinearCurvature_component_contDiff 5))
  have functionEquality :
      (fun point : BasePoint =>
        colorCartanQuadraticResponseCurvatureCoordinate parameter point 1 +
          point 2 •
            colorCartanQuadraticResponseCurvatureCoordinate
              parameter point 5) =
        backgroundField + parameter • linearField := by
    funext point
    have expansion :=
      colorCartanQuadraticResponseCurvatureCoordinate_expansion parameter point
    have pairOne := congrFun expansion 1
    have pairFive := congrFun expansion 5
    dsimp only [backgroundField, linearField]
    rw [pairOne, pairFive]
    simp only [Pi.add_apply, Pi.smul_apply]
    module
  have backgroundDerivative :
      HasFDerivAt backgroundField (fderiv ℝ backgroundField 0) 0 :=
    ((backgroundSmooth.differentiable (by simp)).differentiableAt).hasFDerivAt
  have linearDerivative :
      HasFDerivAt linearField (fderiv ℝ linearField 0) 0 :=
    ((linearSmooth.differentiable (by simp)).differentiableAt).hasFDerivAt
  have sumDerivative :=
    backgroundDerivative.add (linearDerivative.const_smul parameter)
  rw [functionEquality]
  unfold fieldDirectionalDerivative
  rw [sumDerivative.fderiv]
  simp only [add_apply, smul_apply]
  change fieldDirectionalDerivative backgroundField 0 2 +
      parameter • fieldDirectionalDerivative linearField 0 2 = 0
  rw [show fieldDirectionalDerivative backgroundField 0 2 = 0 by
      change fieldDirectionalDerivative
        (fun point : BasePoint =>
          actualNativeCurvatureCoordinate point 1 +
            point 2 • actualNativeCurvatureCoordinate point 5) 0 2 = 0
      exact actualFramedCurvatureOne_direction_two_eq_zero,
    show fieldDirectionalDerivative linearField 0 2 = 0 by
      exact colorCartanQuadraticLinearFramedOne_direction_two_eq_zero]
  simp

theorem colorCartanQuadraticResponseFramedTwo_direction_three_eq_zero
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          colorCartanQuadraticResponseCurvatureCoordinate parameter point 2 -
            point 2 •
              colorCartanQuadraticResponseCurvatureCoordinate
                parameter point 4)
        0 3 = 0 := by
  let backgroundField : BasePoint → P286CoordinateCarrier := fun point =>
    holonomicP286GaugeCurvatureCoordinate canonicalResponse point 2 -
      point 2 •
        holonomicP286GaugeCurvatureCoordinate canonicalResponse point 4
  let linearField : BasePoint → P286CoordinateCarrier := fun point =>
    p286GaugeConnectionLinearCurvatureVariation canonicalResponse
        colorCartanQuadraticJet point 2 -
      point 2 •
        p286GaugeConnectionLinearCurvatureVariation canonicalResponse
          colorCartanQuadraticJet point 4
  have backgroundTwoSmooth : ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeCurvatureCoordinate canonicalResponse point 2 :=
    holonomicGaugeCurvature_coordinate_contDiff canonicalResponse
      canonicalResponse_smooth_local 2
  have backgroundFourSmooth : ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeCurvatureCoordinate canonicalResponse point 4 :=
    holonomicGaugeCurvature_coordinate_contDiff canonicalResponse
      canonicalResponse_smooth_local 4
  have backgroundSmooth : ContDiff ℝ ∞ backgroundField :=
    backgroundTwoSmooth.sub
      (coordinateTwo_smul_contDiff _ backgroundFourSmooth)
  have linearSmooth : ContDiff ℝ ∞ linearField :=
    (colorCartanQuadraticLinearCurvature_component_contDiff 2).sub
      (coordinateTwo_smul_contDiff _
        (colorCartanQuadraticLinearCurvature_component_contDiff 4))
  have functionEquality :
      (fun point : BasePoint =>
        colorCartanQuadraticResponseCurvatureCoordinate parameter point 2 -
          point 2 •
            colorCartanQuadraticResponseCurvatureCoordinate
              parameter point 4) =
        backgroundField + parameter • linearField := by
    funext point
    have expansion :=
      colorCartanQuadraticResponseCurvatureCoordinate_expansion parameter point
    have pairTwo := congrFun expansion 2
    have pairFour := congrFun expansion 4
    dsimp only [backgroundField, linearField]
    rw [pairTwo, pairFour]
    simp only [Pi.add_apply, Pi.smul_apply]
    module
  have backgroundDerivative :
      HasFDerivAt backgroundField (fderiv ℝ backgroundField 0) 0 :=
    ((backgroundSmooth.differentiable (by simp)).differentiableAt).hasFDerivAt
  have linearDerivative :
      HasFDerivAt linearField (fderiv ℝ linearField 0) 0 :=
    ((linearSmooth.differentiable (by simp)).differentiableAt).hasFDerivAt
  have sumDerivative :=
    backgroundDerivative.add (linearDerivative.const_smul parameter)
  rw [functionEquality]
  unfold fieldDirectionalDerivative
  rw [sumDerivative.fderiv]
  simp only [add_apply, smul_apply]
  change fieldDirectionalDerivative backgroundField 0 3 +
      parameter • fieldDirectionalDerivative linearField 0 3 = 0
  rw [show fieldDirectionalDerivative backgroundField 0 3 = 0 by
      change fieldDirectionalDerivative
        (fun point : BasePoint =>
          actualNativeCurvatureCoordinate point 2 -
            point 2 • actualNativeCurvatureCoordinate point 4) 0 3 = 0
      exact actualFramedCurvatureTwo_direction_three_eq_zero,
    show fieldDirectionalDerivative linearField 0 3 = 0 by
      exact colorCartanQuadraticLinearFramedTwo_direction_three_eq_zero]
  simp

theorem colorCartanQuadraticMomentum_direction_two_derivative_eq_zero
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 2 colorCartanMuZeroDirection))
        0 2 = 0 := by
  let framedField : BasePoint → P286CoordinateCarrier := fun point =>
    colorCartanQuadraticResponseCurvatureCoordinate parameter point 1 +
      point 2 •
        colorCartanQuadraticResponseCurvatureCoordinate parameter point 5
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (framedField point)
      colorCartanQuadraticCoordinate
  have curvatureOneSmooth : ContDiff ℝ ∞ fun point =>
      colorCartanQuadraticResponseCurvatureCoordinate parameter point 1 :=
    holonomicGaugeCurvature_coordinate_contDiff
      (colorCartanQuadraticConstitutiveResponse parameter)
      (colorCartanQuadraticConstitutiveResponse_smooth parameter) 1
  have curvatureFiveSmooth : ContDiff ℝ ∞ fun point =>
      colorCartanQuadraticResponseCurvatureCoordinate parameter point 5 :=
    holonomicGaugeCurvature_coordinate_contDiff
      (colorCartanQuadraticConstitutiveResponse parameter)
      (colorCartanQuadraticConstitutiveResponse_smooth parameter) 5
  have framedSmooth : ContDiff ℝ ∞ framedField :=
    curvatureOneSmooth.add
      (coordinateTwo_smul_contDiff _ curvatureFiveSmooth)
  have framedDifferentiable : DifferentiableAt ℝ framedField 0 :=
    ((framedSmooth.differentiable (by simp)).differentiableAt)
  have pairingHasDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        framedDifferentiable.hasFDerivAt
        (hasFDerivAt_const colorCartanQuadraticCoordinate 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 :=
    pairingHasDerivative.differentiableAt
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 2 colorCartanMuZeroDirection) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact colorCartanQuadraticMomentum_direction_two parameter point
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 2 = 0
  rw [fieldDirectionalDerivative_pairing_const_local framedField
    (fderiv ℝ framedField 0) 0 2 colorCartanQuadraticCoordinate
    framedDifferentiable.hasFDerivAt]
  rw [show fieldDirectionalDerivative framedField 0 2 = 0 by
      exact colorCartanQuadraticResponseFramedOne_direction_two_eq_zero
        parameter]
  simp

theorem colorCartanQuadraticMomentum_direction_three_derivative_eq_zero
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 3 colorCartanMuZeroDirection))
        0 3 = 0 := by
  let framedField : BasePoint → P286CoordinateCarrier := fun point =>
    colorCartanQuadraticResponseCurvatureCoordinate parameter point 2 -
      point 2 •
        colorCartanQuadraticResponseCurvatureCoordinate parameter point 4
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (framedField point)
      colorCartanQuadraticCoordinate
  have curvatureTwoSmooth : ContDiff ℝ ∞ fun point =>
      colorCartanQuadraticResponseCurvatureCoordinate parameter point 2 :=
    holonomicGaugeCurvature_coordinate_contDiff
      (colorCartanQuadraticConstitutiveResponse parameter)
      (colorCartanQuadraticConstitutiveResponse_smooth parameter) 2
  have curvatureFourSmooth : ContDiff ℝ ∞ fun point =>
      colorCartanQuadraticResponseCurvatureCoordinate parameter point 4 :=
    holonomicGaugeCurvature_coordinate_contDiff
      (colorCartanQuadraticConstitutiveResponse parameter)
      (colorCartanQuadraticConstitutiveResponse_smooth parameter) 4
  have framedSmooth : ContDiff ℝ ∞ framedField :=
    curvatureTwoSmooth.sub
      (coordinateTwo_smul_contDiff _ curvatureFourSmooth)
  have framedDifferentiable : DifferentiableAt ℝ framedField 0 :=
    ((framedSmooth.differentiable (by simp)).differentiableAt)
  have pairingHasDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        framedDifferentiable.hasFDerivAt
        (hasFDerivAt_const colorCartanQuadraticCoordinate 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 :=
    pairingHasDerivative.differentiableAt
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum
          (colorCartanQuadraticConstitutiveResponse parameter)
          (p286GaugeExteriorDerivativeDirection 3 colorCartanMuZeroDirection) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact colorCartanQuadraticMomentum_direction_three parameter point
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 3 = 0
  rw [fieldDirectionalDerivative_pairing_const_local framedField
    (fderiv ℝ framedField 0) 0 3 colorCartanQuadraticCoordinate
    framedDifferentiable.hasFDerivAt]
  rw [show fieldDirectionalDerivative framedField 0 3 = 0 by
      exact colorCartanQuadraticResponseFramedTwo_direction_three_eq_zero
        parameter]
  simp

theorem colorCartanQuadraticConstitutiveResponse_divergence
    (parameter : ℝ) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        (colorCartanQuadraticConstitutiveResponse parameter)
        colorCartanMuZeroDirection 0 = -1 - 8 * parameter := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  rw [Fin.sum_univ_four,
    colorCartanQuadraticMomentum_direction_zero_derivative_eq_zero,
    colorCartanQuadraticMomentum_direction_one_derivative,
    colorCartanQuadraticMomentum_direction_two_derivative_eq_zero,
    colorCartanQuadraticMomentum_direction_three_derivative_eq_zero]
  ring

/-! ## Residual zero fiber; the coefficient is read from the residual -/

def colorCartanQuadraticEulerLagrangeResidual (parameter : ℝ) : ℝ :=
  p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
    (colorCartanQuadraticConstitutiveResponse parameter)
    colorCartanMuZeroDirection 0

theorem colorCartanQuadraticEulerLagrangeResidual_formula
    (parameter : ℝ) :
    colorCartanQuadraticEulerLagrangeResidual parameter =
      1 + 8 * parameter := by
  unfold colorCartanQuadraticEulerLagrangeResidual
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance]
  unfold p286GaugeBFBalanceCoefficient
  rw [colorCartanQuadraticConstitutiveResponse_p286BFAlgebraic_eq_zero,
    colorCartanQuadraticConstitutiveResponse_divergence,
    colorCartanQuadraticConstitutiveResponse_p286ScalarCurrent_eq_zero,
    colorCartanQuadraticConstitutiveResponse_p286MatterCurrent_eq_zero]
  ring

/-- The transport slope is computed from two residual readouts; it is not a
source coupling or caller-supplied normalization. -/
def colorCartanQuadraticResidualSlope : ℝ :=
  colorCartanQuadraticEulerLagrangeResidual 1 -
    colorCartanQuadraticEulerLagrangeResidual 0

theorem colorCartanQuadraticResidualSlope_eq_eight :
    colorCartanQuadraticResidualSlope = 8 := by
  unfold colorCartanQuadraticResidualSlope
  rw [colorCartanQuadraticEulerLagrangeResidual_formula,
    colorCartanQuadraticEulerLagrangeResidual_formula]
  norm_num

/-- Canonical zero-fiber coordinate obtained only from the observed residual
and its proved nonzero slope. -/
def colorCartanQuadraticResidualDerivedCoefficient : ℝ :=
  -colorCartanQuadraticEulerLagrangeResidual 0 /
    colorCartanQuadraticResidualSlope

theorem colorCartanQuadraticResidualDerivedCoefficient_eq_neg_eighth :
    colorCartanQuadraticResidualDerivedCoefficient = -(1 / 8 : ℝ) := by
  unfold colorCartanQuadraticResidualDerivedCoefficient
  rw [colorCartanQuadraticEulerLagrangeResidual_formula,
    colorCartanQuadraticResidualSlope_eq_eight]
  norm_num

theorem colorCartanQuadraticResidualDerivedCoefficient_solves :
    colorCartanQuadraticEulerLagrangeResidual
        colorCartanQuadraticResidualDerivedCoefficient = 0 := by
  rw [colorCartanQuadraticEulerLagrangeResidual_formula,
    colorCartanQuadraticResidualDerivedCoefficient_eq_neg_eighth]
  norm_num

theorem colorCartanQuadraticEulerLagrangeResidual_zeroFiber
    (parameter : ℝ) :
    colorCartanQuadraticEulerLagrangeResidual parameter = 0 ↔
      parameter = colorCartanQuadraticResidualDerivedCoefficient := by
  rw [colorCartanQuadraticEulerLagrangeResidual_formula,
    colorCartanQuadraticResidualDerivedCoefficient_eq_neg_eighth]
  constructor
  · intro residualZero
    linarith
  · intro parameterEquality
    rw [parameterEquality]
    norm_num

/-- Deterministic existing-field repair selected by the proved residual
zero fiber.  The coefficient is not accepted from a caller or stored in the
source. -/
def colorCartanQuadraticResidualRepair : StageNineHolonomicConfiguration :=
  colorCartanQuadraticConstitutiveResponse
    colorCartanQuadraticResidualDerivedCoefficient

theorem colorCartanQuadraticResidualRepair_smooth :
    colorCartanQuadraticResidualRepair.Smooth :=
  colorCartanQuadraticConstitutiveResponse_smooth _

theorem colorCartanQuadraticResidualRepair_nondegenerate :
    colorCartanQuadraticResidualRepair.Nondegenerate :=
  colorCartanQuadraticConstitutiveResponse_nondegenerate _

theorem colorCartanQuadraticResidualRepair_auxiliaryEquation
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryEquationResidual positiveSmoothUnifiedSource
        colorCartanQuadraticResidualRepair point = 0 :=
  colorCartanQuadraticConstitutiveResponse_auxiliaryEquation _ point

theorem colorCartanQuadraticResidualRepair_colorCartanMuZero_EL_eq_zero :
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        colorCartanQuadraticResidualRepair colorCartanMuZeroDirection 0 = 0 :=
  colorCartanQuadraticResidualDerivedCoefficient_solves

theorem colorCartanQuadraticResidualRepair_coefficient_unique
    (parameter : ℝ)
    (residualZero :
      p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
          (colorCartanQuadraticConstitutiveResponse parameter)
          colorCartanMuZeroDirection 0 = 0) :
    parameter = colorCartanQuadraticResidualDerivedCoefficient :=
  (colorCartanQuadraticEulerLagrangeResidual_zeroFiber parameter).mp
    residualZero

end

end SaturationMonoid.PhysicsCore.StageNineP286ColorCartanConstitutiveResponse
