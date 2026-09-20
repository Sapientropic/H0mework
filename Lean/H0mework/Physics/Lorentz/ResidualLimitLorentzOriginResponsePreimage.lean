import H0mework.Physics.Lorentz.ResidualLimitSameCurvatureLorentzTransport

/-!
# S9-C3h31: Lorentz origin-response preimage

C3h30 rejected only the scalar-origin section of the existing normalized
affine same-curvature connection fiber.  This module audits the complete
lowered Lorentz origin coordinate instead.  An arbitrary coordinate
`q : LorentzBivectorOneForm` is lifted by the already-existing Lorentz-skew
map and the already-existing normalized-affine right inverse.  The curvature,
coframe, gravity auxiliary, gauge fields, scalar, and completion fields are
not changed.

The actual algebraic gravity--BF response is computed on all 24 basis
directions.  The already-proved differential response

`D(direction) = direction 0 5`

has the explicit sparse origin preimage

`q_D(0,5) = -1/2`, `q_D(1,1) = 1/2`, `q_D(2,0) = -1/2`.

Lean proves a two-sided inverse for the complete 24-coordinate operator and
the complete function equality `A(q_D)=D`, not merely one matching
coordinate.  Thus `q_D` is the unique origin coordinate with that response.
Since the differential channel is frozen over this fiber, the reader at
`q_D` has zero gravity--BF balance at the origin while retaining the strong
algebraic shell and the same actual curvature.

This is an inhabitance result for one existing field carrier.  The arbitrary
`q` is an audit coordinate, not source data or a physical knob, and this
module does not yet prove that exact lineage generates this coordinate, that
it is the required one-step transported endpoint, or that the complete joint
shell is stationary.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzOriginResponsePreimage

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellZeroFiber
open StageNineLorentzConnectionActionVariation
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineConnectionSectorSourceBalance
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitSameCurvatureLorentzTransport

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Complete existing same-curvature origin fiber -/

/-- Lift an arbitrary lowered Lorentz origin coordinate through the existing
normalized-affine right inverse at the already-derived residual-limit
curvature. -/
def residualLimitArbitraryOriginConnectionField
    (q : LorentzBivectorOneForm) : LorentzConnectionField :=
  normalizedAffineLorentzConnectionField
    (lorentzSkewConnectionOfBivectorOneForm q)
    positiveSourceGravityMouthResidualLimitCurvature

/-- Retain every field of the C3h27 reader except for the audited origin
connection coordinate. -/
def residualLimitArbitraryOriginReader
    (q : LorentzBivectorOneForm) : StageNineHolonomicConfiguration :=
  { residualLimitLorentzCarrierReader with
    gravityConnection := residualLimitArbitraryOriginConnectionField q }

@[simp] theorem residualLimitArbitraryOriginReader_coframe
    (q : LorentzBivectorOneForm) :
    (residualLimitArbitraryOriginReader q).coframe =
      residualLimitLorentzCarrierReader.coframe :=
  rfl

@[simp] theorem residualLimitArbitraryOriginReader_gravityAuxiliary
    (q : LorentzBivectorOneForm) :
    (residualLimitArbitraryOriginReader q).gravityAuxiliary =
      residualLimitLorentzCarrierReader.gravityAuxiliary :=
  rfl

@[simp] theorem residualLimitArbitraryOriginConnectionField_origin
    (q : LorentzBivectorOneForm) :
    residualLimitArbitraryOriginConnectionField q 0 =
      lorentzSkewConnectionOfBivectorOneForm q :=
  normalizedAffineLorentzConnectionField_zero _ _

@[simp] theorem residualLimitArbitraryOriginReader_gravityConnection_origin
    (q : LorentzBivectorOneForm) :
    (residualLimitArbitraryOriginReader q).gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm q :=
  residualLimitArbitraryOriginConnectionField_origin q

/-- Curvature is recomputed from the generated field and remains the actual
residual-limit curvature for every audited origin coordinate. -/
theorem residualLimitArbitraryOriginReader_curvature_origin
    (q : LorentzBivectorOneForm) :
    holonomicGravityCurvature (residualLimitArbitraryOriginReader q) 0 =
      positiveSourceGravityMouthResidualLimitCurvature := by
  change holonomicGravityCurvature
      (normalizedAffineConfiguration
        (lorentzSkewConnectionOfBivectorOneForm q)
        positiveSourceGravityMouthResidualLimitCurvature) 0 =
    positiveSourceGravityMouthResidualLimitCurvature
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

/-! ## The existing strong algebraic shell is retained -/

theorem residualLimitArbitraryOriginReader_gravitySimplicity_zero
    (q : LorentzBivectorOneForm) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitArbitraryOriginReader q) 0).gravitySimplicity = 0 := by
  change generatedGravitySimplicityResidual
      (toContinuumPointField (residualLimitArbitraryOriginReader q) 0) = 0
  exact (gravitySimplicityResidual_eq_zero_iff
    (residualLimitArbitraryOriginReader q) 0).mpr (by rfl)

theorem residualLimitArbitraryOriginReader_gravityAuxiliary_zero
    (q : LorentzBivectorOneForm) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitArbitraryOriginReader q) 0).gravityAuxiliary = 0 := by
  change holonomicGravityAuxiliaryEquationResidual
      (residualLimitArbitraryOriginReader q) 0 = 0
  apply (gravityAuxiliaryResidual_eq_zero_iff
    (residualLimitArbitraryOriginReader q) 0).mpr
  rw [residualLimitArbitraryOriginReader_curvature_origin]
  change positiveSourceGravityMouthResidualLimitCurvature =
    gravityInternalDualEquiv
      (residualLimitLorentzCarrierReader.gravityAuxiliary 0)
  calc
    positiveSourceGravityMouthResidualLimitCurvature =
        holonomicGravityCurvature residualLimitLorentzCarrierReader 0 :=
      (residualLimitExtension_gravityCurvature_origin
        residualLimitLorentzCarrierReader
        residualLimitLorentzCarrierReader_extends).symm
    _ = gravityInternalDualEquiv
        (residualLimitLorentzCarrierReader.gravityAuxiliary 0) :=
      (gravityAuxiliaryResidual_eq_zero_iff
        residualLimitLorentzCarrierReader 0).mp
          (residualLimitExtension_gravityAuxiliaryResidual_origin
            residualLimitLorentzCarrierReader
            residualLimitLorentzCarrierReader_extends)

theorem residualLimitArbitraryOriginReader_p286GaugeAuxiliary_zero
    (q : LorentzBivectorOneForm) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitArbitraryOriginReader q) 0).p286GaugeAuxiliary = 0 := by
  change
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      residualLimitLorentzCarrierReader 0).p286GaugeAuxiliary = 0
  exact residualLimitExtension_p286GaugeAuxiliaryResidual_origin
    residualLimitLorentzCarrierReader residualLimitLorentzCarrierReader_extends

/-- All three strong pointwise algebraic coordinates remain zero throughout
the complete existing origin fiber. -/
theorem residualLimitArbitraryOriginReader_algebraicResidual_zero
    (q : LorentzBivectorOneForm) :
    currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitArbitraryOriginReader q) 0 = 0 := by
  apply CurrentPointwiseAlgebraicResidualCarrier.ext
  · exact residualLimitArbitraryOriginReader_gravitySimplicity_zero q
  · exact residualLimitArbitraryOriginReader_gravityAuxiliary_zero q
  · exact residualLimitArbitraryOriginReader_p286GaugeAuxiliary_zero q

/-! ## Actual response operator and exhaustive finite normal form -/

/-- Complete algebraic gravity--BF response at the origin. -/
def residualLimitOriginAlgebraicResponse
    (q : LorentzBivectorOneForm) : RestrictedLorentzResponse :=
  fun direction =>
    lorentzGravityBFAlgebraicCoefficient
      (residualLimitArbitraryOriginReader q) direction 0

/-- Complete differential response in the same existing field fiber. -/
def residualLimitOriginDivergenceResponse
    (q : LorentzBivectorOneForm) : RestrictedLorentzResponse :=
  fun direction =>
    lorentzConnectionBFDifferentialMomentumDivergence
      (residualLimitArbitraryOriginReader q) direction 0

/-- The differential response reads only the retained coframe and gravity
auxiliary, so it is frozen over the whole origin fiber. -/
theorem residualLimitOriginDivergenceResponse_eq_reference
    (q : LorentzBivectorOneForm) :
    residualLimitOriginDivergenceResponse q =
      residualLimitReferenceDivergenceResponse := by
  funext direction
  have momentumEq (derivativeDirection : LorentzianIndex) :
      lorentzConnectionBFDifferentialMomentum
          (residualLimitArbitraryOriginReader q)
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction) =
        lorentzConnectionBFDifferentialMomentum
          residualLimitLorentzCarrierReader
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction) := by
    funext point
    unfold lorentzConnectionBFDifferentialMomentum generatedVolumeDensity
      toContinuumPointField
    rfl
  unfold residualLimitOriginDivergenceResponse
    residualLimitReferenceDivergenceResponse
    lorentzConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [momentumEq derivativeDirection]

/-- The explicit 24 output coordinates of the actual algebraic response.
Rows and columns use `(formDirection, internalPair)` in the repository's
`(01,02,03,23,31,12)` pair order. -/
def residualLimitOriginAlgebraicResponseCoordinates
    (q : LorentzBivectorOneForm) : LorentzBivectorOneForm :=
  ![
    ![
      q 2 5 - q 3 4,
      -q 1 5 + q 3 3,
      q 1 4 - q 2 3,
      q 2 2 - q 3 1,
      -q 1 2 + q 3 0,
      q 1 1 - q 2 0],
    ![
      q 2 1 + q 3 2,
      q 0 5 - q 2 0,
      -q 0 4 - q 3 0,
      -q 2 4 - q 3 5,
      q 0 2 + q 2 3,
      -q 0 1 + q 3 3],
    ![
      -q 0 5 - q 1 1,
      q 1 0 + q 3 2,
      q 0 3 - q 3 1,
      -q 0 2 + q 1 4,
      -q 1 3 - q 3 5,
      q 0 0 + q 3 4],
    ![
      q 0 4 - q 1 2,
      -q 0 3 - q 2 2,
      q 1 0 + q 2 1,
      q 0 1 + q 1 5,
      -q 0 0 + q 2 5,
      -q 1 3 - q 2 4]
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- The displayed matrix is the actual response on every one of the 24 basis
directions, not an independently postulated linear operator. -/
theorem residualLimitOriginAlgebraicResponse_basis
    (q : LorentzBivectorOneForm)
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    residualLimitOriginAlgebraicResponse q
        (residualLimitLorentzBasisDirection formDirection internalPair) =
      residualLimitOriginAlgebraicResponseCoordinates q
        formDirection internalPair := by
  unfold residualLimitOriginAlgebraicResponse
    lorentzGravityBFAlgebraicCoefficient
  simp only [toContinuumPointField,
    residualLimitArbitraryOriginReader_coframe,
    residualLimitArbitraryOriginReader_gravityAuxiliary,
    residualLimitLorentzCarrierReader_coframe,
    residualLimitLorentzCarrierReader_gravityAuxiliary,
    ProofFreeRicherAnholonomicSource.Source.coframeAt_zero]
  simp only [generatedVolumeDensity, Matrix.det_one, abs_one, one_mul]
  unfold gravityBFCurvatureIncrementDensity
  rw [← gravityAuxiliaryHodgePairingPolynomial_eq
    (1 : LorentzianCoframe) (by simp)]
  unfold gravityAuxiliaryHodgePairingPolynomial
    lorentzConnectionAlgebraicCurvatureDirection
    lorentzConnectionAlgebraicCurvatureVariation
  rw [residualLimitArbitraryOriginReader_gravityConnection_origin]
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [physicalIIPlusBivector, internalBivectorDual, coframeWedge,
      coframeTwoFormLinear, residualLimitLorentzBasisDirection,
      residualLimitOriginAlgebraicResponseCoordinates,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond,
      Matrix.one_apply, Fin.sum_univ_six, Fin.sum_univ_four] <;> ring

/-! ## Explicit inverse of the complete response-coordinate operator -/

/-- Coordinate-level inverse of the displayed response matrix.  Every input
coordinate is a three-term half-integral combination of response
coordinates. -/
def residualLimitOriginAlgebraicResponsePreimage
    (a : LorentzBivectorOneForm) : LorentzBivectorOneForm :=
  ![
    ![
      (a 0 0 + a 2 5 - a 3 4) / 2,
      (a 0 1 - a 1 5 + a 3 3) / 2,
      (a 0 2 + a 1 4 - a 2 3) / 2,
      (-a 0 3 + a 2 2 - a 3 1) / 2,
      (-a 0 4 - a 1 2 + a 3 0) / 2,
      (-a 0 5 + a 1 1 - a 2 0) / 2],
    ![
      (-a 1 0 + a 2 1 + a 3 2) / 2,
      (a 0 5 - a 1 1 - a 2 0) / 2,
      (-a 0 4 - a 1 2 - a 3 0) / 2,
      (a 1 3 - a 2 4 - a 3 5) / 2,
      (a 0 2 + a 1 4 + a 2 3) / 2,
      (-a 0 1 + a 1 5 + a 3 3) / 2],
    ![
      (-a 0 5 - a 1 1 - a 2 0) / 2,
      (a 1 0 - a 2 1 + a 3 2) / 2,
      (a 0 3 - a 2 2 - a 3 1) / 2,
      (-a 0 2 + a 1 4 + a 2 3) / 2,
      (-a 1 3 + a 2 4 - a 3 5) / 2,
      (a 0 0 + a 2 5 + a 3 4) / 2],
    ![
      (a 0 4 - a 1 2 - a 3 0) / 2,
      (-a 0 3 - a 2 2 - a 3 1) / 2,
      (a 1 0 + a 2 1 - a 3 2) / 2,
      (a 0 1 + a 1 5 + a 3 3) / 2,
      (-a 0 0 + a 2 5 + a 3 4) / 2,
      (-a 1 3 - a 2 4 + a 3 5) / 2]
  ]

theorem residualLimitOriginAlgebraicResponsePreimage_leftInverse
    (q : LorentzBivectorOneForm) :
    residualLimitOriginAlgebraicResponsePreimage
        (residualLimitOriginAlgebraicResponseCoordinates q) = q := by
  funext formDirection internalPair
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [residualLimitOriginAlgebraicResponsePreimage,
      residualLimitOriginAlgebraicResponseCoordinates] <;> ring

theorem residualLimitOriginAlgebraicResponsePreimage_rightInverse
    (a : LorentzBivectorOneForm) :
    residualLimitOriginAlgebraicResponseCoordinates
        (residualLimitOriginAlgebraicResponsePreimage a) = a := by
  funext formDirection internalPair
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [residualLimitOriginAlgebraicResponsePreimage,
      residualLimitOriginAlgebraicResponseCoordinates] <;> ring

/-- The actual finite coordinate operator is bijective.  This classifies the
audit fiber; it does not generate a source branch. -/
theorem residualLimitOriginAlgebraicResponseCoordinates_bijective :
    Function.Bijective residualLimitOriginAlgebraicResponseCoordinates := by
  constructor
  · intro first second equality
    have lifted := congrArg residualLimitOriginAlgebraicResponsePreimage equality
    rw [residualLimitOriginAlgebraicResponsePreimage_leftInverse,
      residualLimitOriginAlgebraicResponsePreimage_leftInverse] at lifted
    exact lifted
  · intro a
    exact ⟨residualLimitOriginAlgebraicResponsePreimage a,
      residualLimitOriginAlgebraicResponsePreimage_rightInverse a⟩

/-! ## Sparse response preimage and Lorentz zero fiber -/

/-- Sparse lowered origin coordinate forced by the actual finite response
normal form for `D(direction)=direction 0 5`. -/
def residualLimitReferenceDivergenceOriginPreimage :
    LorentzBivectorOneForm :=
  ![
    ![0, 0, 0, 0, 0, -(1 / 2 : ℝ)],
    ![0, (1 / 2 : ℝ), 0, 0, 0, 0],
    ![-(1 / 2 : ℝ), 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Function-level hard gate: the sparse lowered coordinate produces the
complete differential response, not merely one matching basis value. -/
theorem residualLimitReferenceDivergenceOriginPreimage_response :
    residualLimitOriginAlgebraicResponse
        residualLimitReferenceDivergenceOriginPreimage =
      residualLimitReferenceDivergenceResponse := by
  funext direction
  rw [residualLimitReferenceDivergenceResponse_apply]
  unfold residualLimitOriginAlgebraicResponse
    lorentzGravityBFAlgebraicCoefficient
  simp only [toContinuumPointField,
    residualLimitArbitraryOriginReader_coframe,
    residualLimitArbitraryOriginReader_gravityAuxiliary,
    residualLimitLorentzCarrierReader_coframe,
    residualLimitLorentzCarrierReader_gravityAuxiliary,
    ProofFreeRicherAnholonomicSource.Source.coframeAt_zero]
  simp only [generatedVolumeDensity, Matrix.det_one, abs_one, one_mul]
  unfold gravityBFCurvatureIncrementDensity
  rw [← gravityAuxiliaryHodgePairingPolynomial_eq
    (1 : LorentzianCoframe) (by simp)]
  unfold gravityAuxiliaryHodgePairingPolynomial
    lorentzConnectionAlgebraicCurvatureDirection
    lorentzConnectionAlgebraicCurvatureVariation
  rw [residualLimitArbitraryOriginReader_gravityConnection_origin]
  simp [physicalIIPlusBivector, internalBivectorDual, coframeWedge,
    coframeTwoFormLinear, residualLimitReferenceDivergenceOriginPreimage,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    lorentzianCoframeHodge, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond,
    Matrix.one_apply, Fin.sum_univ_six, Fin.sum_univ_four]
  ring

/-- The complete divergence response has exactly one lowered-origin preimage.
No caller may select a different representative inside this audited carrier. -/
theorem residualLimitReferenceDivergenceOriginPreimage_unique
    (q : LorentzBivectorOneForm)
    (response : residualLimitOriginAlgebraicResponse q =
      residualLimitReferenceDivergenceResponse) :
    q = residualLimitReferenceDivergenceOriginPreimage := by
  apply residualLimitOriginAlgebraicResponseCoordinates_bijective.1
  funext formDirection internalPair
  calc
    residualLimitOriginAlgebraicResponseCoordinates q
          formDirection internalPair =
        residualLimitOriginAlgebraicResponse q
          (residualLimitLorentzBasisDirection formDirection internalPair) :=
      (residualLimitOriginAlgebraicResponse_basis
        q formDirection internalPair).symm
    _ = residualLimitReferenceDivergenceResponse
          (residualLimitLorentzBasisDirection formDirection internalPair) :=
      congrFun response _
    _ = residualLimitOriginAlgebraicResponse
          residualLimitReferenceDivergenceOriginPreimage
          (residualLimitLorentzBasisDirection formDirection internalPair) :=
      (congrFun residualLimitReferenceDivergenceOriginPreimage_response _).symm
    _ = residualLimitOriginAlgebraicResponseCoordinates
          residualLimitReferenceDivergenceOriginPreimage
          formDirection internalPair :=
      residualLimitOriginAlgebraicResponse_basis
        residualLimitReferenceDivergenceOriginPreimage
        formDirection internalPair

/-- At the explicit existing-carrier preimage, the complete gravity--BF
balance function is zero.  No quotient or supplied zero premise is used. -/
theorem residualLimitReferenceDivergenceOriginPreimage_gravityBFBalance_zero :
    (fun direction =>
      lorentzGravityBFBalanceCoefficient
        (residualLimitArbitraryOriginReader
          residualLimitReferenceDivergenceOriginPreimage)
        direction 0) = 0 := by
  funext direction
  have algebraicEq := congrFun
    residualLimitReferenceDivergenceOriginPreimage_response direction
  have divergenceEq := congrFun
    (residualLimitOriginDivergenceResponse_eq_reference
      residualLimitReferenceDivergenceOriginPreimage) direction
  unfold residualLimitOriginAlgebraicResponse at algebraicEq
  unfold residualLimitOriginDivergenceResponse at divergenceEq
  unfold lorentzGravityBFBalanceCoefficient
  rw [algebraicEq, divergenceEq]
  simp

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzOriginResponsePreimage
