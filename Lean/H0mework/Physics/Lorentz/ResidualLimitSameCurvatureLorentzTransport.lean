import H0mework.Physics.Source.ProofFreeSource
import H0mework.Physics.Geometry.JointShellZeroFiber
import H0mework.Physics.Lorentz.LorentzConnectionActionVariation
import H0mework.Physics.Lorentz.ResidualLimitLorentzClassObstruction

/-!
# S9-C3h30: same-curvature scalar-origin Lorentz transport

This module varies only the origin value of the existing normalized
affine Lorentz-connection germ through the restricted scalar family

`omega0(c) = c • positiveSourceGravityMouthOriginConnectionValue`.

The target curvature remains the already-derived residual-limit curvature;
the coframe, gravity auxiliary, gauge fields, scalar, and three completion
fields remain those of `residualLimitLorentzCarrierReader`.  Thus `c` is an
audit coordinate on one explicit same-curvature connection fiber, not a new
source value, coupling, physical knob, branch receipt, or whole-shell
parameterization.

The framework transports the residual `r=A-D`, not the two response channels
separately.  As proved by C3h29, a transported response pair may therefore
carry a common diagonal displacement `q`:

`A' = k*A + q`, `D' = k*D + q`.

This module computes how the much narrower scalar-origin section sits inside
that fiber.  Its algebraic component scales by `c`, while its
differential-divergence component is frozen.  Direct expansion of the actual
transvection coframe and its generated `II+` auxiliary proves the complete
formula `D(direction)=direction 0 5`, so `D` is nonzero.  After the
algebraic-only coordinate forces `c=k`, the frozen divergence leaves no common
diagonal displacement capable of realizing `k != 1`; exact transport in this
restricted section is therefore possible exactly when `c=k=1`.

Nonzero `D` is not itself an obstruction to residual transport.  The
class-specific no-go says only that this frozen-`D` scalar-origin section does
not produce the diagonal endpoint motion required by the first formula.  It
does not extend to arbitrary origin connections, the whole shell, or
stationarity.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitSameCurvatureLorentzTransport

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

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## The restricted actual same-curvature family -/

/-- Scalar-origin subfamily of the existing normalized affine right inverse.
This does not assert that arbitrary scalar values are source-generated. -/
def residualLimitSameCurvatureScalarOriginConnectionField
    (c : ℝ) : LorentzConnectionField :=
  normalizedAffineLorentzConnectionField
    (c • positiveSourceGravityMouthOriginConnectionValue)
    positiveSourceGravityMouthResidualLimitCurvature

/-- Install the restricted connection while retaining every other field of
the actual C3h27 reader. -/
def residualLimitSameCurvatureScalarOriginReader
    (c : ℝ) : StageNineHolonomicConfiguration :=
  { residualLimitLorentzCarrierReader with
    gravityConnection :=
      residualLimitSameCurvatureScalarOriginConnectionField c }

@[simp] theorem residualLimitSameCurvatureScalarOriginReader_coframe
    (c : ℝ) :
    (residualLimitSameCurvatureScalarOriginReader c).coframe =
      residualLimitLorentzCarrierReader.coframe :=
  rfl

@[simp] theorem residualLimitSameCurvatureScalarOriginReader_gravityAuxiliary
    (c : ℝ) :
    (residualLimitSameCurvatureScalarOriginReader c).gravityAuxiliary =
      residualLimitLorentzCarrierReader.gravityAuxiliary :=
  rfl

@[simp] theorem residualLimitSameCurvatureScalarOriginConnectionField_origin
    (c : ℝ) :
    residualLimitSameCurvatureScalarOriginConnectionField c 0 =
      c • positiveSourceGravityMouthOriginConnectionValue :=
  normalizedAffineLorentzConnectionField_zero _ _

@[simp] theorem residualLimitSameCurvatureScalarOriginReader_gravityConnection_origin
    (c : ℝ) :
    (residualLimitSameCurvatureScalarOriginReader c).gravityConnection 0 =
      c • positiveSourceGravityMouthOriginConnectionValue :=
  residualLimitSameCurvatureScalarOriginConnectionField_origin c

/-- Every member has the same actual `d omega + omega wedge omega` curvature
at the origin.  Curvature is recomputed from the field, not stored. -/
theorem residualLimitSameCurvatureScalarOriginReader_curvature_origin
    (c : ℝ) :
    holonomicGravityCurvature
        (residualLimitSameCurvatureScalarOriginReader c) 0 =
      positiveSourceGravityMouthResidualLimitCurvature := by
  change holonomicGravityCurvature
      (normalizedAffineConfiguration
        (c • positiveSourceGravityMouthOriginConnectionValue)
        positiveSourceGravityMouthResidualLimitCurvature) 0 =
    positiveSourceGravityMouthResidualLimitCurvature
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

/-- The source-derived member `c=1` is exactly the C3h27 reader. -/
theorem residualLimitSameCurvatureScalarOriginReader_one :
    residualLimitSameCurvatureScalarOriginReader 1 =
      residualLimitLorentzCarrierReader := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  change normalizedAffineLorentzConnectionField
      (1 • positiveSourceGravityMouthOriginConnectionValue)
      positiveSourceGravityMouthResidualLimitCurvature =
    positiveSourceGravityMouthResidualLimitConnectionField
  simp [positiveSourceGravityMouthResidualLimitConnectionField]

/-! ## The existing three-coordinate algebraic shell is preserved -/

theorem residualLimitSameCurvatureScalarOriginReader_gravitySimplicity_zero
    (c : ℝ) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitSameCurvatureScalarOriginReader c) 0).gravitySimplicity =
      0 := by
  change generatedGravitySimplicityResidual
      (toContinuumPointField
        (residualLimitSameCurvatureScalarOriginReader c) 0) = 0
  exact (gravitySimplicityResidual_eq_zero_iff
    (residualLimitSameCurvatureScalarOriginReader c) 0).mpr (by rfl)

theorem residualLimitSameCurvatureScalarOriginReader_gravityAuxiliary_zero
    (c : ℝ) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitSameCurvatureScalarOriginReader c) 0).gravityAuxiliary =
      0 := by
  change holonomicGravityAuxiliaryEquationResidual
      (residualLimitSameCurvatureScalarOriginReader c) 0 = 0
  apply (gravityAuxiliaryResidual_eq_zero_iff
    (residualLimitSameCurvatureScalarOriginReader c) 0).mpr
  rw [residualLimitSameCurvatureScalarOriginReader_curvature_origin]
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

theorem residualLimitSameCurvatureScalarOriginReader_p286GaugeAuxiliary_zero
    (c : ℝ) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitSameCurvatureScalarOriginReader c) 0).p286GaugeAuxiliary =
      0 := by
  change
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      residualLimitLorentzCarrierReader 0).p286GaugeAuxiliary = 0
  exact residualLimitExtension_p286GaugeAuxiliaryResidual_origin
    residualLimitLorentzCarrierReader residualLimitLorentzCarrierReader_extends

/-- The full strong algebraic triple stays zero throughout this explicit
same-curvature fiber. -/
theorem residualLimitSameCurvatureScalarOriginReader_algebraicResidual_zero
    (c : ℝ) :
    currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitSameCurvatureScalarOriginReader c) 0 = 0 := by
  apply CurrentPointwiseAlgebraicResidualCarrier.ext
  · exact
      residualLimitSameCurvatureScalarOriginReader_gravitySimplicity_zero c
  · exact residualLimitSameCurvatureScalarOriginReader_gravityAuxiliary_zero c
  · exact
      residualLimitSameCurvatureScalarOriginReader_p286GaugeAuxiliary_zero c

/-! ## Complete Lorentz response pair -/

abbrev RestrictedLorentzResponse := LorentzBivectorOneForm → ℝ

def residualLimitSameCurvatureAlgebraicResponse
    (c : ℝ) : RestrictedLorentzResponse :=
  fun direction =>
    lorentzGravityBFAlgebraicCoefficient
      (residualLimitSameCurvatureScalarOriginReader c) direction 0

def residualLimitSameCurvatureDivergenceResponse
    (c : ℝ) : RestrictedLorentzResponse :=
  fun direction =>
    lorentzConnectionBFDifferentialMomentumDivergence
      (residualLimitSameCurvatureScalarOriginReader c) direction 0

def residualLimitSameCurvatureBalance
    (c : ℝ) : RestrictedLorentzResponse :=
  residualLimitSameCurvatureAlgebraicResponse c -
    residualLimitSameCurvatureDivergenceResponse c

def residualLimitReferenceAlgebraicResponse : RestrictedLorentzResponse :=
  fun direction =>
    lorentzGravityBFAlgebraicCoefficient residualLimitLorentzCarrierReader
      direction 0

def residualLimitReferenceDivergenceResponse : RestrictedLorentzResponse :=
  fun direction =>
    lorentzConnectionBFDifferentialMomentumDivergence
      residualLimitLorentzCarrierReader direction 0

/-- At the origin the algebraic curvature direction scales exactly with the
restricted origin connection value. -/
theorem residualLimitSameCurvature_algebraicCurvatureDirection_eq_smul
    (c : ℝ) (direction : LorentzBivectorOneForm) :
    lorentzConnectionAlgebraicCurvatureDirection
        (residualLimitSameCurvatureScalarOriginReader c) direction 0 =
      c • lorentzConnectionAlgebraicCurvatureDirection
        residualLimitLorentzCarrierReader direction 0 := by
  funext internalPair spacetimePair
  unfold lorentzConnectionAlgebraicCurvatureDirection
    lorentzConnectionAlgebraicCurvatureVariation
  dsimp only
  rw [residualLimitSameCurvatureScalarOriginReader_gravityConnection_origin,
    residualLimitLorentzCarrierReader_gravityConnection_origin]
  simp only [Pi.smul_apply, smul_eq_mul]
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [pairFirst, pairSecond, Fin.sum_univ_four] <;> ring

/-- Complete algebraic response formula: the entire function, not only one
basis coordinate, scales by `c`. -/
theorem residualLimitSameCurvatureAlgebraicResponse_eq_smul
    (c : ℝ) :
    residualLimitSameCurvatureAlgebraicResponse c =
      c • residualLimitReferenceAlgebraicResponse := by
  funext direction
  unfold residualLimitSameCurvatureAlgebraicResponse
    residualLimitReferenceAlgebraicResponse
    lorentzGravityBFAlgebraicCoefficient
  rw [residualLimitSameCurvature_algebraicCurvatureDirection_eq_smul,
    gravityBFCurvatureIncrementDensity_smul]
  change
    generatedVolumeDensity
        (toContinuumPointField residualLimitLorentzCarrierReader 0) *
          (c * gravityBFCurvatureIncrementDensity
            (residualLimitLorentzCarrierReader.coframe 0)
            (residualLimitLorentzCarrierReader.gravityAuxiliary 0)
            (lorentzConnectionAlgebraicCurvatureDirection
              residualLimitLorentzCarrierReader direction 0)) =
      c *
        (generatedVolumeDensity
          (toContinuumPointField residualLimitLorentzCarrierReader 0) *
            gravityBFCurvatureIncrementDensity
              (residualLimitLorentzCarrierReader.coframe 0)
              (residualLimitLorentzCarrierReader.gravityAuxiliary 0)
              (lorentzConnectionAlgebraicCurvatureDirection
                residualLimitLorentzCarrierReader direction 0))
  ring

/-- The differential momentum reads only coframe and gravity auxiliary, so it
is fixed over the whole restricted connection fiber. -/
theorem residualLimitSameCurvatureDivergenceResponse_eq_reference
    (c : ℝ) :
    residualLimitSameCurvatureDivergenceResponse c =
      residualLimitReferenceDivergenceResponse := by
  funext direction
  have momentumEq (derivativeDirection : LorentzianIndex) :
      lorentzConnectionBFDifferentialMomentum
          (residualLimitSameCurvatureScalarOriginReader c)
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
  unfold residualLimitSameCurvatureDivergenceResponse
    residualLimitReferenceDivergenceResponse
    lorentzConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [momentumEq derivativeDirection]

/-- Exact finite normal form of the four differential-momentum functions.
The only term differentiated in its own coordinate is the `mu=2` coefficient
`point 2 * direction 0 5`. -/
def residualLimitReferenceDifferentialMomentumNormalForm
    (direction : LorentzBivectorOneForm)
    (derivativeDirection : LorentzianIndex) (point : BasePoint) : ℝ :=
  if derivativeDirection = 0 then
    direction 1 0 + direction 2 1 + direction 3 2 +
      point 2 * (direction 3 4 - direction 2 5)
  else if derivativeDirection = 1 then
    -direction 0 0 - direction 3 4 + direction 2 5
  else if derivativeDirection = 2 then
    -direction 0 1 + direction 3 3 - direction 1 5 +
      point 2 * direction 0 5
  else
    -direction 0 2 - direction 2 3 + direction 1 4 -
      point 2 * direction 0 4

set_option maxRecDepth 100000 in
/-- Direct expansion of the actual transvection coframe and its generated
`II+` auxiliary gives the complete four-direction momentum normal form. -/
theorem residualLimitReference_differentialMomentum_exterior_eq_normalForm
    (direction : LorentzBivectorOneForm)
    (derivativeDirection : LorentzianIndex) (point : BasePoint) :
    lorentzConnectionBFDifferentialMomentum residualLimitLorentzCarrierReader
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          direction) point =
      residualLimitReferenceDifferentialMomentumNormalForm direction
        derivativeDirection point := by
  have volumeOne :
      generatedVolumeDensity
          (toContinuumPointField residualLimitLorentzCarrierReader point) = 1 := by
    unfold generatedVolumeDensity toContinuumPointField
    rw [residualLimitLorentzCarrierReader_coframe,
      canonicalPhysicalSource_coframeAt_det]
    norm_num
  unfold lorentzConnectionBFDifferentialMomentum
  rw [volumeOne, one_mul, residualLimitLorentzCarrierReader_coframe,
    residualLimitLorentzCarrierReader_gravityAuxiliary]
  fin_cases derivativeDirection <;>
    simp [residualLimitReferenceDifferentialMomentumNormalForm,
      gravityAuxiliaryHodgePairingPolynomial,
      canonicalPhysicalSource_coframeAt_eq_transvection,
      physicalIIPlusBivector, internalBivectorDual, coframeWedge,
      coframeTwoFormLinear, lorentzConnectionExteriorDerivativeDirection,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond,
      Matrix.transvection, Matrix.single, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Fin.sum_univ_six] <;> ring

/-- Directional derivative of an affine function in the only active base
coordinate. -/
theorem fieldDirectionalDerivative_const_add_coordinateTwo_mul
    (constant slope : ℝ) (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point : BasePoint => constant + point 2 * slope) 0
        derivativeDirection =
      if derivativeDirection = 2 then slope else 0 := by
  unfold fieldDirectionalDerivative
  have coordinateDerivative :
      HasFDerivAt (fun point : BasePoint => point 2) (baseCoordinate 2) 0 :=
    (baseCoordinate 2).hasFDerivAt
  have affineDerivative :=
    (coordinateDerivative.mul_const' slope).const_add constant
  rw [affineDerivative.fderiv]
  fin_cases derivativeDirection <;>
    simp [baseCoordinate, coordinateDirection]

/-- The complete differential divergence is the `(form=0,pair=12)`
evaluation functional.  In particular it is not the zero function. -/
theorem residualLimitReferenceDivergenceResponse_apply
    (direction : LorentzBivectorOneForm) :
    residualLimitReferenceDivergenceResponse direction = direction 0 5 := by
  have momentumFunctionEq (derivativeDirection : LorentzianIndex) :
      lorentzConnectionBFDifferentialMomentum residualLimitLorentzCarrierReader
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction) =
        residualLimitReferenceDifferentialMomentumNormalForm direction
          derivativeDirection := by
    funext point
    exact residualLimitReference_differentialMomentum_exterior_eq_normalForm
      direction derivativeDirection point
  unfold residualLimitReferenceDivergenceResponse
    lorentzConnectionBFDifferentialMomentumDivergence
  rw [Fin.sum_univ_four]
  rw [momentumFunctionEq 0, momentumFunctionEq 1, momentumFunctionEq 2,
    momentumFunctionEq 3]
  rw [show residualLimitReferenceDifferentialMomentumNormalForm direction 0 =
      (fun point : BasePoint =>
        (direction 1 0 + direction 2 1 + direction 3 2) +
          point 2 * (direction 3 4 - direction 2 5)) by
        funext point
        simp [residualLimitReferenceDifferentialMomentumNormalForm]]
  rw [show residualLimitReferenceDifferentialMomentumNormalForm direction 1 =
      (fun point : BasePoint =>
        (-direction 0 0 - direction 3 4 + direction 2 5) +
          point 2 * 0) by
        funext point
        simp [residualLimitReferenceDifferentialMomentumNormalForm]]
  rw [show residualLimitReferenceDifferentialMomentumNormalForm direction 2 =
      (fun point : BasePoint =>
        (-direction 0 1 + direction 3 3 - direction 1 5) +
          point 2 * direction 0 5) by
        funext point
        simp [residualLimitReferenceDifferentialMomentumNormalForm]]
  rw [show residualLimitReferenceDifferentialMomentumNormalForm direction 3 =
      (fun point : BasePoint =>
        (-direction 0 2 - direction 2 3 + direction 1 4) +
          point 2 * (-direction 0 4)) by
        funext point
        simp [residualLimitReferenceDifferentialMomentumNormalForm]
        ring]
  rw [fieldDirectionalDerivative_const_add_coordinateTwo_mul,
    fieldDirectionalDerivative_const_add_coordinateTwo_mul,
    fieldDirectionalDerivative_const_add_coordinateTwo_mul,
    fieldDirectionalDerivative_const_add_coordinateTwo_mul]
  simp

theorem residualLimitReferenceDivergenceResponse_basis_zero_five_eq_one :
    residualLimitReferenceDivergenceResponse
        (residualLimitLorentzBasisDirection 0 5) = 1 := by
  rw [residualLimitReferenceDivergenceResponse_apply]
  simp [residualLimitLorentzBasisDirection]

theorem residualLimitReferenceDivergenceResponse_ne_zero :
    residualLimitReferenceDivergenceResponse ≠ 0 := by
  intro divergenceZero
  have pointZero := congrFun divergenceZero
    (residualLimitLorentzBasisDirection 0 5)
  rw [residualLimitReferenceDivergenceResponse_basis_zero_five_eq_one]
    at pointZero
  norm_num at pointZero

/-- Exact complete response-pair normal form over the restricted fiber. -/
theorem residualLimitSameCurvature_responsePair_eq
    (c : ℝ) :
    (residualLimitSameCurvatureAlgebraicResponse c,
        residualLimitSameCurvatureDivergenceResponse c) =
      (c • residualLimitReferenceAlgebraicResponse,
        residualLimitReferenceDivergenceResponse) := by
  rw [residualLimitSameCurvatureAlgebraicResponse_eq_smul,
    residualLimitSameCurvatureDivergenceResponse_eq_reference]

/-- Exact balance formula.  In particular, the divergence is not silently
set to zero. -/
theorem residualLimitSameCurvatureBalance_eq
    (c : ℝ) :
    residualLimitSameCurvatureBalance c =
      c • residualLimitReferenceAlgebraicResponse -
        residualLimitReferenceDivergenceResponse := by
  unfold residualLimitSameCurvatureBalance
  rw [residualLimitSameCurvatureAlgebraicResponse_eq_smul,
    residualLimitSameCurvatureDivergenceResponse_eq_reference]

theorem positiveResidualLimitLorentzBalance_eq_referenceDifference :
    positiveResidualLimitLorentzBalance =
      residualLimitReferenceAlgebraicResponse -
        residualLimitReferenceDivergenceResponse := by
  rfl

/-! ## Exact K-transport zero fiber in the restricted class -/

/-- For arbitrary transport scalar `k`, reachability is exactly one displayed
function zero-fiber condition. -/
theorem residualLimitSameCurvature_transport_iff_zeroFiber
    (c k : ℝ) :
    residualLimitSameCurvatureBalance c =
        k • positiveResidualLimitLorentzBalance ↔
      (c - k) • residualLimitReferenceAlgebraicResponse +
          (k - 1) • residualLimitReferenceDivergenceResponse = 0 := by
  rw [residualLimitSameCurvatureBalance_eq,
    positiveResidualLimitLorentzBalance_eq_referenceDifference]
  constructor
  · intro transport
    funext direction
    have pointTransport := congrFun transport direction
    change
      c * residualLimitReferenceAlgebraicResponse direction -
          residualLimitReferenceDivergenceResponse direction =
        k *
          (residualLimitReferenceAlgebraicResponse direction -
            residualLimitReferenceDivergenceResponse direction)
      at pointTransport
    change
      (c - k) * residualLimitReferenceAlgebraicResponse direction +
          (k - 1) * residualLimitReferenceDivergenceResponse direction = 0
    linarith
  · intro zeroFiber
    funext direction
    have pointZero := congrFun zeroFiber direction
    change
      (c - k) * residualLimitReferenceAlgebraicResponse direction +
          (k - 1) * residualLimitReferenceDivergenceResponse direction = 0
      at pointZero
    change
      c * residualLimitReferenceAlgebraicResponse direction -
          residualLimitReferenceDivergenceResponse direction =
        k *
          (residualLimitReferenceAlgebraicResponse direction -
            residualLimitReferenceDivergenceResponse direction)
    linarith

/-- The C3h27 tested coordinate reads `(A,D)=(1,0)` throughout the reference
pair. -/
theorem residualLimitReferenceResponse_basis_two_zero :
    residualLimitReferenceAlgebraicResponse
          (residualLimitLorentzBasisDirection 2 0) = 1 ∧
      residualLimitReferenceDivergenceResponse
          (residualLimitLorentzBasisDirection 2 0) = 0 := by
  exact
    ⟨residualLimitLorentzCarrierReader_algebraic_basis_two_zero_eq_one,
      residualLimitLorentzCarrierReader_divergence_basis_two_zero_eq_zero⟩

/-- Any transported member of this restricted fiber has a forced scalar.
This proves uniqueness of the only possible audit coordinate; it does not
prove that the forced member satisfies the complete function equation. -/
theorem residualLimitSameCurvature_transport_forces_c
    (c k : ℝ)
    (transport : residualLimitSameCurvatureBalance c =
      k • positiveResidualLimitLorentzBalance) :
    c = k := by
  have pointTransport := congrFun transport
    (residualLimitLorentzBasisDirection 2 0)
  rw [residualLimitSameCurvatureBalance_eq,
    positiveResidualLimitLorentzBalance_eq_referenceDifference] at pointTransport
  change
    c * residualLimitReferenceAlgebraicResponse
          (residualLimitLorentzBasisDirection 2 0) -
        residualLimitReferenceDivergenceResponse
          (residualLimitLorentzBasisDirection 2 0) =
      k *
        (residualLimitReferenceAlgebraicResponse
            (residualLimitLorentzBasisDirection 2 0) -
          residualLimitReferenceDivergenceResponse
            (residualLimitLorentzBasisDirection 2 0))
    at pointTransport
  rw [residualLimitReferenceResponse_basis_two_zero.1,
    residualLimitReferenceResponse_basis_two_zero.2] at pointTransport
  linarith

/-- Complete classification in the restricted scalar-origin fiber.  The
algebraic-only coordinate first forces `c=k`; the remaining frozen nonzero
divergence mismatch then forces `k=1`.  This is a failure of the restricted
section to produce the required diagonal response displacement, not a claim
that nonzero divergence obstructs residual transport in general. -/
theorem residualLimitSameCurvature_transport_iff_c_eq_and_k_eq_one
    (c k : ℝ) :
    residualLimitSameCurvatureBalance c =
        k • positiveResidualLimitLorentzBalance ↔
      c = k ∧ k = 1 := by
  constructor
  · intro transport
    have cEquality :=
      residualLimitSameCurvature_transport_forces_c c k transport
    have zeroFiber :=
      (residualLimitSameCurvature_transport_iff_zeroFiber c k).mp transport
    rw [cEquality, sub_self, zero_smul, zero_add] at zeroFiber
    have pointZero := congrFun zeroFiber
      (residualLimitLorentzBasisDirection 0 5)
    change (k - 1) * residualLimitReferenceDivergenceResponse
        (residualLimitLorentzBasisDirection 0 5) = 0 at pointZero
    rw [residualLimitReferenceDivergenceResponse_basis_zero_five_eq_one]
      at pointZero
    change (k - 1) * 1 = 0 at pointZero
    exact ⟨cEquality, by linarith⟩
  · rintro ⟨cEquality, kEquality⟩
    rw [cEquality, kEquality, residualLimitSameCurvatureBalance_eq,
      positiveResidualLimitLorentzBalance_eq_referenceDifference]
    simp

/-- For the actual source `K = 1-sigma`, the only possible scalar-origin
member is canonically forced; no caller choice remains. -/
theorem residualLimitSameCurvature_actualTransport_forces_c
    (c : ℝ)
    (transport : residualLimitSameCurvatureBalance c =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        positiveResidualLimitLorentzBalance) :
    c = 1 - positiveSmoothUnifiedSource.legacy.sigma :=
  residualLimitSameCurvature_transport_forces_c c
    (1 - positiveSmoothUnifiedSource.legacy.sigma) transport

/-- At the uniquely forced scalar, actual K-transport exists exactly when the
complete fixed divergence response vanishes after multiplication by sigma. -/
theorem residualLimitSameCurvature_forced_actualTransport_iff_sigmaDivergenceZero :
    residualLimitSameCurvatureBalance
          (1 - positiveSmoothUnifiedSource.legacy.sigma) =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          positiveResidualLimitLorentzBalance ↔
      positiveSmoothUnifiedSource.legacy.sigma •
          residualLimitReferenceDivergenceResponse = 0 := by
  rw [residualLimitSameCurvature_transport_iff_zeroFiber]
  have coefficientEquality :
      (1 - positiveSmoothUnifiedSource.legacy.sigma) - 1 =
        -positiveSmoothUnifiedSource.legacy.sigma := by
    ring
  rw [sub_self, zero_smul, zero_add, coefficientEquality, neg_smul,
    neg_eq_zero]

/-- Positivity of the already-generated sigma removes the scalar factor.  The
complete-divergence condition remains an explicit readout in this theorem
mouth; its vanishing is derived separately below, not supplied as a shell receipt. -/
theorem residualLimitSameCurvature_forced_actualTransport_iff_divergenceZero :
    residualLimitSameCurvatureBalance
          (1 - positiveSmoothUnifiedSource.legacy.sigma) =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          positiveResidualLimitLorentzBalance ↔
      residualLimitReferenceDivergenceResponse = 0 := by
  rw [
    residualLimitSameCurvature_forced_actualTransport_iff_sigmaDivergenceZero]
  constructor
  · intro scaledZero
    funext direction
    have pointZero := congrFun scaledZero direction
    change positiveSmoothUnifiedSource.legacy.sigma *
        residualLimitReferenceDivergenceResponse direction = 0 at pointZero
    exact (mul_eq_zero.mp pointZero).resolve_left
      (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos)
  · intro divergenceZero
    rw [divergenceZero, smul_zero]

/-- Existence and uniqueness within the explicit scalar-origin family reduce
to the same complete divergence zero condition.  The unique witness, when it
exists, is the already-forced `1-sigma`; it is not chosen from a supplied
endpoint receipt. -/
theorem existsUnique_residualLimitSameCurvature_actualTransport_iff :
    (∃! c : ℝ,
      residualLimitSameCurvatureBalance c =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          positiveResidualLimitLorentzBalance) ↔
      residualLimitReferenceDivergenceResponse = 0 := by
  constructor
  · rintro ⟨c, transport, _unique⟩
    have cEquality :=
      residualLimitSameCurvature_actualTransport_forces_c c transport
    rw [cEquality] at transport
    exact
      residualLimitSameCurvature_forced_actualTransport_iff_divergenceZero.mp
        transport
  · intro divergenceZero
    have forcedTransport :=
      residualLimitSameCurvature_forced_actualTransport_iff_divergenceZero.mpr
        divergenceZero
    refine ⟨1 - positiveSmoothUnifiedSource.legacy.sigma, forcedTransport, ?_⟩
    intro candidate candidateTransport
    exact residualLimitSameCurvature_actualTransport_forces_c
      candidate candidateTransport

/-- The actual source keep `K=1-sigma` is not `1`, so no member of this
restricted scalar-origin, frozen-divergence section realizes residual
transport.  This is not a no-go for arbitrary origin connections, arbitrary
response-pair endpoints, or the whole shell. -/
theorem residualLimitSameCurvature_not_actualTransport
    (c : ℝ) :
    residualLimitSameCurvatureBalance c ≠
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        positiveResidualLimitLorentzBalance := by
  intro transport
  have classification :=
    (residualLimitSameCurvature_transport_iff_c_eq_and_k_eq_one c
      (1 - positiveSmoothUnifiedSource.legacy.sigma)).mp transport
  have sigmaZero : positiveSmoothUnifiedSource.legacy.sigma = 0 := by
    linarith [classification.2]
  exact (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos) sigmaZero

theorem not_exists_residualLimitSameCurvature_actualTransport :
    ¬ ∃ c : ℝ,
      residualLimitSameCurvatureBalance c =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          positiveResidualLimitLorentzBalance := by
  rintro ⟨c, transport⟩
  exact residualLimitSameCurvature_not_actualTransport c transport

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitSameCurvatureLorentzTransport
