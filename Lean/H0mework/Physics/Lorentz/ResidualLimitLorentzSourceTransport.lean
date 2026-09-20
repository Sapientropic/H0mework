import H0mework.Physics.Lorentz.ResidualLimitLorentzOriginResponsePreimage

/-!
# S9-C3h32: source-derived Lorentz response transport

This module varies the origin of the existing normalized-affine connection
right inverse by an arbitrary lowered Lorentz one-form `q`:

`omega₀(q) = omega_source + lorentzSkewConnectionOfBivectorOneForm q`.

The target curvature is the already-derived residual-limit curvature and all
other fields remain those of the C3h27 reader.  Thus `q` is a coordinate on an
existing same-curvature fiber.  It is not source data, a coupling, a branch
choice, a shell receipt, or a stationarity premise.

The actual algebraic-response displacement `L(q) = A(q) - A(0)` is computed
below.  The differential response `D` is frozen.  Consequently the framework
equation

`A' = K A + (I-K) D`, with `K = 1-sigma`,

is equivalent to the derived equation `L(q) = -sigma * (A-D)`.  No endpoint
response is accepted as a theorem premise.

The source origin is converted to lowered coordinates by an actual readout and
reconstructed exactly.  C3h31's unique differential-response preimage then
forces the parameter-free relative coordinate

`q* = -sigma * (q_source - q_D)`.

The resulting field has the same curvature and strong algebraic shell, and
its complete Lorentz residual obeys `r'=Kr`.  Injectivity of the actual
response operator proves that every relative-origin candidate satisfying the
endpoint equation equals `q*`.

This is a real producer only for the Lorentz response inside the declared
same-curvature connection fiber.  It does not close the other eight residual
coordinates, compact-support joint stationarity, local constraint
propagation, global action, quantum credential, or prediction lock.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzSourceTransport

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
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
open StageNineResidualLimitLorentzOriginResponsePreimage
open StageNineResidualLimitSameCurvatureLorentzTransport
open PointwiseDiracSpinConnectionLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Existing arbitrary-origin same-curvature fiber -/

/-- Relative origin coordinate in the existing Lorentz-skew carrier. -/
def residualLimitRelativeOrigin
    (q : LorentzBivectorOneForm) : PointwiseLorentzSpinConnection :=
  positiveSourceGravityMouthOriginConnectionValue +
    lorentzSkewConnectionOfBivectorOneForm q

/-- Existing normalized-affine right inverse at the fixed residual-limit
curvature, with only its origin coordinate varied. -/
def residualLimitRelativeOriginConnectionField
    (q : LorentzBivectorOneForm) : LorentzConnectionField :=
  normalizedAffineLorentzConnectionField
    (residualLimitRelativeOrigin q)
    positiveSourceGravityMouthResidualLimitCurvature

/-- Retain every non-connection field of the actual residual-limit reader. -/
def residualLimitRelativeOriginReader
    (q : LorentzBivectorOneForm) : StageNineHolonomicConfiguration :=
  { residualLimitLorentzCarrierReader with
    gravityConnection := residualLimitRelativeOriginConnectionField q }

@[simp] theorem residualLimitRelativeOriginReader_coframe
    (q : LorentzBivectorOneForm) :
    (residualLimitRelativeOriginReader q).coframe =
      residualLimitLorentzCarrierReader.coframe :=
  rfl

@[simp] theorem residualLimitRelativeOriginReader_gravityAuxiliary
    (q : LorentzBivectorOneForm) :
    (residualLimitRelativeOriginReader q).gravityAuxiliary =
      residualLimitLorentzCarrierReader.gravityAuxiliary :=
  rfl

@[simp] theorem residualLimitRelativeOriginConnectionField_origin
    (q : LorentzBivectorOneForm) :
    residualLimitRelativeOriginConnectionField q 0 =
      residualLimitRelativeOrigin q :=
  normalizedAffineLorentzConnectionField_zero _ _

@[simp] theorem residualLimitRelativeOriginReader_gravityConnection_origin
    (q : LorentzBivectorOneForm) :
    (residualLimitRelativeOriginReader q).gravityConnection 0 =
      residualLimitRelativeOrigin q :=
  residualLimitRelativeOriginConnectionField_origin q

/-- The zero relative coordinate is exactly the source-derived C3h27 reader. -/
theorem residualLimitRelativeOriginReader_zero :
    residualLimitRelativeOriginReader 0 = residualLimitLorentzCarrierReader := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  change normalizedAffineLorentzConnectionField
      (positiveSourceGravityMouthOriginConnectionValue +
        lorentzSkewConnectionOfBivectorOneForm 0)
      positiveSourceGravityMouthResidualLimitCurvature =
    positiveSourceGravityMouthResidualLimitConnectionField
  rw [show lorentzSkewConnectionOfBivectorOneForm
        (0 : LorentzBivectorOneForm) = 0 by
    funext formDirection internalOut internalIn
    simp [lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix]]
  simp [positiveSourceGravityMouthResidualLimitConnectionField]

/-- Curvature is recomputed from each generated germ and remains the fixed
residual-limit curvature. -/
theorem residualLimitRelativeOriginReader_curvature_origin
    (q : LorentzBivectorOneForm) :
    holonomicGravityCurvature (residualLimitRelativeOriginReader q) 0 =
      positiveSourceGravityMouthResidualLimitCurvature := by
  change holonomicGravityCurvature
      (normalizedAffineConfiguration
        (residualLimitRelativeOrigin q)
        positiveSourceGravityMouthResidualLimitCurvature) 0 =
    positiveSourceGravityMouthResidualLimitCurvature
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

/-! ## Existing algebraic shell remains zero -/

theorem residualLimitRelativeOriginReader_gravitySimplicity_zero
    (q : LorentzBivectorOneForm) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitRelativeOriginReader q) 0).gravitySimplicity = 0 := by
  change generatedGravitySimplicityResidual
      (toContinuumPointField (residualLimitRelativeOriginReader q) 0) = 0
  exact (gravitySimplicityResidual_eq_zero_iff
    (residualLimitRelativeOriginReader q) 0).mpr (by rfl)

theorem residualLimitRelativeOriginReader_gravityAuxiliary_zero
    (q : LorentzBivectorOneForm) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitRelativeOriginReader q) 0).gravityAuxiliary = 0 := by
  change holonomicGravityAuxiliaryEquationResidual
      (residualLimitRelativeOriginReader q) 0 = 0
  apply (gravityAuxiliaryResidual_eq_zero_iff
    (residualLimitRelativeOriginReader q) 0).mpr
  rw [residualLimitRelativeOriginReader_curvature_origin]
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

theorem residualLimitRelativeOriginReader_p286GaugeAuxiliary_zero
    (q : LorentzBivectorOneForm) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitRelativeOriginReader q) 0).p286GaugeAuxiliary = 0 := by
  change
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      residualLimitLorentzCarrierReader 0).p286GaugeAuxiliary = 0
  exact residualLimitExtension_p286GaugeAuxiliaryResidual_origin
    residualLimitLorentzCarrierReader residualLimitLorentzCarrierReader_extends

/-- The full strong pointwise algebraic triple remains zero throughout this
existing same-curvature fiber. -/
theorem residualLimitRelativeOriginReader_algebraicResidual_zero
    (q : LorentzBivectorOneForm) :
    currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (residualLimitRelativeOriginReader q) 0 = 0 := by
  apply CurrentPointwiseAlgebraicResidualCarrier.ext
  · exact residualLimitRelativeOriginReader_gravitySimplicity_zero q
  · exact residualLimitRelativeOriginReader_gravityAuxiliary_zero q
  · exact residualLimitRelativeOriginReader_p286GaugeAuxiliary_zero q

/-! ## Actual response displacement -/

/-- Actual complete algebraic response in the relative-origin family. -/
def residualLimitRelativeOriginAlgebraicResponse
    (q : LorentzBivectorOneForm) : RestrictedLorentzResponse :=
  fun direction =>
    lorentzGravityBFAlgebraicCoefficient
      (residualLimitRelativeOriginReader q) direction 0

/-- Actual complete differential response in the same family. -/
def residualLimitRelativeOriginDivergenceResponse
    (q : LorentzBivectorOneForm) : RestrictedLorentzResponse :=
  fun direction =>
    lorentzConnectionBFDifferentialMomentumDivergence
      (residualLimitRelativeOriginReader q) direction 0

/-- The actual algebraic-response displacement operator `L(q)=A(q)-A(0)`. -/
def residualLimitOriginResponseDisplacement
    (q : LorentzBivectorOneForm) : RestrictedLorentzResponse :=
  residualLimitRelativeOriginAlgebraicResponse q -
    residualLimitReferenceAlgebraicResponse

/-- The differential response reads only coframe and gravity auxiliary, so it
is frozen throughout the arbitrary-origin fiber. -/
theorem residualLimitRelativeOriginDivergenceResponse_eq_reference
    (q : LorentzBivectorOneForm) :
    residualLimitRelativeOriginDivergenceResponse q =
      residualLimitReferenceDivergenceResponse := by
  funext direction
  have momentumEq (derivativeDirection : LorentzianIndex) :
      lorentzConnectionBFDifferentialMomentum
          (residualLimitRelativeOriginReader q)
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
  unfold residualLimitRelativeOriginDivergenceResponse
    residualLimitReferenceDivergenceResponse
    lorentzConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [momentumEq derivativeDirection]

/-! ## Complete linear normal form of `L` -/

set_option maxRecDepth 100000 in
/-- The actual relative-origin displacement is exactly the C3h31 absolute
origin response generated by the same coordinate `q`. -/
theorem residualLimitOriginResponseDisplacement_eq_absoluteResponse
    (q : LorentzBivectorOneForm) :
    residualLimitOriginResponseDisplacement q =
      residualLimitOriginAlgebraicResponse q := by
  funext direction
  unfold residualLimitOriginResponseDisplacement
    residualLimitRelativeOriginAlgebraicResponse
    residualLimitReferenceAlgebraicResponse
    residualLimitOriginAlgebraicResponse
    lorentzGravityBFAlgebraicCoefficient
  simp only [Pi.sub_apply]
  have volumeRelative :
      generatedVolumeDensity
          (toContinuumPointField (residualLimitRelativeOriginReader q) 0) =
        generatedVolumeDensity
          (toContinuumPointField residualLimitLorentzCarrierReader 0) := by
    unfold generatedVolumeDensity toContinuumPointField
    rfl
  have volumeAbsolute :
      generatedVolumeDensity
          (toContinuumPointField (residualLimitArbitraryOriginReader q) 0) =
        generatedVolumeDensity
          (toContinuumPointField residualLimitLorentzCarrierReader 0) := by
    unfold generatedVolumeDensity toContinuumPointField
    rfl
  rw [volumeRelative, volumeAbsolute]
  have curvatureDirectionSplit :
      lorentzConnectionAlgebraicCurvatureDirection
          (residualLimitRelativeOriginReader q) direction 0 =
        lorentzConnectionAlgebraicCurvatureDirection
            residualLimitLorentzCarrierReader direction 0 +
          lorentzConnectionAlgebraicCurvatureDirection
            (residualLimitArbitraryOriginReader q) direction 0 := by
    funext internalPair spacetimePair
    unfold lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    dsimp only
    rw [residualLimitRelativeOriginReader_gravityConnection_origin,
      residualLimitLorentzCarrierReader_gravityConnection_origin,
      residualLimitArbitraryOriginReader_gravityConnection_origin]
    unfold residualLimitRelativeOrigin
    simp only [Pi.add_apply]
    rw [← mul_add, ← Finset.sum_add_distrib]
    apply congrArg
    apply Finset.sum_congr rfl
    intro middle _
    ring
  rw [curvatureDirectionSplit,
    gravityBFCurvatureIncrementDensity_add]
  simp only [residualLimitRelativeOriginReader_coframe,
    residualLimitRelativeOriginReader_gravityAuxiliary,
    residualLimitArbitraryOriginReader_coframe,
    residualLimitArbitraryOriginReader_gravityAuxiliary]
  ring

set_option maxRecDepth 100000 in
theorem residualLimitOriginAlgebraicResponse_add
    (first second : LorentzBivectorOneForm) :
    residualLimitOriginAlgebraicResponse (first + second) =
      residualLimitOriginAlgebraicResponse first +
        residualLimitOriginAlgebraicResponse second := by
  funext direction
  unfold residualLimitOriginAlgebraicResponse
    lorentzGravityBFAlgebraicCoefficient
  simp only [Pi.add_apply]
  have volumeFirst :
      generatedVolumeDensity
          (toContinuumPointField
            (residualLimitArbitraryOriginReader first) 0) =
        generatedVolumeDensity
          (toContinuumPointField residualLimitLorentzCarrierReader 0) := by
    unfold generatedVolumeDensity toContinuumPointField
    rfl
  have volumeSecond :
      generatedVolumeDensity
          (toContinuumPointField
            (residualLimitArbitraryOriginReader second) 0) =
        generatedVolumeDensity
          (toContinuumPointField residualLimitLorentzCarrierReader 0) := by
    unfold generatedVolumeDensity toContinuumPointField
    rfl
  have volumeAdd :
      generatedVolumeDensity
          (toContinuumPointField
            (residualLimitArbitraryOriginReader (first + second)) 0) =
        generatedVolumeDensity
          (toContinuumPointField residualLimitLorentzCarrierReader 0) := by
    unfold generatedVolumeDensity toContinuumPointField
    rfl
  rw [volumeFirst, volumeSecond, volumeAdd]
  have directionAdd :
      lorentzConnectionAlgebraicCurvatureDirection
          (residualLimitArbitraryOriginReader (first + second)) direction 0 =
        lorentzConnectionAlgebraicCurvatureDirection
            (residualLimitArbitraryOriginReader first) direction 0 +
          lorentzConnectionAlgebraicCurvatureDirection
            (residualLimitArbitraryOriginReader second) direction 0 := by
    funext internalPair spacetimePair
    unfold lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    dsimp only
    rw [residualLimitArbitraryOriginReader_gravityConnection_origin,
      residualLimitArbitraryOriginReader_gravityConnection_origin,
      residualLimitArbitraryOriginReader_gravityConnection_origin,
      lorentzSkewConnectionOfBivectorOneForm_add]
    simp only [Pi.add_apply]
    rw [← mul_add, ← Finset.sum_add_distrib]
    apply congrArg
    apply Finset.sum_congr rfl
    intro middle _
    ring
  rw [directionAdd, gravityBFCurvatureIncrementDensity_add]
  simp only [residualLimitArbitraryOriginReader_coframe,
    residualLimitArbitraryOriginReader_gravityAuxiliary]
  ring

set_option maxRecDepth 100000 in
theorem residualLimitOriginAlgebraicResponse_smul
    (scalar : ℝ) (q : LorentzBivectorOneForm) :
    residualLimitOriginAlgebraicResponse (scalar • q) =
      scalar • residualLimitOriginAlgebraicResponse q := by
  funext direction
  unfold residualLimitOriginAlgebraicResponse
    lorentzGravityBFAlgebraicCoefficient
  simp only [Pi.smul_apply, smul_eq_mul]
  have volumeScaled :
      generatedVolumeDensity
          (toContinuumPointField
            (residualLimitArbitraryOriginReader (scalar • q)) 0) =
        generatedVolumeDensity
          (toContinuumPointField residualLimitLorentzCarrierReader 0) := by
    unfold generatedVolumeDensity toContinuumPointField
    rfl
  have volumeReference :
      generatedVolumeDensity
          (toContinuumPointField
            (residualLimitArbitraryOriginReader q) 0) =
        generatedVolumeDensity
          (toContinuumPointField residualLimitLorentzCarrierReader 0) := by
    unfold generatedVolumeDensity toContinuumPointField
    rfl
  rw [volumeScaled, volumeReference]
  have directionScaled :
      lorentzConnectionAlgebraicCurvatureDirection
          (residualLimitArbitraryOriginReader (scalar • q)) direction 0 =
        scalar • lorentzConnectionAlgebraicCurvatureDirection
          (residualLimitArbitraryOriginReader q) direction 0 := by
    funext internalPair spacetimePair
    unfold lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    dsimp only
    rw [residualLimitArbitraryOriginReader_gravityConnection_origin,
      residualLimitArbitraryOriginReader_gravityConnection_origin,
      lorentzSkewConnectionOfBivectorOneForm_smul]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro middle _
    ring
  rw [directionScaled, gravityBFCurvatureIncrementDensity_smul]
  simp only [residualLimitArbitraryOriginReader_coframe,
    residualLimitArbitraryOriginReader_gravityAuxiliary]
  ring

/-- Linear-map packaging of the actual complete displacement operator. -/
def residualLimitOriginResponseDisplacementLinearMap :
    LorentzBivectorOneForm →ₗ[ℝ] RestrictedLorentzResponse where
  toFun := residualLimitOriginResponseDisplacement
  map_add' := by
    intro first second
    rw [residualLimitOriginResponseDisplacement_eq_absoluteResponse,
      residualLimitOriginResponseDisplacement_eq_absoluteResponse,
      residualLimitOriginResponseDisplacement_eq_absoluteResponse,
      residualLimitOriginAlgebraicResponse_add]
  map_smul' := by
    intro scalar q
    simpa only [residualLimitOriginResponseDisplacement_eq_absoluteResponse,
      RingHom.id_apply] using
        residualLimitOriginAlgebraicResponse_smul scalar q

@[simp] theorem residualLimitOriginResponseDisplacementLinearMap_apply
    (q : LorentzBivectorOneForm) :
    residualLimitOriginResponseDisplacementLinearMap q =
      residualLimitOriginResponseDisplacement q :=
  rfl

/-- C3h31's actual basis matrix and coordinate bijection make the complete
absolute response injective; equality on all response directions fixes the
origin coordinate. -/
theorem residualLimitOriginAlgebraicResponse_injective :
    Function.Injective residualLimitOriginAlgebraicResponse := by
  intro first second responseEquality
  apply residualLimitOriginAlgebraicResponseCoordinates_bijective.1
  funext formDirection internalPair
  rw [← residualLimitOriginAlgebraicResponse_basis
      first formDirection internalPair,
    ← residualLimitOriginAlgebraicResponse_basis
      second formDirection internalPair]
  exact congrFun responseEquality
    (residualLimitLorentzBasisDirection formDirection internalPair)

/-- The actual relative displacement operator inherits the same injectivity.
No response responsibility is quotiented away. -/
theorem residualLimitOriginResponseDisplacement_injective :
    Function.Injective residualLimitOriginResponseDisplacement := by
  intro first second responseEquality
  apply residualLimitOriginAlgebraicResponse_injective
  rw [← residualLimitOriginResponseDisplacement_eq_absoluteResponse,
    ← residualLimitOriginResponseDisplacement_eq_absoluteResponse]
  exact responseEquality

/-! ## Derived differential preimage and framework target -/

/-- C3h31's unique absolute preimage is also the relative displacement whose
complete response is `D`. -/
theorem residualLimitReferenceDivergenceOriginPreimage_displacement :
    residualLimitOriginResponseDisplacement
        residualLimitReferenceDivergenceOriginPreimage =
      residualLimitReferenceDivergenceResponse := by
  rw [residualLimitOriginResponseDisplacement_eq_absoluteResponse]
  exact residualLimitReferenceDivergenceOriginPreimage_response

/-- Deterministic lowered coordinates of the existing source-generated origin
connection.  This is a readout of `omega_source`, not a caller parameter. -/
def residualLimitSourceOriginCoordinate : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    loweredLorentzConnectionCoefficient
      positiveSourceGravityMouthOriginConnectionValue
      formDirection internalPair

set_option maxRecDepth 100000 in
/-- The coordinate readout reconstructs the actual Lorentz-skew source origin. -/
theorem residualLimitSourceOriginCoordinate_lift :
    lorentzSkewConnectionOfBivectorOneForm
        residualLimitSourceOriginCoordinate =
      positiveSourceGravityMouthOriginConnectionValue := by
  funext formDirection internalOut internalIn
  have skewness :=
    positive_generatedLorentzConnection_lorentzSkew (0 : BasePoint)
      formDirection
  have skewEntry := congrArg
    (fun matrix : LorentzianMetric => matrix internalOut internalIn)
    skewness
  fin_cases internalOut <;> fin_cases internalIn <;>
    simp [spinConnectionMatrix, Matrix.mul_apply,
      residualLimitSourceOriginCoordinate,
      positiveSourceGravityMouthOriginConnectionValue,
      loweredLorentzConnectionCoefficient,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond, minkowskiInternalMetric,
      minkowskiInternalSign, Fin.sum_univ_four, Fin.sum_univ_six]
      at skewEntry ⊢ <;>
    linarith

/-- The source-origin coordinate produces exactly the reference algebraic
response under the C3h31 absolute response operator. -/
theorem residualLimitSourceOriginCoordinate_absoluteResponse :
    residualLimitOriginAlgebraicResponse
        residualLimitSourceOriginCoordinate =
      residualLimitReferenceAlgebraicResponse := by
  funext direction
  unfold residualLimitOriginAlgebraicResponse
    residualLimitReferenceAlgebraicResponse
    lorentzGravityBFAlgebraicCoefficient
  have readerConnection :
      (residualLimitArbitraryOriginReader
        residualLimitSourceOriginCoordinate).gravityConnection 0 =
        residualLimitLorentzCarrierReader.gravityConnection 0 := by
    rw [residualLimitArbitraryOriginReader_gravityConnection_origin,
      residualLimitSourceOriginCoordinate_lift,
      residualLimitLorentzCarrierReader_gravityConnection_origin]
  have volumeEquality :
      generatedVolumeDensity
          (toContinuumPointField
            (residualLimitArbitraryOriginReader
              residualLimitSourceOriginCoordinate) 0) =
        generatedVolumeDensity
          (toContinuumPointField residualLimitLorentzCarrierReader 0) := by
    unfold generatedVolumeDensity toContinuumPointField
    rfl
  have curvatureDirectionEquality :
      lorentzConnectionAlgebraicCurvatureDirection
          (residualLimitArbitraryOriginReader
            residualLimitSourceOriginCoordinate) direction 0 =
        lorentzConnectionAlgebraicCurvatureDirection
          residualLimitLorentzCarrierReader direction 0 := by
    funext internalPair spacetimePair
    unfold lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    dsimp only
    rw [readerConnection]
  rw [volumeEquality, curvatureDirectionEquality]
  simp only [residualLimitArbitraryOriginReader_coframe,
    residualLimitArbitraryOriginReader_gravityAuxiliary]

/-- Framework equivalence for an arbitrary member of the audited fiber.  The
required endpoint is derived from `A' = K*A + (I-K)*D`; equivalently the
actual displacement must be `-sigma*(A-D)`. -/
theorem residualLimitRelativeOrigin_algebraicTransport_iff_displacement
    (q : LorentzBivectorOneForm) :
    residualLimitRelativeOriginAlgebraicResponse q =
          (1 - positiveSmoothUnifiedSource.legacy.sigma) •
              residualLimitReferenceAlgebraicResponse +
            positiveSmoothUnifiedSource.legacy.sigma •
              residualLimitReferenceDivergenceResponse ↔
      residualLimitOriginResponseDisplacement q =
        -positiveSmoothUnifiedSource.legacy.sigma •
          (residualLimitReferenceAlgebraicResponse -
            residualLimitReferenceDivergenceResponse) := by
  constructor <;> intro equality <;> funext direction
  · have pointEquality := congrFun equality direction
    unfold residualLimitOriginResponseDisplacement
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      at pointEquality ⊢
    linarith
  · have pointEquality := congrFun equality direction
    unfold residualLimitOriginResponseDisplacement at pointEquality
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      at pointEquality ⊢
    linarith

/-- Relative coordinate canonically forced by the framework endpoint formula.
In absolute-origin coordinates this is equivalent to
`K*q_source + sigma*q_D`. -/
def residualLimitRequiredTransportRelativeOrigin : LorentzBivectorOneForm :=
  -positiveSmoothUnifiedSource.legacy.sigma •
    (residualLimitSourceOriginCoordinate -
      residualLimitReferenceDivergenceOriginPreimage)

/-- The corresponding absolute origin is the framework-forced keep/trace
combination `K*omega_source + sigma*omega_D`. -/
theorem residualLimitRequiredTransportRelativeOrigin_absolute :
    residualLimitRelativeOrigin
        residualLimitRequiredTransportRelativeOrigin =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          positiveSourceGravityMouthOriginConnectionValue +
        positiveSmoothUnifiedSource.legacy.sigma •
          lorentzSkewConnectionOfBivectorOneForm
            residualLimitReferenceDivergenceOriginPreimage := by
  have differenceLift :
      lorentzSkewConnectionOfBivectorOneForm
          (residualLimitSourceOriginCoordinate -
            residualLimitReferenceDivergenceOriginPreimage) =
        positiveSourceGravityMouthOriginConnectionValue -
          lorentzSkewConnectionOfBivectorOneForm
            residualLimitReferenceDivergenceOriginPreimage := by
    calc
      lorentzSkewConnectionOfBivectorOneForm
          (residualLimitSourceOriginCoordinate -
            residualLimitReferenceDivergenceOriginPreimage) =
          lorentzSkewConnectionOfBivectorOneForm
            (residualLimitSourceOriginCoordinate +
              (-1 : ℝ) •
                residualLimitReferenceDivergenceOriginPreimage) := by
            congr 1
            funext formDirection internalPair
            change
              residualLimitSourceOriginCoordinate formDirection internalPair -
                  residualLimitReferenceDivergenceOriginPreimage
                    formDirection internalPair =
                residualLimitSourceOriginCoordinate formDirection internalPair +
                  (-1 : ℝ) *
                    residualLimitReferenceDivergenceOriginPreimage
                      formDirection internalPair
            ring
      _ = lorentzSkewConnectionOfBivectorOneForm
            residualLimitSourceOriginCoordinate +
          lorentzSkewConnectionOfBivectorOneForm
            ((-1 : ℝ) • residualLimitReferenceDivergenceOriginPreimage) :=
        lorentzSkewConnectionOfBivectorOneForm_add _ _
      _ = positiveSourceGravityMouthOriginConnectionValue +
          (-1 : ℝ) • lorentzSkewConnectionOfBivectorOneForm
            residualLimitReferenceDivergenceOriginPreimage := by
        rw [lorentzSkewConnectionOfBivectorOneForm_smul,
          residualLimitSourceOriginCoordinate_lift]
      _ = positiveSourceGravityMouthOriginConnectionValue -
          lorentzSkewConnectionOfBivectorOneForm
            residualLimitReferenceDivergenceOriginPreimage := by
        funext formDirection internalOut internalIn
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
  unfold residualLimitRelativeOrigin
    residualLimitRequiredTransportRelativeOrigin
  rw [lorentzSkewConnectionOfBivectorOneForm_smul, differenceLift]
  funext formDirection internalOut internalIn
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The target algebraic response is derived from the first formula, not
accepted from a caller:

`A' = K*A + (I-K)*D`, with `K=1-sigma`. -/
theorem residualLimitRequiredTransportRelativeOrigin_algebraicResponse :
    residualLimitRelativeOriginAlgebraicResponse
        residualLimitRequiredTransportRelativeOrigin =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          residualLimitReferenceAlgebraicResponse +
        positiveSmoothUnifiedSource.legacy.sigma •
          residualLimitReferenceDivergenceResponse := by
  have sourceResponse :=
    residualLimitSourceOriginCoordinate_absoluteResponse
  have divergenceResponse :=
    residualLimitReferenceDivergenceOriginPreimage_response
  have displacementFormula :
      residualLimitOriginResponseDisplacement
          residualLimitRequiredTransportRelativeOrigin =
        -positiveSmoothUnifiedSource.legacy.sigma •
          (residualLimitReferenceAlgebraicResponse -
            residualLimitReferenceDivergenceResponse) := by
    change residualLimitOriginResponseDisplacementLinearMap
        (-positiveSmoothUnifiedSource.legacy.sigma •
          (residualLimitSourceOriginCoordinate -
            residualLimitReferenceDivergenceOriginPreimage)) = _
    rw [map_smul, map_sub]
    simp only [residualLimitOriginResponseDisplacementLinearMap_apply]
    rw [residualLimitOriginResponseDisplacement_eq_absoluteResponse,
      residualLimitOriginResponseDisplacement_eq_absoluteResponse]
    rw [sourceResponse, divergenceResponse]
  have actualEq :
      residualLimitRelativeOriginAlgebraicResponse
          residualLimitRequiredTransportRelativeOrigin =
        residualLimitReferenceAlgebraicResponse +
          residualLimitOriginResponseDisplacement
            residualLimitRequiredTransportRelativeOrigin := by
    funext direction
    unfold residualLimitOriginResponseDisplacement
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [actualEq, displacementFormula]
  funext direction
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- No-free-parameter hard gate: any relative-origin coordinate satisfying
the actual framework-derived algebraic endpoint equation is the canonical
`q*`.  The premise is the real response equation, not a supplied zero,
endpoint witness, branch receipt, or stationarity certificate. -/
theorem residualLimitRequiredTransportRelativeOrigin_unique
    (q : LorentzBivectorOneForm)
    (actualEndpoint :
      residualLimitRelativeOriginAlgebraicResponse q =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
            residualLimitReferenceAlgebraicResponse +
          positiveSmoothUnifiedSource.legacy.sigma •
            residualLimitReferenceDivergenceResponse) :
    q = residualLimitRequiredTransportRelativeOrigin := by
  apply residualLimitOriginResponseDisplacement_injective
  have qDisplacement :=
    (residualLimitRelativeOrigin_algebraicTransport_iff_displacement q).mp
      actualEndpoint
  have requiredDisplacement :=
    (residualLimitRelativeOrigin_algebraicTransport_iff_displacement
      residualLimitRequiredTransportRelativeOrigin).mp
        residualLimitRequiredTransportRelativeOrigin_algebraicResponse
  exact qDisplacement.trans requiredDisplacement.symm

/-- Actual residual transport follows after subtracting the frozen `D`.
This is exactly `r'=Kr` for `r=A-D`. -/
theorem residualLimitRequiredTransportRelativeOrigin_balance :
    residualLimitRelativeOriginAlgebraicResponse
          residualLimitRequiredTransportRelativeOrigin -
        residualLimitRelativeOriginDivergenceResponse
          residualLimitRequiredTransportRelativeOrigin =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        positiveResidualLimitLorentzBalance := by
  rw [residualLimitRequiredTransportRelativeOrigin_algebraicResponse,
    residualLimitRelativeOriginDivergenceResponse_eq_reference,
    positiveResidualLimitLorentzBalance_eq_referenceDifference]
  funext direction
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Parameter-free produced endpoint reader -/

/-- The existing normalized-affine field reader at the uniquely forced
relative origin.  It accepts no caller parameter, endpoint witness, zero
premise, branch receipt, or stationarity certificate. -/
def residualLimitRequiredTransportReader :
    StageNineHolonomicConfiguration :=
  residualLimitRelativeOriginReader
    residualLimitRequiredTransportRelativeOrigin

theorem residualLimitRequiredTransportReader_curvature_origin :
    holonomicGravityCurvature residualLimitRequiredTransportReader 0 =
      positiveSourceGravityMouthResidualLimitCurvature :=
  residualLimitRelativeOriginReader_curvature_origin _

theorem residualLimitRequiredTransportReader_algebraicResidual_zero :
    currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        residualLimitRequiredTransportReader 0 = 0 :=
  residualLimitRelativeOriginReader_algebraicResidual_zero _

/-- Reader-level form of the first formula on the complete Lorentz
gravity--BF balance function. -/
theorem residualLimitRequiredTransportReader_gravityBFBalance :
    (fun direction =>
      lorentzGravityBFBalanceCoefficient
        residualLimitRequiredTransportReader direction 0) =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        positiveResidualLimitLorentzBalance := by
  funext direction
  have balanceAt := congrFun
    residualLimitRequiredTransportRelativeOrigin_balance direction
  change
    lorentzGravityBFAlgebraicCoefficient
          (residualLimitRelativeOriginReader
            residualLimitRequiredTransportRelativeOrigin) direction 0 -
        lorentzConnectionBFDifferentialMomentumDivergence
          (residualLimitRelativeOriginReader
            residualLimitRequiredTransportRelativeOrigin) direction 0 =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) *
        positiveResidualLimitLorentzBalance direction
    at balanceAt
  simpa [residualLimitRequiredTransportReader,
    lorentzGravityBFBalanceCoefficient] using balanceAt

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzSourceTransport
