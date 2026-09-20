import H0mework.Physics.Lorentz.ResidualLimitLorentzSourceTransport

/-!
# Scratch: local compatibility audit of the produced Lorentz endpoint

This diagnostic consumes the parameter-free C3h32 reader.  It checks the
actual normalized-affine field for smoothness, Lorentz skewness, origin
curvature, and the off-shell gravity Bianchi identity.  It then evaluates the
origin tetrad postulate and coframe torsion without accepting either as a
premise.

Any negative result below is restricted to this produced reader.  It is not a
no-go for the full Stage-9 shell or for other existing connection fibers.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzSourceTransportLocalCompatibilityAudit

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitLorentzOriginResponsePreimage
open StageNineResidualLimitLorentzSourceTransport
open StageNineResidualLimitSameCurvatureLorentzTransport
open PointwiseDiracSpinConnectionLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Smooth and Lorentz-admissible normalized-affine field -/

theorem residualLimitRequiredTransportReader_gravityConnection_smooth :
    SmoothLorentzConnectionField
      residualLimitRequiredTransportReader.gravityConnection := by
  change SmoothLorentzConnectionField
    (normalizedAffineLorentzConnectionField
      (residualLimitRelativeOrigin
        residualLimitRequiredTransportRelativeOrigin)
      positiveSourceGravityMouthResidualLimitCurvature)
  exact normalizedAffineLorentzConnectionField_smooth _ _

theorem residualLimitRelativeOrigin_lorentzSkew
    (q : LorentzBivectorOneForm) :
    LorentzSkew (residualLimitRelativeOrigin q) := by
  intro formDirection
  have sourceSkew : LorentzSkew
      positiveSourceGravityMouthOriginConnectionValue := by
    change LorentzSkew
      (generatedLorentzConnectionAt positiveSmoothUnifiedSource 0)
    exact positive_generatedLorentzConnection_lorentzSkew (0 : BasePoint)
  have displacementSkew :=
    lorentzSkewConnectionOfBivectorOneForm_lorentzSkew q formDirection
  rw [show spinConnectionMatrix (residualLimitRelativeOrigin q) formDirection =
      spinConnectionMatrix positiveSourceGravityMouthOriginConnectionValue
          formDirection +
        spinConnectionMatrix
          (lorentzSkewConnectionOfBivectorOneForm q) formDirection by
    ext internalOut internalIn
    rfl]
  rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  calc
    (Matrix.transpose
          (spinConnectionMatrix positiveSourceGravityMouthOriginConnectionValue
            formDirection) * minkowskiInternalMetric +
        Matrix.transpose
            (spinConnectionMatrix
              (lorentzSkewConnectionOfBivectorOneForm q) formDirection) *
          minkowskiInternalMetric) +
      (minkowskiInternalMetric *
          spinConnectionMatrix positiveSourceGravityMouthOriginConnectionValue
            formDirection +
        minkowskiInternalMetric *
          spinConnectionMatrix
            (lorentzSkewConnectionOfBivectorOneForm q) formDirection) =
        (Matrix.transpose
            (spinConnectionMatrix positiveSourceGravityMouthOriginConnectionValue
              formDirection) * minkowskiInternalMetric +
          minkowskiInternalMetric *
            spinConnectionMatrix positiveSourceGravityMouthOriginConnectionValue
              formDirection) +
        (Matrix.transpose
            (spinConnectionMatrix
              (lorentzSkewConnectionOfBivectorOneForm q) formDirection) *
              minkowskiInternalMetric +
          minkowskiInternalMetric *
            spinConnectionMatrix
              (lorentzSkewConnectionOfBivectorOneForm q) formDirection) := by
      abel
    _ = 0 := by
      rw [sourceSkew formDirection, displacementSkew, add_zero]

theorem residualLimitRequiredTransportReader_gravityConnection_lorentzSkew
    (point : BasePoint) :
    LorentzSkew
      (residualLimitRequiredTransportReader.gravityConnection point) := by
  change LorentzSkew
    (normalizedAffineLorentzConnectionField
      (residualLimitRelativeOrigin
        residualLimitRequiredTransportRelativeOrigin)
      positiveSourceGravityMouthResidualLimitCurvature point)
  exact normalizedAffineLorentzConnectionField_lorentzSkew _ _
    (residualLimitRelativeOrigin_lorentzSkew _) point

/-- The generic off-shell Bianchi theorem asks for a smooth full carrier even
though its conclusion consumes only the primitive gravity connection.  This
zero-filled diagnostic carrier supplies no shell data and keeps exactly the
produced connection. -/
theorem configurationOfLorentzConnection_smooth_of_connection_smooth
    (connection : LorentzConnectionField)
    (smooth : SmoothLorentzConnectionField connection) :
    (configurationOfLorentzConnection connection).Smooth := by
  refine ⟨?_, smooth, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row column
    simp [configurationOfLorentzConnection]
    fun_prop
  · intro internalPair spacetimePair
    simp [configurationOfLorentzConnection]
    fun_prop
  · intro internalPair spacetimePair
    simp [configurationOfLorentzConnection]
    fun_prop
  · intro direction
    simp [configurationOfLorentzConnection]
    fun_prop
  · intro pair
    simp [configurationOfLorentzConnection]
    fun_prop
  · simp [configurationOfLorentzConnection]
    exact contDiff_const
  · simp [configurationOfLorentzConnection]
    fun_prop
  · intro index
    simp [configurationOfLorentzConnection]
    fun_prop

/-- Actual off-shell differential Bianchi identity for the C3h32-produced
primitive gravity connection.  No tetrad compatibility or shell receipt is
used: this is the existing generic connection identity. -/
theorem residualLimitRequiredTransportReader_gravity_bianchi
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantMixedCurvatureDerivative residualLimitRequiredTransportReader
          point first second third +
        covariantMixedCurvatureDerivative residualLimitRequiredTransportReader
          point second third first +
        covariantMixedCurvatureDerivative residualLimitRequiredTransportReader
          point third first second = 0 := by
  have smoothDiagnostic :
      (configurationOfLorentzConnection
        residualLimitRequiredTransportReader.gravityConnection).Smooth :=
    configurationOfLorentzConnection_smooth_of_connection_smooth _
      residualLimitRequiredTransportReader_gravityConnection_smooth
  change
    covariantMixedCurvatureDerivative
          (configurationOfLorentzConnection
            residualLimitRequiredTransportReader.gravityConnection)
          point first second third +
        covariantMixedCurvatureDerivative
          (configurationOfLorentzConnection
            residualLimitRequiredTransportReader.gravityConnection)
          point second third first +
        covariantMixedCurvatureDerivative
          (configurationOfLorentzConnection
            residualLimitRequiredTransportReader.gravityConnection)
          point third first second = 0
  exact holonomicGravityGL4Curvature_bianchi _ smoothDiagnostic point
    first second third

theorem residualLimitRequiredTransportReader_curvature_origin_actual :
    holonomicGravityCurvature residualLimitRequiredTransportReader 0 =
      positiveSourceGravityMouthResidualLimitCurvature :=
  residualLimitRequiredTransportReader_curvature_origin

/-! ## Origin tetrad-postulate and torsion readouts -/

/-- Actual tetrad-postulate residual after retaining the source coframe jet
and Levi-Civita affine connection and replacing only the origin spin
connection. -/
def sourceJetTetradResidualForConnection
    (connection : PointwiseLorentzSpinConnection)
    (derivativeDirection internal coordinate : LorentzianIndex) : ℝ :=
  let jet := canonicalPhysicalSource.jetAt 0
  jet.derivative derivativeDirection internal coordinate -
      ∑ upper, jet.leviCivitaConnection upper derivativeDirection coordinate *
        jet.coframe internal upper +
    ∑ internalIn,
      connection derivativeDirection internal internalIn *
        jet.coframe internalIn coordinate

/-- At the identity source coframe, changing only the spin connection changes
the tetrad residual by exactly the corresponding origin-connection entry. -/
theorem sourceJetTetradResidualForConnection_eq_difference
    (connection : PointwiseLorentzSpinConnection)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    sourceJetTetradResidualForConnection connection derivativeDirection
        internal coordinate =
      connection derivativeDirection internal coordinate -
        positiveSourceGravityMouthOriginConnectionValue derivativeDirection
          internal coordinate := by
  have sourceCompatible :=
    positive_generatedLorentzConnection_tetradCompatible (0 : BasePoint)
      derivativeDirection internal coordinate
  simp only [sourceJetTetradResidualForConnection]
  rw [canonicalPhysicalSource.jetAt_zero_coframe]
  simp [Matrix.one_apply]
  rw [canonicalPhysicalSource.jetAt_zero_coframe] at sourceCompatible
  simp [Matrix.one_apply] at sourceCompatible
  change
    (canonicalPhysicalSource.jetAt 0).derivative derivativeDirection internal
          coordinate -
        (canonicalPhysicalSource.jetAt 0).leviCivitaConnection internal
          derivativeDirection coordinate +
        positiveSourceGravityMouthOriginConnectionValue derivativeDirection
          internal coordinate = 0
    at sourceCompatible
  linarith

/-- Actual tetrad-postulate residual for the produced C3h32 transport
endpoint. -/
def residualLimitRequiredTransportTetradResidual
    (derivativeDirection internal coordinate : LorentzianIndex) : ℝ :=
  sourceJetTetradResidualForConnection
    (residualLimitRequiredTransportReader.gravityConnection 0)
    derivativeDirection internal coordinate

/-- Cartan coframe torsion is the antisymmetrized tetrad residual.  The
source affine connection is Levi-Civita and hence torsion-free, so this is the
actual torsion created by changing only the spin connection. -/
def residualLimitRequiredTransportCoframeTorsion
    (internal first second : LorentzianIndex) : ℝ :=
  residualLimitRequiredTransportTetradResidual first internal second -
  residualLimitRequiredTransportTetradResidual second internal first

theorem residualLimitReferenceDivergenceOriginPreimage_lift_one_zero_two :
    lorentzSkewConnectionOfBivectorOneForm
        residualLimitReferenceDivergenceOriginPreimage 1 0 2 =
      -(1 / 2 : ℝ) := by
  have coordinate := loweredLorentzConnectionCoefficient_ofBivectorOneForm
    residualLimitReferenceDivergenceOriginPreimage (1 : LorentzianIndex)
      (1 : Fin 6)
  simp [loweredLorentzConnectionCoefficient, lorentzBivectorFirst,
    lorentzBivectorSecond] at coordinate
  rw [show residualLimitReferenceDivergenceOriginPreimage 1 1 =
      (1 / 2 : ℝ) by rfl] at coordinate
  linarith

theorem residualLimitReferenceDivergenceOriginPreimage_lift_two_zero_one :
    lorentzSkewConnectionOfBivectorOneForm
        residualLimitReferenceDivergenceOriginPreimage 2 0 1 =
      (1 / 2 : ℝ) := by
  have coordinate := loweredLorentzConnectionCoefficient_ofBivectorOneForm
    residualLimitReferenceDivergenceOriginPreimage (2 : LorentzianIndex)
      (0 : Fin 6)
  simp [loweredLorentzConnectionCoefficient, lorentzBivectorFirst,
    lorentzBivectorSecond] at coordinate
  rw [show residualLimitReferenceDivergenceOriginPreimage 2 0 =
      -(1 / 2 : ℝ) by rfl] at coordinate
  linarith

theorem positiveSourceGravityMouthOriginConnectionValue_two_zero_one :
    positiveSourceGravityMouthOriginConnectionValue 2 0 1 =
      -(1 / 2 : ℝ) := by
  norm_num [positiveSourceGravityMouthOriginConnectionValue,
    generatedLorentzConnectionAt,
    PointwiseLorentzianCoframeJet.lorentzSpinConnection,
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix,
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix,
    affineConnectionMatrix,
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix,
    PointwiseLorentzianCoframeJet.leviCivitaConnection,
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaVector,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection,
    PointwiseLorentzianCoframeJet.metricDerivative,
    PointwiseLorentzianCoframeJet.metric,
    StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ProofFreeRicherAnholonomicSource.Source.jetAt,
    StageNineEnrichedProofFreeSource.SmoothUnifiedSource.legacy,
    StageNineEnrichedProofFreeSource.SmoothUnifiedSource.forget,
    StageEightProofFreeSource.Source.toPhysicalSource,
    StageEightProofFreeSource.canonicalPhysicalSource,
    StageEightProofFreeSource.canonicalSource,
    ProofFreeRicherAnholonomicSource.shearCoefficient,
    residualLimit_identityCoframeMetric_inv,
    residualLimit_minkowskiInternalMetric_inv,
    minkowskiInternalMetric, minkowskiInternalSign, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, Matrix.diagonal_apply];
  simp;
  norm_num

theorem residualLimitRequiredTransportReader_connection_origin_one_zero_two :
    residualLimitRequiredTransportReader.gravityConnection 0 1 0 2 = 0 := by
  rw [show residualLimitRequiredTransportReader.gravityConnection 0 =
      residualLimitRelativeOrigin
        residualLimitRequiredTransportRelativeOrigin by
    exact residualLimitRelativeOriginReader_gravityConnection_origin _]
  rw [residualLimitRequiredTransportRelativeOrigin_absolute]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half,
    residualLimit_originConnection_algebraic_support.2]
  rw [residualLimitReferenceDivergenceOriginPreimage_lift_one_zero_two]
  norm_num

theorem residualLimitRequiredTransportReader_connection_origin_two_zero_one :
    residualLimitRequiredTransportReader.gravityConnection 0 2 0 1 = 0 := by
  rw [show residualLimitRequiredTransportReader.gravityConnection 0 =
      residualLimitRelativeOrigin
        residualLimitRequiredTransportRelativeOrigin by
    exact residualLimitRelativeOriginReader_gravityConnection_origin _]
  rw [residualLimitRequiredTransportRelativeOrigin_absolute]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half,
    positiveSourceGravityMouthOriginConnectionValue_two_zero_one,
    residualLimitReferenceDivergenceOriginPreimage_lift_two_zero_one]
  norm_num

theorem residualLimitRequiredTransportTetradResidual_one_zero_two :
    residualLimitRequiredTransportTetradResidual 1 0 2 = -(1 / 2 : ℝ) := by
  rw [residualLimitRequiredTransportTetradResidual,
    sourceJetTetradResidualForConnection_eq_difference,
    residualLimitRequiredTransportReader_connection_origin_one_zero_two,
    residualLimit_originConnection_algebraic_support.2]
  norm_num

theorem residualLimitRequiredTransportTetradResidual_two_zero_one :
    residualLimitRequiredTransportTetradResidual 2 0 1 = (1 / 2 : ℝ) := by
  rw [residualLimitRequiredTransportTetradResidual,
    sourceJetTetradResidualForConnection_eq_difference,
    residualLimitRequiredTransportReader_connection_origin_two_zero_one,
    positiveSourceGravityMouthOriginConnectionValue_two_zero_one]
  norm_num

theorem residualLimitRequiredTransportCoframeTorsion_zero_one_two :
    residualLimitRequiredTransportCoframeTorsion 0 1 2 = -1 := by
  rw [residualLimitRequiredTransportCoframeTorsion,
    residualLimitRequiredTransportTetradResidual_one_zero_two,
    residualLimitRequiredTransportTetradResidual_two_zero_one]
  norm_num

theorem residualLimitRequiredTransportReader_not_tetradCompatible :
    ¬ TetradCompatible (canonicalPhysicalSource.jetAt 0)
      (canonicalPhysicalSource.jetAt 0).leviCivitaConnection
      (residualLimitRequiredTransportReader.gravityConnection 0) := by
  intro compatibility
  have zeroCoordinate := compatibility
    (1 : LorentzianIndex) (0 : LorentzianIndex) (2 : LorentzianIndex)
  change residualLimitRequiredTransportTetradResidual 1 0 2 = 0
    at zeroCoordinate
  rw [residualLimitRequiredTransportTetradResidual_one_zero_two]
    at zeroCoordinate
  norm_num at zeroCoordinate

/-! ## Independent audit of C3h31's absolute zero-balance reader -/

/-- C3h31's absolute `q_D` reader is not the C3h32 intermediate endpoint and
must be tested independently. -/
def residualLimitAbsoluteZeroBalanceTetradResidual
    (derivativeDirection internal coordinate : LorentzianIndex) : ℝ :=
  sourceJetTetradResidualForConnection
    ((residualLimitArbitraryOriginReader
      residualLimitReferenceDivergenceOriginPreimage).gravityConnection 0)
    derivativeDirection internal coordinate

def residualLimitAbsoluteZeroBalanceCoframeTorsion
    (internal first second : LorentzianIndex) : ℝ :=
  residualLimitAbsoluteZeroBalanceTetradResidual first internal second -
    residualLimitAbsoluteZeroBalanceTetradResidual second internal first

theorem residualLimitAbsoluteZeroBalanceReader_connection_one_zero_two :
    (residualLimitArbitraryOriginReader
        residualLimitReferenceDivergenceOriginPreimage).gravityConnection
        0 1 0 2 = -(1 / 2 : ℝ) := by
  rw [residualLimitArbitraryOriginReader_gravityConnection_origin]
  exact residualLimitReferenceDivergenceOriginPreimage_lift_one_zero_two

theorem residualLimitAbsoluteZeroBalanceReader_connection_two_zero_one :
    (residualLimitArbitraryOriginReader
        residualLimitReferenceDivergenceOriginPreimage).gravityConnection
        0 2 0 1 = (1 / 2 : ℝ) := by
  rw [residualLimitArbitraryOriginReader_gravityConnection_origin]
  exact residualLimitReferenceDivergenceOriginPreimage_lift_two_zero_one

theorem residualLimitAbsoluteZeroBalanceTetradResidual_one_zero_two :
    residualLimitAbsoluteZeroBalanceTetradResidual 1 0 2 = -1 := by
  rw [residualLimitAbsoluteZeroBalanceTetradResidual,
    sourceJetTetradResidualForConnection_eq_difference,
    residualLimitAbsoluteZeroBalanceReader_connection_one_zero_two,
    residualLimit_originConnection_algebraic_support.2]
  norm_num

theorem residualLimitAbsoluteZeroBalanceTetradResidual_two_zero_one :
    residualLimitAbsoluteZeroBalanceTetradResidual 2 0 1 = 1 := by
  rw [residualLimitAbsoluteZeroBalanceTetradResidual,
    sourceJetTetradResidualForConnection_eq_difference,
    residualLimitAbsoluteZeroBalanceReader_connection_two_zero_one,
    positiveSourceGravityMouthOriginConnectionValue_two_zero_one]
  norm_num

theorem residualLimitAbsoluteZeroBalanceCoframeTorsion_zero_one_two :
    residualLimitAbsoluteZeroBalanceCoframeTorsion 0 1 2 = -2 := by
  rw [residualLimitAbsoluteZeroBalanceCoframeTorsion,
    residualLimitAbsoluteZeroBalanceTetradResidual_one_zero_two,
    residualLimitAbsoluteZeroBalanceTetradResidual_two_zero_one]
  norm_num

theorem residualLimitAbsoluteZeroBalanceReader_not_tetradCompatible :
    ¬ TetradCompatible (canonicalPhysicalSource.jetAt 0)
      (canonicalPhysicalSource.jetAt 0).leviCivitaConnection
      ((residualLimitArbitraryOriginReader
        residualLimitReferenceDivergenceOriginPreimage).gravityConnection 0) := by
  intro compatibility
  have zeroCoordinate := compatibility
    (1 : LorentzianIndex) (0 : LorentzianIndex) (2 : LorentzianIndex)
  change residualLimitAbsoluteZeroBalanceTetradResidual 1 0 2 = 0
    at zeroCoordinate
  rw [residualLimitAbsoluteZeroBalanceTetradResidual_one_zero_two]
    at zeroCoordinate
  norm_num at zeroCoordinate

/-! ## Stable no-go for the declared same-curvature origin class -/

/-- There is no lowered Lorentz-origin coordinate in the existing
normalized-affine same-curvature reader class whose actual algebraic response
is the differential response `D` and whose origin spin connection is
compatible with the retained source tetrad jet.

The negative existential is deliberately closed: no caller supplies a
solution, zero-fiber receipt, selected witness, or compatibility certificate.
C3h31's actual response injectivity forces any candidate to be `q_D`; the
explicit `T⁰₁₂ = -2` readout then rejects compatibility.  This theorem says
nothing about readers outside `residualLimitArbitraryOriginReader`. -/
theorem residualLimitArbitraryOriginSameCurvature_responseD_tetradCompatible_noGo :
    ¬ ∃ q : LorentzBivectorOneForm,
      residualLimitOriginAlgebraicResponse q =
          residualLimitReferenceDivergenceResponse ∧
        TetradCompatible (canonicalPhysicalSource.jetAt 0)
          (canonicalPhysicalSource.jetAt 0).leviCivitaConnection
          ((residualLimitArbitraryOriginReader q).gravityConnection 0) := by
  rintro ⟨q, response, compatibility⟩
  have coordinateForced :
      q = residualLimitReferenceDivergenceOriginPreimage :=
    residualLimitReferenceDivergenceOriginPreimage_unique q response
  subst q
  have firstZero := compatibility
    (1 : LorentzianIndex) (0 : LorentzianIndex) (2 : LorentzianIndex)
  have secondZero := compatibility
    (2 : LorentzianIndex) (0 : LorentzianIndex) (1 : LorentzianIndex)
  change residualLimitAbsoluteZeroBalanceTetradResidual 1 0 2 = 0
    at firstZero
  change residualLimitAbsoluteZeroBalanceTetradResidual 2 0 1 = 0
    at secondZero
  have torsionZero :
      residualLimitAbsoluteZeroBalanceCoframeTorsion 0 1 2 = 0 := by
    rw [residualLimitAbsoluteZeroBalanceCoframeTorsion]
    linarith
  rw [residualLimitAbsoluteZeroBalanceCoframeTorsion_zero_one_two]
    at torsionZero
  norm_num at torsionZero

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzSourceTransportLocalCompatibilityAudit
