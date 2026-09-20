import H0mework.Physics.Admission.ResidualLimitDifferentialChannelNormalForm
import H0mework.Physics.Matter.ResidualLimitMatterOrbitJointClassification

/-!
# S9-C3h27: residual-limit Lorentz class obstruction

This module computes one actual Lorentz gravity--BF response coordinate on the
source-generated residual-limit six-field carrier.  The value is `1`.  The
readout depends only on the coframe, gravity connection, and gravity auxiliary
fields, so the same value holds for every full configuration satisfying
`ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier`; the arbitrary
multiplier, matter, and conjugate-matter completion fields are not used to
obtain it.

When both endpoints also realize consecutive source matter first jets, the
matter spin term vanishes.  Hence any actual update satisfying
`update initial = terminal` has, on this Lorentz coordinate,

`D_U = 1 - (1 - sigma) * 1 = sigma != 0`.

This is a class-specific obstruction for endpoints in the frozen six-field
residual-limit carrier plus the declared matter orbit.  It is not a no-go for
the whole Stage-9 joint shell, does not show that every proof-free source class
is unreachable, and does not authorize a quotient, repair carrier, new field,
free parameter, zero-fiber premise, or stationarity receipt.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzClassObstruction

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionActionVariation
open StageNineLorentzConnectionVariation
open StageNineConnectionSectorSourceBalance
open StageNineJointShellResidualCarrier
open StageNineJointStateLiftDefect
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNineResidualLimitDifferentialChannelNormalForm
open StageNineResidualLimitMatterOrbitJointClassification
open StageNineSourceGeneratedPartialPrimitiveCarrier
open StageNineSourceMatterFirstJetResidualOrbit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Actual residual-limit gravity--BF coordinate -/

/-- A complete reader of the actual residual-limit six-field carrier.  The
three zero completion fields lie outside the gravity--BF balance readout. -/
def residualLimitLorentzCarrierReader : StageNineHolonomicConfiguration where
  coframe := positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.coframe
  gravityConnection :=
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.gravityConnection
  gravityAuxiliary :=
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.gravityAuxiliary
  gravitySimplicityMultiplier := 0
  gaugeConnection :=
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.gaugeConnection
  gaugeAuxiliary :=
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.gaugeAuxiliary
  scalar := positiveSourceResidualLimitStageNinePartialPrimitiveCarrier.scalar
  matter := 0
  conjugateMatter := 0

theorem residualLimitLorentzCarrierReader_extends :
    ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier
      residualLimitLorentzCarrierReader := by
  constructor <;> rfl

/-- The tested coordinate direction in the actual Lorentz one-form variation
carrier. -/
def residualLimitLorentzBasisDirection
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    LorentzBivectorOneForm :=
  fun candidateForm candidatePair =>
    if candidateForm = formDirection ∧ candidatePair = internalPair then 1
    else 0

theorem residualLimit_minkowskiInternalMetric_inv :
    minkowskiInternalMetric⁻¹ = minkowskiInternalMetric := by
  apply Matrix.inv_eq_left_inv
  rw [minkowskiInternalMetric, Matrix.diagonal_mul_diagonal]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num

theorem residualLimit_identityCoframeMetric_inv :
    (lorentzianMetricOfCoframe (1 : LorentzianCoframe))⁻¹ =
      minkowskiInternalMetric := by
  rw [show lorentzianMetricOfCoframe (1 : LorentzianCoframe) =
      minkowskiInternalMetric by
    simp [lorentzianMetricOfCoframe]]
  exact residualLimit_minkowskiInternalMetric_inv

theorem residualLimit_originConnection_algebraic_support :
    positiveSourceGravityMouthOriginConnectionValue 0 1 2 =
        -(1 / 2 : ℝ) ∧
      positiveSourceGravityMouthOriginConnectionValue 1 0 2 =
        (1 / 2 : ℝ) := by
  constructor <;>
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
      dotProduct, Fin.sum_univ_succ, Matrix.diagonal_apply] <;>
    simp <;> norm_num

@[simp] theorem residualLimitLorentzCarrierReader_coframe
    (point : BasePoint) :
    residualLimitLorentzCarrierReader.coframe point =
      canonicalPhysicalSource.coframeAt point := by
  rfl

@[simp] theorem residualLimitLorentzCarrierReader_gravityAuxiliary
    (point : BasePoint) :
    residualLimitLorentzCarrierReader.gravityAuxiliary point =
      physicalIIPlusBivector (canonicalPhysicalSource.coframeAt point) := by
  rfl

@[simp] theorem residualLimitLorentzCarrierReader_gravityConnection_origin :
    residualLimitLorentzCarrierReader.gravityConnection 0 =
      positiveSourceGravityMouthOriginConnectionValue := by
  exact positiveSourceGravityMouthResidualLimitConnectionField_origin

theorem residualLimitLorentzCarrierReader_algebraic_basis_two_zero_eq_one :
    lorentzGravityBFAlgebraicCoefficient residualLimitLorentzCarrierReader
      (residualLimitLorentzBasisDirection 2 0) 0 = 1 := by
  unfold lorentzGravityBFAlgebraicCoefficient
  simp only [toContinuumPointField,
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
  rw [residualLimitLorentzCarrierReader_gravityConnection_origin]
  simp [physicalIIPlusBivector, internalBivectorDual, coframeWedge,
    coframeTwoFormLinear, residualLimitLorentzBasisDirection,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    lorentzianCoframeHodge, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond,
    Matrix.one_apply, Fin.sum_univ_six]
  rw [residualLimit_originConnection_algebraic_support.1,
    residualLimit_originConnection_algebraic_support.2]
  norm_num

theorem residualLimitLorentzCarrierReader_differentialMomentum_basis_two_zero
    (derivativeDirection : LorentzianIndex) (point : BasePoint) :
    lorentzConnectionBFDifferentialMomentum
      residualLimitLorentzCarrierReader
      (lorentzConnectionExteriorDerivativeDirection derivativeDirection
        (residualLimitLorentzBasisDirection 2 0)) point = 0 := by
  unfold lorentzConnectionBFDifferentialMomentum
  rw [residualLimitLorentzCarrierReader_coframe,
    residualLimitLorentzCarrierReader_gravityAuxiliary]
  suffices
      gravityAuxiliaryHodgePairingPolynomial
        (canonicalPhysicalSource.coframeAt point)
        (physicalIIPlusBivector
          (canonicalPhysicalSource.coframeAt point))
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          (residualLimitLorentzBasisDirection 2 0)) = 0 by
    rw [this]
    ring
  fin_cases derivativeDirection <;>
    simp [gravityAuxiliaryHodgePairingPolynomial,
      canonicalPhysicalSource_coframeAt_eq_transvection,
      physicalIIPlusBivector, internalBivectorDual, coframeWedge,
      coframeTwoFormLinear, lorentzConnectionExteriorDerivativeDirection,
      residualLimitLorentzBasisDirection,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond,
      Matrix.one_apply, Matrix.transvection, Matrix.single,
      Fin.sum_univ_six]

theorem residualLimitLorentzCarrierReader_differentialMomentumField_basis_two_zero
    (derivativeDirection : LorentzianIndex) :
    lorentzConnectionBFDifferentialMomentum
      residualLimitLorentzCarrierReader
      (lorentzConnectionExteriorDerivativeDirection derivativeDirection
        (residualLimitLorentzBasisDirection 2 0)) = 0 := by
  funext point
  exact
    residualLimitLorentzCarrierReader_differentialMomentum_basis_two_zero
      derivativeDirection point

theorem residualLimitLorentzCarrierReader_divergence_basis_two_zero_eq_zero :
    lorentzConnectionBFDifferentialMomentumDivergence
      residualLimitLorentzCarrierReader
      (residualLimitLorentzBasisDirection 2 0) 0 = 0 := by
  unfold lorentzConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_eq_zero
  intro derivativeDirection _
  rw [
    residualLimitLorentzCarrierReader_differentialMomentumField_basis_two_zero]
  simp [fieldDirectionalDerivative]

theorem residualLimitLorentzCarrierReader_balance_basis_two_zero_eq_one :
    lorentzGravityBFBalanceCoefficient residualLimitLorentzCarrierReader
      (residualLimitLorentzBasisDirection 2 0) 0 = 1 := by
  unfold lorentzGravityBFBalanceCoefficient
  rw [residualLimitLorentzCarrierReader_algebraic_basis_two_zero_eq_one,
    residualLimitLorentzCarrierReader_divergence_basis_two_zero_eq_zero]
  norm_num

/-- Complete actual gravity--BF balance seed of the residual-limit carrier.
This is a residual readout, not a source slot or a shell certificate. -/
def positiveResidualLimitLorentzBalance :
    LorentzBivectorOneForm → ℝ :=
  fun direction =>
    lorentzGravityBFBalanceCoefficient residualLimitLorentzCarrierReader
      direction 0

/-- The complete balance seed is nonzero, witnessed by the explicitly
computed basis coordinate. -/
theorem positiveResidualLimitLorentzBalance_ne_zero :
    positiveResidualLimitLorentzBalance ≠ 0 := by
  intro balanceZero
  have coordinateZero :
      positiveResidualLimitLorentzBalance
          (residualLimitLorentzBasisDirection 2 0) = 0 := by
    simpa using congrFun balanceZero
      (residualLimitLorentzBasisDirection 2 0)
  have coordinateOne :
      positiveResidualLimitLorentzBalance
          (residualLimitLorentzBasisDirection 2 0) = 1 := by
    simpa only [positiveResidualLimitLorentzBalance] using
      residualLimitLorentzCarrierReader_balance_basis_two_zero_eq_one
  rw [coordinateOne] at coordinateZero
  norm_num at coordinateZero

/-! ## Frozen carrier-class obstruction -/

/-- Every full completion of the residual-limit six-field carrier has the
same complete gravity--BF balance function.  The equality follows from the
three primitive fields actually consumed by this readout. -/
theorem residualLimitExtension_lorentzGravityBFBalance_function_eq
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier
        configuration) :
    (fun direction =>
      lorentzGravityBFBalanceCoefficient configuration direction 0) =
      positiveResidualLimitLorentzBalance := by
  funext direction
  have algebraicEq :
      lorentzGravityBFAlgebraicCoefficient configuration direction 0 =
        lorentzGravityBFAlgebraicCoefficient residualLimitLorentzCarrierReader
          direction 0 := by
    unfold lorentzGravityBFAlgebraicCoefficient generatedVolumeDensity
      toContinuumPointField lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    rw [extension.coframe, extension.gravityAuxiliary,
      extension.gravityConnection]
    rfl
  have momentumEq
      (derivativeDirection : LorentzianIndex) :
      lorentzConnectionBFDifferentialMomentum configuration
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction) =
        lorentzConnectionBFDifferentialMomentum
          residualLimitLorentzCarrierReader
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction) := by
    funext point
    unfold lorentzConnectionBFDifferentialMomentum generatedVolumeDensity
      toContinuumPointField
    rw [extension.coframe, extension.gravityAuxiliary]
    rfl
  have divergenceEq :
      lorentzConnectionBFDifferentialMomentumDivergence configuration
          direction 0 =
        lorentzConnectionBFDifferentialMomentumDivergence
          residualLimitLorentzCarrierReader direction 0 := by
    unfold lorentzConnectionBFDifferentialMomentumDivergence
    apply Finset.sum_congr rfl
    intro derivativeDirection _
    rw [momentumEq derivativeDirection]
  unfold positiveResidualLimitLorentzBalance
    lorentzGravityBFBalanceCoefficient
  rw [algebraicEq, divergenceEq]

/-- The actual basis value is independent of the three omitted completion
fields throughout the declared residual-limit six-field reader class. -/
theorem residualLimitExtension_lorentzGravityBFBalance_basis_two_zero_eq_one
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier
        configuration) :
    lorentzGravityBFBalanceCoefficient configuration
        (residualLimitLorentzBasisDirection 2 0) 0 = 1 := by
  have balanceEq := congrFun
    (residualLimitExtension_lorentzGravityBFBalance_function_eq
      configuration extension) (residualLimitLorentzBasisDirection 2 0)
  rw [balanceEq]
  simpa only [positiveResidualLimitLorentzBalance] using
    residualLimitLorentzCarrierReader_balance_basis_two_zero_eq_one

/-- With the source matter-orbit condition, the complete Lorentz
Euler--Lagrange residual is exactly the same actual gravity--BF seed. -/
theorem residualLimitRealizingOrbit_lorentzResidual_function_eq
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration)
    (realizes :
      RealizesPositiveSourceMatterFirstJetOrbitAtOrigin n configuration) :
    (fun direction =>
      lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        configuration direction 0) =
      positiveResidualLimitLorentzBalance := by
  funext direction
  rw [realizingOrbit_lorentzResidual_origin_eq_gravityBFBalance
    n configuration realizes]
  exact congrFun
    (residualLimitExtension_lorentzGravityBFBalance_function_eq
      configuration extension) direction

/-- Exact first-formula obstruction on one Lorentz coordinate for any actual
update between consecutive endpoints in the frozen class. -/
theorem residualLimitMatterOrbit_lorentzLiftDefect_basis_two_zero_eq_sigma
    (n : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends : ExtendsResidualLimitAndMatterOrbitAt n initial)
    (terminalExtends : ExtendsResidualLimitAndMatterOrbitAt (n + 1) terminal)
    (update : CurrentJointShellStateUpdate)
    (updateInitial : update initial = terminal) :
    ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
        initial) 0).eulerLagrange.lorentzConnection
          (residualLimitLorentzBasisDirection 2 0) =
      positiveSmoothUnifiedSource.legacy.sigma := by
  change
    lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
          (update initial) (residualLimitLorentzBasisDirection 2 0) 0 -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) *
          lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
            initial (residualLimitLorentzBasisDirection 2 0) 0 =
      positiveSmoothUnifiedSource.legacy.sigma
  rw [updateInitial,
    realizingOrbit_lorentzResidual_origin_eq_gravityBFBalance
      (n + 1) terminal terminalExtends.matterOrbit,
    realizingOrbit_lorentzResidual_origin_eq_gravityBFBalance
      n initial initialExtends.matterOrbit,
    residualLimitExtension_lorentzGravityBFBalance_basis_two_zero_eq_one
      terminal terminalExtends.residualLimit,
    residualLimitExtension_lorentzGravityBFBalance_basis_two_zero_eq_one
      initial initialExtends.residualLimit]
  ring

theorem residualLimitMatterOrbit_lorentzLiftDefect_basis_two_zero_ne_zero
    (n : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends : ExtendsResidualLimitAndMatterOrbitAt n initial)
    (terminalExtends : ExtendsResidualLimitAndMatterOrbitAt (n + 1) terminal)
    (update : CurrentJointShellStateUpdate)
    (updateInitial : update initial = terminal) :
    ((currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
        initial) 0).eulerLagrange.lorentzConnection
          (residualLimitLorentzBasisDirection 2 0) ≠ 0 := by
  rw [residualLimitMatterOrbit_lorentzLiftDefect_basis_two_zero_eq_sigma
    n initial terminal initialExtends terminalExtends update updateInitial]
  exact ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos

/-- The complete pointwise defect is nonzero only under the explicit frozen
endpoint-class hypotheses above. -/
theorem residualLimitMatterOrbit_jointStateLiftDefect_origin_ne_zero
    (n : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends : ExtendsResidualLimitAndMatterOrbitAt n initial)
    (terminalExtends : ExtendsResidualLimitAndMatterOrbitAt (n + 1) terminal)
    (update : CurrentJointShellStateUpdate)
    (updateInitial : update initial = terminal) :
    currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
        initial 0 ≠ 0 := by
  intro defectZero
  exact
    (residualLimitMatterOrbit_lorentzLiftDefect_basis_two_zero_ne_zero
      n initial terminal initialExtends terminalExtends update updateInitial)
      (congrArg
        (fun residual : CurrentPointwiseJointShellResidualCarrier =>
          residual.eulerLagrange.lorentzConnection
            (residualLimitLorentzBasisDirection 2 0))
        defectZero)

/-- Class-specific transport-lift rejection.  This theorem does not quantify
over arbitrary Stage-9 shell configurations. -/
theorem residualLimitMatterOrbit_not_transportLiftAt
    (n : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends : ExtendsResidualLimitAndMatterOrbitAt n initial)
    (terminalExtends : ExtendsResidualLimitAndMatterOrbitAt (n + 1) terminal)
    (update : CurrentJointShellStateUpdate)
    (updateInitial : update initial = terminal) :
    ¬ CurrentJointShellResidualTransportLiftAt positiveSmoothUnifiedSource
        update initial := by
  intro transportLift
  have defectSectionZero :
      currentJointShellStateLiftDefect positiveSmoothUnifiedSource update
          initial = 0 :=
    (currentJointShellStateLiftDefect_eq_zero_iff_transportLift
      positiveSmoothUnifiedSource update initial).2 transportLift
  exact residualLimitMatterOrbit_jointStateLiftDefect_origin_ne_zero
    n initial terminal initialExtends terminalExtends update updateInitial
    (congrFun defectSectionZero 0)

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzClassObstruction
