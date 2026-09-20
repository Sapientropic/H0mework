import H0mework.Physics.Admission.ResidualLimitScalarBalanceClosure

/-!
# S9-C3h39: P286 BF source-balance decision

This module decides the actual P286 BF balance left after
the scalar current was proved zero.  It accepts no balance value, zero-fiber
witness, tuned source, ansatz coefficient, shell, or stationarity receipt.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitP286BFBalanceDecision

open ProofFreeRicherAnholonomicSource
open PhysicalIIPlusFrechetVariation
open EmpiricalReferenceScaleCouplingBoundary
open SourceGeneratedPhysicalPlebanskiConfiguration
open NonseparableGravityGaugeSourceAction
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineBlockwiseConstitutive
open StageNineHolonomicField
open StageNineJointResidualResponseSnapshot
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNineResidualLimitMatterOrbitJointClassification
open StageNineResidualLimitP286ScalarFrozenTransportBoundary
open StageNineResidualLimitP286ScalarSourceNormalForm
open StageNineResidualLimitScalarBalanceClosure
open StageNineRequiredDifferentialResponseTransport
open StageNineSourceGeneratedPartialPrimitiveCarrier
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def p286CommutatorProbeData : P286LieBlockData :=
  p286LieBracket (colorMixingGenerator, 0, 0) canonicalP286Generator

def p286CommutatorProbe : P286GaugeOneForm
  | 0 => p286CoordinateEquiv p286CommutatorProbeData
  | _ => 0

def p286DoubleCommutatorProbeData : P286LieBlockData :=
  p286LieBracket p286CommutatorProbeData (colorMixingGenerator, 0, 0)

theorem positiveSourceGaugeCurvature_zero :
    sourceGaugeCurvature positiveSmoothUnifiedSource.legacy 0 =
      (1 / 4 : ℝ) := by
  simpa [positiveSmoothUnifiedSource, SmoothUnifiedSource.legacy,
    SmoothUnifiedSource.forget] using
    canonicalPhysicalSource_gaugeCurvature_component

theorem positiveSourceGaugeCurvature_one :
    sourceGaugeCurvature positiveSmoothUnifiedSource.legacy 1 = 0 := by
  change minkowskiInternalSign (pairFirst (0 : Fin 6)) *
      canonicalPhysicalSource.coordinateCurvatureAtOrigin
        (pairFirst (0 : Fin 6)) (pairSecond (0 : Fin 6))
        (pairFirst (1 : Fin 6)) (pairSecond (1 : Fin 6)) = 0
  simp [Source.coordinateCurvatureAtOrigin,
    Source.raisedChristoffelDerivativeAtOrigin,
    Source.inverseMetricDerivativeAtOrigin,
    Source.metricFirstDerivativeAtOrigin,
    Source.loweredChristoffelDerivativeAtOrigin,
    Source.metricSecondDerivativeAtOrigin,
    Source.raisedChristoffelAtOrigin,
    Source.loweredChristoffelAtOrigin,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection,
    PointwiseLorentzianCoframeJet.metricDerivative,
    Source.jetAt, canonicalPhysicalSource, canonicalSource,
    Source.toPhysicalSource, Source.physicalPhaseAmplitude,
    n10FiveSevenPhasePotential, shearCoefficient, pairFirst, pairSecond,
    minkowskiInternalSign, Fin.sum_univ_four]

theorem positiveSourceGaugeCurvature_apply (pair : Fin 6) :
    sourceGaugeCurvature positiveSmoothUnifiedSource.legacy pair =
      if pair = 0 then (1 / 4 : ℝ) else 0 := by
  fin_cases pair
  · simpa using positiveSourceGaugeCurvature_zero
  · simpa using positiveSourceGaugeCurvature_one
  all_goals
    change minkowskiInternalSign (pairFirst (0 : Fin 6)) *
        canonicalPhysicalSource.coordinateCurvatureAtOrigin
          (pairFirst (0 : Fin 6)) (pairSecond (0 : Fin 6))
          (pairFirst (_ : Fin 6)) (pairSecond (_ : Fin 6)) = 0
    simp [Source.coordinateCurvatureAtOrigin,
      Source.raisedChristoffelDerivativeAtOrigin,
      Source.inverseMetricDerivativeAtOrigin,
      Source.metricFirstDerivativeAtOrigin,
      Source.loweredChristoffelDerivativeAtOrigin,
      Source.metricSecondDerivativeAtOrigin,
      Source.raisedChristoffelAtOrigin,
      Source.loweredChristoffelAtOrigin,
      PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection,
      PointwiseLorentzianCoframeJet.metricDerivative,
      Source.jetAt, canonicalPhysicalSource, canonicalSource,
      Source.toPhysicalSource, Source.physicalPhaseAmplitude,
      n10FiveSevenPhasePotential, shearCoefficient, pairFirst, pairSecond,
      minkowskiInternalSign, Fin.sum_univ_four]

theorem realScaleP286_eq_smul (scalar : ℝ) (data : P286LieBlockData) :
    realScaleP286 scalar data = scalar • data := by
  ext <;> simp [realScaleP286, realScaleHypercharge]

theorem positiveSourceP286TargetCurvature_apply (pair : Fin 6) :
    p286CoordinateEquiv
        (sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy pair) =
      if pair = 0 then
        (1 / 4 : ℝ) • p286CoordinateEquiv canonicalP286Generator
      else 0 := by
  rw [sourceP286TargetCurvature, positiveSourceGaugeCurvature_apply]
  split_ifs with hpair
  · rw [realScaleP286_eq_smul, p286CoordinateEquiv.map_smul]
  · simp

theorem positiveResidualLimitP286AuxiliaryCoordinate_apply
    (point : BasePoint) (pair : Fin 6) :
    positiveResidualLimitP286AuxiliaryCoordinate point pair =
      if pair = 3 then
        (1 / 2 : ℝ) • p286CoordinateEquiv canonicalP286Generator
      else 0 := by
  simp only [positiveResidualLimitP286AuxiliaryCoordinate,
    positiveResidualLimitSixFieldCarrier,
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier,
    positiveSourceStageNinePartialPrimitiveCarrier,
    sourceGeneratedStageNinePartialPrimitiveCarrier,
    generatedP286GaugeConstitutiveAuxiliary,
    p286CoordinateEquiv.apply_symm_apply]
  change p286GaugeConstitutiveAuxiliaryCoordinate
      positiveSmoothUnifiedSource (canonicalPhysicalSource.coframeAt point)
        (fun candidate => p286CoordinateEquiv
          (sourceP286TargetCurvature
            positiveSmoothUnifiedSource.legacy candidate)) pair = _
  unfold p286GaugeConstitutiveAuxiliaryCoordinate
  have couplingInverse :
      (((sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)⁻¹) = 2 := by
    change (positiveSmoothUnifiedSource.legacy.sigma)⁻¹ = 2
    rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half]
    norm_num
  rw [couplingInverse]
  rw [coframeGaugeSpacetimeHodgeLinear_positiveSource]
  rw [WithLp.ext_iff]
  funext internal
  simp only [Pi.smul_apply, WithLp.ofLp_smul]
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  simp_rw [positiveSourceP286TargetCurvature_apply]
  fin_cases pair <;>
    simp [positiveGaugeSpacetimeHodge, positiveCoframeTwoFormFrame,
      lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val];
    ring

theorem positiveResidualLimitP286FramedAuxiliary_apply
    (point : BasePoint) (pair : Fin 6) :
    liftGaugeTwoFormOperator
        (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
        (positiveResidualLimitP286AuxiliaryCoordinate point) pair =
      if pair = 3 then
        (1 / 2 : ℝ) • p286CoordinateEquiv canonicalP286Generator
      else 0 := by
  rw [coframeTwoFormLinear_positiveSource]
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  simp_rw [positiveResidualLimitP286AuxiliaryCoordinate_apply]
  fin_cases pair <;>
    simp [positiveCoframeTwoFormFrame, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val]

theorem positiveResidualLimitP286FramedDirectionHodge_three
    (point : BasePoint) (direction : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator lorentzianCoframeHodge
        (liftGaugeTwoFormOperator
          (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
          direction) 3 =
      -direction 0 := by
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  have framedDirection :
      (fun input =>
        (liftGaugeTwoFormOperator
          (coframeTwoFormLinear (canonicalPhysicalSource.coframeAt point))
          direction input).ofLp internal) =
        positiveCoframeTwoFormFrame point
          (fun input => (direction input).ofLp internal) := by
    funext input
    rw [liftGaugeTwoFormOperator_p286Coordinate_apply,
      coframeTwoFormLinear_positiveSource]
    rfl
  rw [framedDirection]
  simp [lorentzianCoframeHodge, positiveCoframeTwoFormFrame,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val]

theorem positiveResidualLimitP286DifferentialMomentum_normalForm
    (direction : P286GaugeTwoForm) (point : BasePoint) :
    positiveResidualLimitP286DifferentialMomentum direction point =
      -(1 / 2 : ℝ) *
        p286CoordinateLiePairing
          (p286CoordinateEquiv canonicalP286Generator) (direction 0) := by
  unfold positiveResidualLimitP286DifferentialMomentum
  change
    abs (Matrix.det (canonicalPhysicalSource.coframeAt point)) *
        p286GaugeAuxiliaryHodgePairingPolynomial
          (canonicalPhysicalSource.coframeAt point)
          (positiveResidualLimitP286AuxiliaryCoordinate point) direction = _
  rw [canonicalPhysicalSource_coframeAt_det]
  simp only [abs_one, one_mul]
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  simp_rw [positiveResidualLimitP286FramedAuxiliary_apply]
  rw [Fin.sum_univ_six]
  simp [positiveResidualLimitP286FramedDirectionHodge_three,
    lorentzianTwoFormSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_smul_left]
  rw [show -direction 0 = (-1 : ℝ) • direction 0 by simp,
    p286CoordinateLiePairing_smul_right]
  ring

theorem positiveResidualLimitP286DifferentialMomentum_diagonalDerivative_eq_zero
    (direction : P286GaugeOneForm)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (positiveResidualLimitP286DifferentialMomentum
          (p286GaugeExteriorDerivativeDirection derivativeDirection direction))
        0 derivativeDirection = 0 := by
  have momentumFunction :
      positiveResidualLimitP286DifferentialMomentum
          (p286GaugeExteriorDerivativeDirection derivativeDirection direction) =
        fun _ =>
          -(1 / 2 : ℝ) *
            p286CoordinateLiePairing
              (p286CoordinateEquiv canonicalP286Generator)
              (p286GaugeExteriorDerivativeDirection
                derivativeDirection direction 0) := by
    funext point
    exact positiveResidualLimitP286DifferentialMomentum_normalForm
      (p286GaugeExteriorDerivativeDirection derivativeDirection direction) point
  rw [momentumFunction]
  simp [fieldDirectionalDerivative]

theorem positiveResidualLimitP286Divergence_apply_eq_zero
    (direction : P286GaugeOneForm) :
    positiveResidualLimitP286Divergence direction = 0 := by
  unfold positiveResidualLimitP286Divergence
  exact Finset.sum_eq_zero fun derivativeDirection _ =>
    positiveResidualLimitP286DifferentialMomentum_diagonalDerivative_eq_zero
      direction derivativeDirection

theorem positiveResidualLimitP286Divergence_eq_zero :
    positiveResidualLimitP286Divergence = 0 := by
  funext direction
  exact positiveResidualLimitP286Divergence_apply_eq_zero direction

theorem positiveResidualLimitP286ConnectionCoordinate_origin
    (direction : LorentzianIndex) :
    positiveResidualLimitP286ConnectionCoordinate 0 direction =
      p286CoordinateEquiv
        (sourceP286Potential positiveSmoothUnifiedSource.legacy direction) := by
  simp [positiveResidualLimitP286ConnectionCoordinate,
    positiveResidualLimitSixFieldCarrier,
    positiveSourceResidualLimitStageNinePartialPrimitiveCarrier,
    positiveSourceStageNinePartialPrimitiveCarrier,
    sourceGeneratedStageNinePartialPrimitiveCarrier,
    sourceP286AffineConnectionField_origin]

theorem positiveResidualLimitP286ConnectionCoordinate_origin_zero :
    positiveResidualLimitP286ConnectionCoordinate 0 0 =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv (colorCartanGenerator, 0, 0) := by
  rw [positiveResidualLimitP286ConnectionCoordinate_origin]
  change p286CoordinateEquiv
      (realScaleP286 positiveSmoothUnifiedSource.legacy.sigma
        (colorCartanGenerator, 0, 0)) = _
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half,
    realScaleP286_eq_smul, p286CoordinateEquiv.map_smul]

theorem positiveResidualLimitP286ConnectionCoordinate_origin_one :
    positiveResidualLimitP286ConnectionCoordinate 0 1 =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv (colorMixingGenerator, 0, 0) := by
  rw [positiveResidualLimitP286ConnectionCoordinate_origin]
  change p286CoordinateEquiv
      (realScaleP286 positiveSmoothUnifiedSource.legacy.sigma
        (colorMixingGenerator, 0, 0)) = _
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half,
    realScaleP286_eq_smul, p286CoordinateEquiv.map_smul]

theorem positiveResidualLimitP286ConnectionCoordinate_origin_two :
    positiveResidualLimitP286ConnectionCoordinate 0 2 = 0 := by
  rw [positiveResidualLimitP286ConnectionCoordinate_origin]
  simp [sourceP286Potential]

theorem positiveResidualLimitP286ConnectionCoordinate_origin_three :
    positiveResidualLimitP286ConnectionCoordinate 0 3 = 0 := by
  rw [positiveResidualLimitP286ConnectionCoordinate_origin]
  simp [sourceP286Potential]

theorem p286CoordinateLieBracket_equiv_apply
    (first second : P286LieBlockData) :
    p286CoordinateLieBracket (p286CoordinateEquiv first)
        (p286CoordinateEquiv second) =
      p286CoordinateEquiv (p286LieBracket first second) := by
  simp [p286CoordinateLieBracket]

theorem positiveResidualLimitP286ProbeAlgebraicCurvature_apply
    (pair : Fin 6) :
    positiveResidualLimitP286AlgebraicCurvatureDirection
        p286CommutatorProbe pair =
      if pair = 0 then
        (1 / 2 : ℝ) •
          p286CoordinateEquiv p286DoubleCommutatorProbeData
      else 0 := by
  unfold positiveResidualLimitP286AlgebraicCurvatureDirection
  fin_cases pair <;>
    simp [p286CommutatorProbe, p286DoubleCommutatorProbeData,
      p286CommutatorProbeData, p286CoordinateLieBracket_equiv_apply,
      positiveResidualLimitP286ConnectionCoordinate_origin_zero,
      positiveResidualLimitP286ConnectionCoordinate_origin_one,
      positiveResidualLimitP286ConnectionCoordinate_origin_two,
      positiveResidualLimitP286ConnectionCoordinate_origin_three,
      p286CoordinateLieBracket_smul_right,
      pairFirst, pairSecond]

theorem positiveResidualLimitP286BFAlgebraicResponse_eq_momentum
    (direction : P286GaugeOneForm) :
    positiveResidualLimitP286BFAlgebraicResponse direction =
      positiveResidualLimitP286DifferentialMomentum
        (positiveResidualLimitP286AlgebraicCurvatureDirection direction) 0 := by
  unfold positiveResidualLimitP286BFAlgebraicResponse
    positiveResidualLimitP286DifferentialMomentum
  change
    abs (Matrix.det (canonicalPhysicalSource.coframeAt 0)) *
        p286GaugeBFCurvatureIncrementDensity
          (canonicalPhysicalSource.coframeAt 0)
          (coframeGaugeSpacetimeHodgeLinear
            (canonicalPhysicalSource.coframeAt 0))
          (positiveResidualLimitP286AuxiliaryCoordinate 0)
          (positiveResidualLimitP286AlgebraicCurvatureDirection direction) =
      abs (Matrix.det (canonicalPhysicalSource.coframeAt 0)) *
        p286GaugeAuxiliaryHodgePairingPolynomial
          (canonicalPhysicalSource.coframeAt 0)
          (positiveResidualLimitP286AuxiliaryCoordinate 0)
          (positiveResidualLimitP286AlgebraicCurvatureDirection direction)
  rw [p286GaugeAuxiliaryHodgePairingPolynomial_eq]
  · rfl
  · rw [canonicalPhysicalSource_coframeAt_det]
    norm_num

theorem positiveResidualLimitP286BFAlgebraicResponse_probe_normalForm :
    positiveResidualLimitP286BFAlgebraicResponse p286CommutatorProbe =
      -(1 / 4 : ℝ) *
        p286CoordinateLiePairing
          (p286CoordinateEquiv canonicalP286Generator)
          (p286CoordinateEquiv p286DoubleCommutatorProbeData) := by
  rw [positiveResidualLimitP286BFAlgebraicResponse_eq_momentum,
    positiveResidualLimitP286DifferentialMomentum_normalForm,
    positiveResidualLimitP286ProbeAlgebraicCurvature_apply]
  simp only [if_pos]
  rw [p286CoordinateLiePairing_smul_right]
  ring

theorem p286DoubleCommutatorProbeData_eq_colorCartan :
    p286DoubleCommutatorProbeData =
      (4 : ℝ) • (colorCartanGenerator, 0, 0) := by
  apply Prod.ext
  · apply Subtype.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [p286DoubleCommutatorProbeData,
        p286CommutatorProbeData, p286LieBracket, suLieBracket,
        canonicalP286Generator, colorCartanGenerator, colorCartanRaw,
        colorMixingGenerator, colorMixingRaw, Matrix.mul_apply,
        Fin.sum_univ_three] <;>
      simp [Matrix.diagonal] <;>
      ring
  · simp [p286DoubleCommutatorProbeData, p286CommutatorProbeData,
      p286LieBracket, suLieBracket]

theorem colorCartanGenerator_pairing_self :
    specialUnitaryLiePairing colorCartanGenerator colorCartanGenerator = 2 := by
  norm_num [specialUnitaryLiePairing, colorCartanGenerator,
    colorCartanRaw, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals simp

theorem p286ProbePairing_eq_eight :
    p286CoordinateLiePairing
        (p286CoordinateEquiv canonicalP286Generator)
        (p286CoordinateEquiv p286DoubleCommutatorProbeData) = 8 := by
  rw [p286DoubleCommutatorProbeData_eq_colorCartan,
    p286CoordinateEquiv.map_smul,
    p286CoordinateLiePairing_smul_right]
  simp only [p286CoordinateLiePairing, LinearEquiv.symm_apply_apply,
    p286LiePairing, canonicalP286Generator]
  change 4 *
      (specialUnitaryLiePairing colorCartanGenerator colorCartanGenerator +
        specialUnitaryLiePairing weakCartanGenerator 0 +
        hyperchargeLiePairing hyperchargeGenerator 0) = 8
  rw [colorCartanGenerator_pairing_self]
  simp [specialUnitaryLiePairing, hyperchargeLiePairing]
  norm_num

theorem positiveResidualLimitP286BFAlgebraicResponse_probe_eq_neg_two :
    positiveResidualLimitP286BFAlgebraicResponse p286CommutatorProbe = -2 := by
  rw [positiveResidualLimitP286BFAlgebraicResponse_probe_normalForm,
    p286ProbePairing_eq_eight]
  norm_num

theorem positiveResidualLimitP286BFBalance_probe_eq_neg_two :
    positiveResidualLimitP286BFBalance p286CommutatorProbe = -2 := by
  unfold positiveResidualLimitP286BFBalance
  rw [positiveResidualLimitP286BFAlgebraicResponse_probe_eq_neg_two,
    positiveResidualLimitP286Divergence_apply_eq_zero]
  norm_num

theorem positiveResidualLimitP286BFBalance_ne_zero :
    positiveResidualLimitP286BFBalance ≠ 0 := by
  intro balanceZero
  have probeZero := congrFun balanceZero p286CommutatorProbe
  rw [positiveResidualLimitP286BFBalance_probe_eq_neg_two] at probeZero
  norm_num at probeZero

theorem positiveResidualLimitP286TotalBalance_probe_eq_neg_two :
    positiveResidualLimitP286TotalBalance p286CommutatorProbe = -2 := by
  unfold positiveResidualLimitP286TotalBalance
  rw [positiveResidualLimitP286BFBalance_probe_eq_neg_two,
    positiveSourceOriginP286ScalarCurrent_eq_zero]
  norm_num

theorem positiveResidualLimitP286TotalBalance_ne_zero :
    positiveResidualLimitP286TotalBalance ≠ 0 := by
  intro balanceZero
  have probeZero := congrFun balanceZero p286CommutatorProbe
  rw [positiveResidualLimitP286TotalBalance_probe_eq_neg_two] at probeZero
  norm_num at probeZero

theorem residualLimitMatterOrbit_p286ActualResidual_transport_noGo
    (initialIndex terminalIndex : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsResidualLimitAndMatterOrbitAt initialIndex initial)
    (terminalExtends :
      ExtendsResidualLimitAndMatterOrbitAt terminalIndex terminal) :
    ¬ ((fun direction =>
      p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource terminal direction 0) =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (fun direction =>
            p286GaugeConnectionEulerLagrangeCoefficient
              positiveSmoothUnifiedSource initial direction 0)) := by
  intro transported
  have balanceZero :=
    (residualLimitMatterOrbit_p286ActualResidual_transport_iff_sourceBalance_zero
      initialIndex terminalIndex initial terminal initialExtends
      terminalExtends).mp transported
  exact positiveResidualLimitP286TotalBalance_ne_zero balanceZero

theorem residualLimitMatterOrbit_p286RequiredResponse_mismatch
    (initialIndex : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsResidualLimitAndMatterOrbitAt initialIndex initial)
    (terminalExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier terminal) :
    ¬ ((fun direction =>
      p286GaugeConnectionBFDifferentialMomentumDivergence terminal
        direction 0) =
        (sourceSigmaRequiredDifferentialResponseSnapshot
          positiveSmoothUnifiedSource
          (pointwiseResidualResponseSnapshot positiveSmoothUnifiedSource
            initial 0)).p286BFDifferentialMomentumDivergence) := by
  intro matched
  have balanceZero :=
    (residualLimitMatterOrbit_p286RequiredResponse_matches_iff_sourceBalance_zero
      initialIndex initial terminal initialExtends terminalExtends).mp matched
  exact positiveResidualLimitP286TotalBalance_ne_zero balanceZero

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitP286BFBalanceDecision
