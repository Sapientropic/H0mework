import H0mework.Physics.DualVariation.ECCauchyConnectionLocalActualLiftRegression
import H0mework.Physics.Gauge.GaugeAuxiliaryVariation
import H0mework.Physics.Dirac.ScalarLocalSpinDensity
import H0mework.Physics.Matter.SU7ExteriorBreakingYukawa

/-!
# Fixed KIN-8 repaired-root EC Cauchy constraint obstruction

The temporal EC connection write solves the twelve evolution rows but, by
construction, transports the four temporal-column Cauchy rows.  This file
computes the latter on the fixed P506/L0 KIN-8 actual from the authoritative
repaired `II+` coframe equation.

The readout here is the reduced Einstein--Cartan coefficient

```text
curvature + intrinsic coframe wedge + gauge + repaired Dirac-dual matter,
```

not the historical frozen-`B` multiplier reaction.  No KIN-9 zero theorem,
constraint certificate, target curvature, residual value, or branch choice
is used to produce the result.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECCauchyConstraintObstructionRegression

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeFirstJet
open StageNineCoframeVariation
open StageNineConjugateMatterActionTimeVelocity
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanConnectionLocalActualLiftRegression
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanReactionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionLocalActualLiftRegression
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLiftRegression
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineJointActionLocalActualLift
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNineMatterActionTimeVelocity
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineScalarLocalSpinDensity
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineTopologicalFourFormPairing
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRestriction

open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-! ## Fixed KIN-8 magnetic contribution -/

/-- The spatial Cartan curvature contributes `1/8` to the temporal-dilation
constraint.  KIN-8 changes only the reaction field, so this is the same live
primitive connection curvature computed at KIN-6. -/
theorem positiveDiracDualCartanReaction_curvatureConstraint_zero :
    identityDiracDualECConstraintObservation
        (diracDualFormNativeECCauchyCurrentCurvature
          positiveDiracDualCartanReactionLocalActual) 0 =
      (1 / 8 : ℝ) := by
  rw [positiveDiracDualECCauchyCurrentCurvature_eq_connectionOnly,
    congrFun (identityDiracDualECConstraintObservation_explicit
      (holonomicGravityCurvature
        positiveDiracDualCartanConnectionLocalActual 0)) 0]
  change
    -(holonomicGravityCurvature positiveDiracDualCartanConnectionLocalActual
          0 3 3 +
        holonomicGravityCurvature positiveDiracDualCartanConnectionLocalActual
          0 4 4 +
        holonomicGravityCurvature positiveDiracDualCartanConnectionLocalActual
          0 5 5) =
      (1 / 8 : ℝ)
  unfold holonomicGravityCurvature
  simp [pairFirst, pairSecond, minkowskiInternalSign]
  rw [show
      gravityConnectionDerivative positiveDiracDualCartanConnectionLocalActual
          0 2 3 2 3 = 0 by
        exact positiveDiracDualCartanConnection_spatialDerivative_zero
          1 3 2 3,
    show
      gravityConnectionDerivative positiveDiracDualCartanConnectionLocalActual
          0 3 2 2 3 = 0 by
        exact positiveDiracDualCartanConnection_spatialDerivative_zero
          2 2 2 3,
    show
      gravityConnectionDerivative positiveDiracDualCartanConnectionLocalActual
          0 3 1 3 1 = 0 by
        exact positiveDiracDualCartanConnection_spatialDerivative_zero
          2 1 3 1,
    show
      gravityConnectionDerivative positiveDiracDualCartanConnectionLocalActual
          0 1 3 3 1 = 0 by
        exact positiveDiracDualCartanConnection_spatialDerivative_zero
          0 3 3 1,
    show
      gravityConnectionDerivative positiveDiracDualCartanConnectionLocalActual
          0 1 2 1 2 = 0 by
        exact positiveDiracDualCartanConnection_spatialDerivative_zero
          0 2 1 2,
    show
      gravityConnectionDerivative positiveDiracDualCartanConnectionLocalActual
          0 2 1 1 2 = 0 by
        exact positiveDiracDualCartanConnection_spatialDerivative_zero
          1 1 1 2]
  simp [pairFirst, pairSecond, minkowskiInternalSign,
    positiveDiracDualCartanConnectionLocalActual_originConnection,
    fixedActionCartanConnection_eq_positiveNormalForm,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    Fin.sum_univ_four, Fin.sum_univ_six]
  norm_num

/-! ## Fixed repaired non-gravity contact -/

/-- The non-gravity fields consumed by the repaired EC load at KIN-8. -/
def positiveDiracDualCartanReactionECContactField :
    StageNineContinuumPointField :=
  diracDualFormNativeECNormalContactField
    positiveDiracDualCartanReactionLocalActual

@[simp] theorem positiveDiracDualCartanReactionECContactField_coframe :
    positiveDiracDualCartanReactionECContactField.coframe = 1 := by
  change positiveSourceTargetMatterCauchyState.coframe 0 = 1
  change positivePhaseProbeCauchyState.coframe 0 = 1
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

@[simp] theorem positiveDiracDualCartanReactionECContactField_matter :
    positiveDiracDualCartanReactionECContactField.matter =
      diracSpinTwoMatterProbe := by
  change
    (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
      positiveSourceTargetMatterCauchyState 0).matter 0 =
      diracSpinTwoMatterProbe
  rw [sourceActionGeneratedJointLocalActualLift_initialMatter]
  exact positiveSourceTargetMatterCauchyState_matter

@[simp] theorem positiveDiracDualCartanReactionECContactField_conjugateMatter :
    positiveDiracDualCartanReactionECContactField.conjugateMatter =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
      positiveSourceTargetMatterCauchyState 0).conjugateMatter 0 =
      diracSpinZeroMatterCoordinate
  rw [sourceActionGeneratedJointLocalActualLift_initialConjugateMatter]
  exact positiveSourceTargetMatterCauchyState_conjugate

@[simp] theorem positiveDiracDualCartanReactionECContactField_scalar :
    positiveDiracDualCartanReactionECContactField.scalar =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
      positiveSourceTargetMatterCauchyState 0).scalar 0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  rw [sourceActionGeneratedJointLocalActualLift_initialScalar]
  change positivePhaseProbeCauchyState.scalar 0 = _
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

@[simp] theorem positiveDiracDualCartanReactionECContactField_gaugeAuxiliary :
    positiveDiracDualCartanReactionECContactField.gaugeAuxiliary = 0 := by
  rfl

theorem
    positiveDiracDualCartanReactionECContactField_scalarCovariantDerivative :
    positiveDiracDualCartanReactionECContactField.scalarCovariantDerivative =
      0 := by
  funext direction
  change
    holonomicScalarCovariantDerivative
        positiveDiracDualCartanReactionLocalActual 0 direction = 0
  have scalarDerivativeZero :
      fieldDirectionalDerivative
          positiveDiracDualCartanReactionLocalActual.scalar 0 direction = 0 := by
    calc
      _ = actionGeneratedScalarLocalJetCoordinate
            positiveSourceTargetMatterCauchyState 0 direction := by
        simpa [positiveDiracDualCartanReactionLocalActual,
          sourceActionGeneratedDiracDualCartanReactionLocalActualLift,
          sourceActionGeneratedDiracDualCartanConnectionLocalActualLift,
          sourceActionGeneratedJointLocalActualLift,
          sourceActionGeneratedMatterDualScalarLocalActualLift,
          sourceActionGeneratedMatterDualLocalActualLift] using
          sourceActionGeneratedMatterDualScalarLocalActualLift_scalarDerivative_origin
            positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
              0 direction
      _ = 0 := by
        fin_cases direction <;>
          simp [actionGeneratedScalarLocalJetCoordinate,
            cauchyScalarSpatialDerivativeCoordinate,
            positiveSourceTargetMatterCauchyState,
            sourceTargetMatterCauchyState,
            positivePhaseProbeCauchyState_eq_normalForm,
            positiveProbeCauchyStateNormalForm]
  have gaugeConnectionZero :
      positiveDiracDualCartanReactionLocalActual.gaugeConnection 0 = 0 := by
    funext formDirection
    change
      sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
          positiveSourceTargetMatterCauchyState 0 0 formDirection = 0
    rw [sourceGeneratedP286ActionLocalConnection_origin]
    rfl
  unfold holonomicScalarCovariantDerivative
  rw [scalarDerivativeZero, gaugeConnectionZero]
  simp

/-- The zero auxiliary at this exact source contact makes the whole
first-order gauge coframe density identically zero, independently of the
candidate coframe. -/
theorem positiveDiracDualCartanReactionECContactField_gaugeDensity_zero :
    diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
        positiveDiracDualCartanReactionECContactField = 0 := by
  funext coframe
  unfold diracDualFormNativeCoframeGaugeDensity
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286]
  simp [withCoframe,
    positiveDiracDualCartanReactionECContactField_gaugeAuxiliary]

theorem positiveDiracDualCartanReactionECContactField_gaugeEuler_zero :
    diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
        positiveDiracDualCartanReactionECContactField = 0 := by
  unfold diracDualFormNativeCoframeGaugeEulerCovector
  rw [positiveDiracDualCartanReactionECContactField_gaugeDensity_zero]
  simp

/-- Both scalar kinetic and potential terms vanish at the source-generated
vacuum, for every coframe readout. -/
theorem positiveDiracDualCartanReactionECContactField_scalarDensity_zero
    (coframe : LorentzianCoframe) :
    generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource
        0 0
        (withCoframe positiveDiracDualCartanReactionECContactField coframe) =
      0 := by
  unfold generatedDensitizedContinuumScalarDensity
    generatedScalarKineticDensity
  simp only [withCoframe]
  rw [positiveDiracDualCartanReactionECContactField_scalarCovariantDerivative,
    positiveDiracDualCartanReactionECContactField_scalar]
  simp [scalarFrameRelativeCovariantDerivative,
    scalarCoordinatePairingRe, generatedScalarPotential]

/-- The independent P506 dual reads the degree-two summand, whereas the
repaired right-chiral Yukawa map lands in degree six. -/
theorem
    diracSpinZeroMatterCoordinate_diracDualRightChiralYukawaAction_eq_zero
    (scalar : ExteriorBreakingScalarCarrier)
    (field : DiracExteriorMatterCarrier) :
    diracSpinZeroMatterCoordinate
        (diracDualRightChiralYukawaAction scalar field) = 0 := by
  change
    ((su7ExteriorBasis 2).repr
      ((diracDualRightChiralYukawaAction scalar field 0).2.1))
        hyperchargeDegreeTwoIndex = 0
  unfold diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply]
  unfold
    diracExteriorYukawaInternalAction
    internalMatterLinearAction exteriorYukawaInternalAction
  simp

/-! ## Direct repaired matter coefficient at the KIN-8 contact -/

/-- The live KIN-8 Cartan connection acts on the selected matter probe in
the only spatial direction seen by the independent dual.  This is computed
from the installed connection normal form, not from a coframe equation. -/
theorem positiveDiracDualCartan_spinLift_three :
    diracMatrixMatterAction
        (diracSpinConnectionLift fixedActionCartanConnection 3)
        diracSpinTwoMatterProbe =
      (Complex.I / 8) • diracSpinTwoMatterProbe := by
  rw [fixedActionCartanConnection_eq_positiveNormalForm]
  funext spinIndex
  fin_cases spinIndex
  all_goals
    simp [diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      positiveDiracDualCartanContorsionNormalForm,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      Matrix.cons_val]
  all_goals try (congr 1; ring)

theorem positiveDiracDualCartan_spinLift_one :
    diracMatrixMatterAction
        (diracSpinConnectionLift fixedActionCartanConnection 1)
        diracSpinTwoMatterProbe = 0 := by
  rw [fixedActionCartanConnection_eq_positiveNormalForm]
  funext spinIndex
  fin_cases spinIndex
  all_goals
    simp [diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      positiveDiracDualCartanContorsionNormalForm,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      Matrix.cons_val]

theorem positiveDiracDualCartan_spinLift_two :
    diracMatrixMatterAction
        (diracSpinConnectionLift fixedActionCartanConnection 2)
        diracSpinTwoMatterProbe = 0 := by
  rw [fixedActionCartanConnection_eq_positiveNormalForm]
  funext spinIndex
  fin_cases spinIndex
  all_goals
    simp [diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      positiveDiracDualCartanContorsionNormalForm,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      Matrix.cons_val]

theorem positiveDiracDualCartanReactionECContactField_derivative_three :
    positiveDiracDualCartanReactionECContactField.matterCovariantDerivative 3 =
      (Complex.I / 8) • diracSpinTwoMatterProbe := by
  change
    holonomicMatterCovariantDerivative
        positiveDiracDualCartanReactionLocalActual 0 3 = _
  have rawDerivativeThree :
      fieldDirectionalDerivative
          (fun candidate => matterCoordinateEquiv
            (positiveDiracDualCartanReactionLocalActual.matter candidate))
          0 3 = 0 := by
    calc
      _ = actionGeneratedMatterLocalJetCoordinate
            positiveSourceTargetMatterCauchyState 0 3 := by
        simpa [positiveDiracDualCartanReactionLocalActual,
          sourceActionGeneratedDiracDualCartanReactionLocalActualLift,
          sourceActionGeneratedDiracDualCartanConnectionLocalActualLift,
          sourceActionGeneratedJointLocalActualLift,
          sourceActionGeneratedMatterDualScalarLocalActualLift,
          sourceActionGeneratedMatterDualLocalActualLift] using
          sourceActionGeneratedMatterLocalActualLift_rawDerivative_origin
            positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
              0 3
      _ = 0 := by
        simp [actionGeneratedMatterLocalJetCoordinate,
          cauchyMatterSpatialDerivativeCoordinate,
          positiveSourceTargetMatterCauchyState,
          sourceTargetMatterCauchyState]
  have matterOrigin :
      positiveDiracDualCartanReactionLocalActual.matter 0 =
        diracSpinTwoMatterProbe := by
    change
      (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
        positiveSourceTargetMatterCauchyState 0).matter 0 = _
    rw [sourceActionGeneratedJointLocalActualLift_initialMatter]
    exact positiveSourceTargetMatterCauchyState_matter
  have gaugeConnectionZero :
      positiveDiracDualCartanReactionLocalActual.gaugeConnection 0 = 0 := by
    funext formDirection
    change
      sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
          positiveSourceTargetMatterCauchyState 0 0 formDirection = 0
    rw [sourceGeneratedP286ActionLocalConnection_origin]
    rfl
  have connectionOrigin :
      positiveDiracDualCartanReactionLocalActual.gravityConnection 0 =
        fixedActionCartanConnection := by
    change positiveDiracDualCartanConnectionLocalActual.gravityConnection 0 = _
    exact positiveDiracDualCartanConnectionLocalActual_originConnection
  unfold holonomicMatterCovariantDerivative
  rw [rawDerivativeThree, matterOrigin, gaugeConnectionZero, connectionOrigin,
    positiveDiracDualCartan_spinLift_three]
  simp

private theorem positiveDiracDualCartanReaction_rawDerivative_spatial
    (axis : Fin 3) :
    fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv
          (positiveDiracDualCartanReactionLocalActual.matter candidate))
        0 axis.succ = 0 := by
  calc
    _ = actionGeneratedMatterLocalJetCoordinate
          positiveSourceTargetMatterCauchyState 0 axis.succ := by
      simpa [positiveDiracDualCartanReactionLocalActual,
        sourceActionGeneratedDiracDualCartanReactionLocalActualLift,
        sourceActionGeneratedDiracDualCartanConnectionLocalActualLift,
        sourceActionGeneratedJointLocalActualLift,
        sourceActionGeneratedMatterDualScalarLocalActualLift,
        sourceActionGeneratedMatterDualLocalActualLift] using
        sourceActionGeneratedMatterLocalActualLift_rawDerivative_origin
          positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
            0 axis.succ
    _ = 0 := by
      fin_cases axis <;>
        simp [actionGeneratedMatterLocalJetCoordinate,
          cauchyMatterSpatialDerivativeCoordinate,
          positiveSourceTargetMatterCauchyState,
          sourceTargetMatterCauchyState]

theorem positiveDiracDualCartanReactionECContactField_derivative_one :
    positiveDiracDualCartanReactionECContactField.matterCovariantDerivative 1 =
      0 := by
  change
    holonomicMatterCovariantDerivative
        positiveDiracDualCartanReactionLocalActual 0 1 = 0
  unfold holonomicMatterCovariantDerivative
  rw [show fieldDirectionalDerivative
      (fun candidate => matterCoordinateEquiv
        (positiveDiracDualCartanReactionLocalActual.matter candidate))
      0 1 = 0 by
        simpa using positiveDiracDualCartanReaction_rawDerivative_spatial 0]
  rw [show positiveDiracDualCartanReactionLocalActual.matter 0 =
      diracSpinTwoMatterProbe by
        change
          (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
            positiveSourceTargetMatterCauchyState 0).matter 0 = _
        rw [sourceActionGeneratedJointLocalActualLift_initialMatter]
        exact positiveSourceTargetMatterCauchyState_matter]
  rw [show positiveDiracDualCartanReactionLocalActual.gaugeConnection 0 = 0 by
      funext formDirection
      change
        sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
            positiveSourceTargetMatterCauchyState 0 0 formDirection = 0
      rw [sourceGeneratedP286ActionLocalConnection_origin]
      rfl]
  rw [show positiveDiracDualCartanReactionLocalActual.gravityConnection 0 =
      fixedActionCartanConnection by
        change
          positiveDiracDualCartanConnectionLocalActual.gravityConnection 0 = _
        exact positiveDiracDualCartanConnectionLocalActual_originConnection]
  rw [positiveDiracDualCartan_spinLift_one]
  simp

theorem positiveDiracDualCartanReactionECContactField_derivative_two :
    positiveDiracDualCartanReactionECContactField.matterCovariantDerivative 2 =
      0 := by
  change
    holonomicMatterCovariantDerivative
        positiveDiracDualCartanReactionLocalActual 0 2 = 0
  unfold holonomicMatterCovariantDerivative
  rw [show fieldDirectionalDerivative
      (fun candidate => matterCoordinateEquiv
        (positiveDiracDualCartanReactionLocalActual.matter candidate))
      0 2 = 0 by
        simpa using positiveDiracDualCartanReaction_rawDerivative_spatial 1]
  rw [show positiveDiracDualCartanReactionLocalActual.matter 0 =
      diracSpinTwoMatterProbe by
        change
          (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
            positiveSourceTargetMatterCauchyState 0).matter 0 = _
        rw [sourceActionGeneratedJointLocalActualLift_initialMatter]
        exact positiveSourceTargetMatterCauchyState_matter]
  rw [show positiveDiracDualCartanReactionLocalActual.gaugeConnection 0 = 0 by
      funext formDirection
      change
        sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
            positiveSourceTargetMatterCauchyState 0 0 formDirection = 0
      rw [sourceGeneratedP286ActionLocalConnection_origin]
      rfl]
  rw [show positiveDiracDualCartanReactionLocalActual.gravityConnection 0 =
      fixedActionCartanConnection by
        change
          positiveDiracDualCartanConnectionLocalActual.gravityConnection 0 = _
        exact positiveDiracDualCartanConnectionLocalActual_originConnection]
  rw [positiveDiracDualCartan_spinLift_two]
  simp

def positiveDiracDualCartanReactionSpatialKineticVector :
    DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ axis : Fin 3,
      diracMatrixMatterAction (diracGamma axis.succ)
        (positiveDiracDualCartanReactionECContactField
          |>.matterCovariantDerivative axis.succ)

theorem positiveDiracDualCartanReactionSpatialKineticPairing :
    (diracSpinZeroMatterCoordinate
      positiveDiracDualCartanReactionSpatialKineticVector).re =
      -(1 / 8 : ℝ) := by
  unfold positiveDiracDualCartanReactionSpatialKineticVector
  simp [Fin.sum_univ_three,
    positiveDiracDualCartanReactionECContactField_derivative_one,
    positiveDiracDualCartanReactionECContactField_derivative_two,
    positiveDiracDualCartanReactionECContactField_derivative_three,
    diracMatrixMatterAction, diracSpinZeroMatterCoordinate,
    diracSpinTwoMatterProbe,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    Fin.sum_univ_four]

/-! ## Temporal-dilation path for the single independent row -/

def kinEightTemporalDilationVariation : LorentzianCoframe :=
  coframeCoordinateDirection 0 0

def kinEightTemporalDilationPath (parameter : ℝ) : LorentzianCoframe :=
  (1 : LorentzianCoframe) +
    parameter • kinEightTemporalDilationVariation

theorem kinEightTemporalDilationPath_eq_diagonal (parameter : ℝ) :
    kinEightTemporalDilationPath parameter =
      Matrix.diagonal ![(1 + parameter : ℝ), 1, 1, 1] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [kinEightTemporalDilationPath,
      kinEightTemporalDilationVariation, coframeCoordinateDirection]

@[simp] theorem kinEightTemporalDilationPath_det (parameter : ℝ) :
    Matrix.det (kinEightTemporalDilationPath parameter) = 1 + parameter := by
  rw [kinEightTemporalDilationPath_eq_diagonal, Matrix.det_diagonal]
  simp [Fin.prod_univ_four]

theorem kinEightTemporalDilationPath_inv
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0) :
    (kinEightTemporalDilationPath parameter)⁻¹ =
      Matrix.diagonal ![(1 + parameter)⁻¹, 1, 1, 1] := by
  apply Matrix.inv_eq_left_inv
  rw [kinEightTemporalDilationPath_eq_diagonal]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, nonzero]

theorem inverseCoframeDiracGamma_kinEightTemporalDilationPath
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0)
    (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := kinEightTemporalDilationPath parameter,
          derivative := 0 }
        direction =
      ![((((1 + parameter)⁻¹ : ℝ) : ℂ) • diracGamma 0),
        diracGamma 1, diracGamma 2, diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [kinEightTemporalDilationPath_inv parameter nonzero]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.diagonal_apply, diracGamma,
      diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree]

def positiveDiracDualCartanReactionTemporalKineticVector :
    DiracExteriorMatterCarrier :=
  Complex.I •
    diracMatrixMatterAction (diracGamma 0)
      (positiveDiracDualCartanReactionECContactField
        |>.matterCovariantDerivative 0)

def positiveDiracDualCartanReactionTemporalKineticPairing : ℝ :=
  (diracSpinZeroMatterCoordinate
    positiveDiracDualCartanReactionTemporalKineticVector).re

theorem
    positiveDiracDualCartanReaction_generatedKineticVector_temporalDilation
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0) :
    generatedContinuumMatterKineticVector positiveSmoothUnifiedSource 0 0
        (withCoframe positiveDiracDualCartanReactionECContactField
          (kinEightTemporalDilationPath parameter)) =
      ((((1 + parameter)⁻¹ : ℝ) : ℂ) •
          positiveDiracDualCartanReactionTemporalKineticVector) +
        positiveDiracDualCartanReactionSpatialKineticVector := by
  unfold generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart]
  simp_rw [inverseCoframeDiracGamma_kinEightTemporalDilationPath
    parameter nonzero]
  unfold positiveDiracDualCartanReactionTemporalKineticVector
    positiveDiracDualCartanReactionSpatialKineticVector
  simp [Fin.sum_univ_four, Fin.sum_univ_three,
    diracMatrixMatterAction_smul_matrix]
  module

theorem positiveDiracDualCartanReaction_yukawaDensity_zero
    (coframe : LorentzianCoframe) :
    generatedDensitizedContinuumDiracDualYukawaDensity
        positiveSmoothUnifiedSource 0 0
        (withCoframe positiveDiracDualCartanReactionECContactField coframe) =
      0 := by
  unfold generatedDensitizedContinuumDiracDualYukawaDensity
    generatedContinuumDiracDualYukawaVector
  simp only [withCoframe, matterDualFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart, matterFrameRelative_zeroChart]
  rw [positiveDiracDualCartanReactionECContactField_conjugateMatter,
    positiveDiracDualCartanReactionECContactField_matter,
    diracSpinZeroMatterCoordinate_diracDualRightChiralYukawaAction_eq_zero]
  simp

theorem positiveDiracDualCartanReaction_kineticDensity_temporalDilation
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0)
    (positive : 0 < 1 + parameter) :
    generatedDensitizedContinuumMatterKineticDensity
        positiveSmoothUnifiedSource 0 0
        (withCoframe positiveDiracDualCartanReactionECContactField
          (kinEightTemporalDilationPath parameter)) =
      positiveDiracDualCartanReactionTemporalKineticPairing +
        (1 + parameter) * (-(1 / 8 : ℝ)) := by
  unfold generatedDensitizedContinuumMatterKineticDensity
  rw [positiveDiracDualCartanReaction_generatedKineticVector_temporalDilation
    parameter nonzero]
  simp only [withCoframe, matterDualFrameRelative_zeroChart]
  rw [positiveDiracDualCartanReactionECContactField_conjugateMatter]
  simp only [map_add, map_smul, Complex.add_re, Complex.coe_smul,
    Complex.smul_re]
  unfold generatedVolumeDensity
  rw [kinEightTemporalDilationPath_det, abs_of_pos positive]
  unfold positiveDiracDualCartanReactionTemporalKineticPairing
  rw [positiveDiracDualCartanReactionSpatialKineticPairing]
  simp only [smul_eq_mul]
  rw [show
    (1 + parameter) *
        ((1 + parameter)⁻¹ *
            (diracSpinZeroMatterCoordinate
              positiveDiracDualCartanReactionTemporalKineticVector).re +
          -(1 / 8 : ℝ)) =
      ((1 + parameter) * (1 + parameter)⁻¹) *
          (diracSpinZeroMatterCoordinate
            positiveDiracDualCartanReactionTemporalKineticVector).re +
        (1 + parameter) * (-(1 / 8 : ℝ)) by ring]
  rw [mul_inv_cancel₀ nonzero]
  ring

private theorem kinEightTemporalDilationPath_positive_eventually :
    ∀ᶠ parameter : ℝ in nhds 0, 0 < 1 + parameter := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
      (show (0 : ℝ) < 1 by norm_num)] with parameter inBall
  have absLt : |parameter| < 1 := by
    simpa [Real.dist_eq] using inBall
  rcases abs_lt.mp absLt with ⟨lower, _upper⟩
  linarith

theorem positiveDiracDualCartanReaction_matterDensity_temporalDilation
    (parameter : ℝ) (positive : 0 < 1 + parameter) :
    diracDualFormNativeCoframeMatterDensity positiveSmoothUnifiedSource 0
        positiveDiracDualCartanReactionECContactField
        (kinEightTemporalDilationPath parameter) =
      positiveDiracDualCartanReactionTemporalKineticPairing +
        (1 + parameter) * (-(1 / 8 : ℝ)) := by
  have nonzero : 1 + parameter ≠ 0 := positive.ne'
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  rw [positiveDiracDualCartanReactionECContactField_scalarDensity_zero,
    positiveDiracDualCartanReaction_kineticDensity_temporalDilation
      parameter nonzero positive,
    positiveDiracDualCartanReaction_yukawaDensity_zero]
  ring

theorem positiveDiracDualCartanReaction_matterDensity_path_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeMatterDensity positiveSmoothUnifiedSource 0
          positiveDiracDualCartanReactionECContactField
          (kinEightTemporalDilationPath parameter))
      (-(1 / 8 : ℝ)) 0 := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have onePlusDerivative := identityDerivative.const_add (1 : ℝ)
  have scaledDerivative :=
    onePlusDerivative.mul_const (-(1 / 8 : ℝ))
  have affineDerivative :=
    scaledDerivative.const_add
      positiveDiracDualCartanReactionTemporalKineticPairing
  have eventualEquality :
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeMatterDensity positiveSmoothUnifiedSource 0
          positiveDiracDualCartanReactionECContactField
          (kinEightTemporalDilationPath parameter)) =ᶠ[nhds 0]
        (fun parameter : ℝ =>
          positiveDiracDualCartanReactionTemporalKineticPairing +
            (1 + parameter) * (-(1 / 8 : ℝ))) := by
    filter_upwards [kinEightTemporalDilationPath_positive_eventually]
        with parameter positive
    exact positiveDiracDualCartanReaction_matterDensity_temporalDilation
      parameter positive
  simpa only [one_mul, id_eq] using
    affineDerivative.congr_of_eventuallyEq eventualEquality

theorem positiveDiracDualCartanReaction_matterEuler_zero :
    diracDualFormNativeCoframeMatterEulerCovector positiveSmoothUnifiedSource 0
        positiveDiracDualCartanReactionECContactField
        kinEightTemporalDilationVariation =
      -(1 / 8 : ℝ) := by
  have nondegenerate :
      Matrix.det positiveDiracDualCartanReactionECContactField.coframe ≠ 0 := by
    rw [positiveDiracDualCartanReactionECContactField_coframe]
    simp
  have outer :=
    diracDualFormNativeCoframeMatterDensity_hasFDerivAt
      positiveSmoothUnifiedSource 0
      positiveDiracDualCartanReactionECContactField nondegenerate
  rw [positiveDiracDualCartanReactionECContactField_coframe] at outer
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have variationDerivative :=
    identityDerivative.smul_const kinEightTemporalDilationVariation
  have variationDerivativeValue :
      (1 : ℝ) • kinEightTemporalDilationVariation =
        kinEightTemporalDilationVariation := by
    simp
  have variationDerivativeAtZero :=
    variationDerivative.congr_deriv variationDerivativeValue
  have pathDerivative :=
    variationDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have baseEquality :
      (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) +
          (0 : ℝ) • kinEightTemporalDilationVariation := by
    simp
  have composed :=
    outer.comp_hasDerivAt_of_eq 0 pathDerivative baseEquality
  exact composed.unique (by
    simpa [kinEightTemporalDilationPath, Function.comp_def] using
      positiveDiracDualCartanReaction_matterDensity_path_hasDerivAt)

/-! ## Independent KIN-8 reduced EC constraint obstruction -/

theorem positiveDiracDualCartanReaction_loadConstraint_zero :
    identityECConstraintCoordinatesOfCovector
        (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
          positiveDiracDualCartanReactionLocalActual) 0 =
      -(25 / 8 : ℝ) := by
  unfold identityECConstraintCoordinatesOfCovector
    diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  change
    identityDiracDualECConstraintObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) 0 +
        diracDualFormNativeCoframeGaugeEulerCovector
            positiveSmoothUnifiedSource
            positiveDiracDualCartanReactionECContactField
            (coframeCoordinateDirection 0 0) +
      diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0
          positiveDiracDualCartanReactionECContactField
          (coframeCoordinateDirection 0 0) =
      -(25 / 8 : ℝ)
  rw [congrFun identityDiracDualECIntrinsicConstraintObservation 0,
    positiveDiracDualCartanReactionECContactField_gaugeEuler_zero]
  change
    (-3 : ℝ) + 0 +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0
          positiveDiracDualCartanReactionECContactField
          kinEightTemporalDilationVariation =
      -(25 / 8 : ℝ)
  rw [positiveDiracDualCartanReaction_matterEuler_zero]
  norm_num

/-- The four-row constraint carrier transported by the Cauchy evolution
write, read directly on its KIN-8 input actual. -/
def positiveDiracDualCartanReactionECConstraintResidual : Fin 4 → ℝ :=
  identityDiracDualECConstraintObservation
      (diracDualFormNativeECCauchyCurrentCurvature
        positiveDiracDualCartanReactionLocalActual) +
    identityECConstraintCoordinatesOfCovector
      (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        positiveDiracDualCartanReactionLocalActual)

/-- Direct Cauchy-row adjudication: `1/8 - 25/8 = -3`.  This is an
independent failure control for KIN-8, not producer soundness for KIN-9. -/
theorem positiveDiracDualCartanReactionECConstraintResidual_zero :
    positiveDiracDualCartanReactionECConstraintResidual 0 = -3 := by
  unfold positiveDiracDualCartanReactionECConstraintResidual
  simp only [Pi.add_apply]
  rw [positiveDiracDualCartanReaction_curvatureConstraint_zero,
    positiveDiracDualCartanReaction_loadConstraint_zero]
  norm_num

theorem positiveDiracDualCartanReactionECConstraintResidual_ne_zero :
    positiveDiracDualCartanReactionECConstraintResidual ≠ 0 := by
  intro residualZero
  have coordinateZero := congrFun residualZero 0
  rw [positiveDiracDualCartanReactionECConstraintResidual_zero] at coordinateZero
  norm_num at coordinateZero

/-! ## Transport to the positive KIN-10 output -/

/-- The independent constraint carrier read back from the generated KIN-10
output actual. -/
def positiveDiracDualECCauchyConnectionECConstraintResidual : Fin 4 → ℝ :=
  identityDiracDualECConstraintObservation
      (holonomicGravityCurvature
        positiveDiracDualECCauchyConnectionLocalActual 0) +
    identityECConstraintCoordinatesOfCovector
      (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        positiveDiracDualECCauchyConnectionLocalActual)

/-- KIN-10 solves only the twelve evolution rows; it faithfully transports
the independent KIN-8 constraint carrier. -/
theorem positiveDiracDualECCauchyConnectionECConstraintResidual_eq_input :
    positiveDiracDualECCauchyConnectionECConstraintResidual =
      positiveDiracDualCartanReactionECConstraintResidual := by
  exact positiveDiracDualECCauchyConnectionLocalActual_outputConstraintResidual

theorem positiveDiracDualECCauchyConnectionECConstraintResidual_zero :
    positiveDiracDualECCauchyConnectionECConstraintResidual 0 = -3 := by
  rw [positiveDiracDualECCauchyConnectionECConstraintResidual_eq_input,
    positiveDiracDualCartanReactionECConstraintResidual_zero]

theorem positiveDiracDualECCauchyConnectionECConstraintResidual_ne_zero :
    positiveDiracDualECCauchyConnectionECConstraintResidual ≠ 0 := by
  rw [positiveDiracDualECCauchyConnectionECConstraintResidual_eq_input]
  exact positiveDiracDualCartanReactionECConstraintResidual_ne_zero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECCauchyConstraintObstructionRegression
