import H0mework.Physics.JointVariation.GlobalDevelopmentFixedP286Compatibility
import H0mework.Physics.ElectricEC.FixedMatterScalarDeltas
import H0mework.Physics.ElectricEC.FixedOriginPhysicalRetention
import H0mework.Physics.ElectricEC.FixedOriginTransport
import H0mework.Physics.FixedJoint.FixedConstitutiveZeroFiber
import H0mework.Physics.DualVariation.P286CanonicalJointActionFirstGerm
import H0mework.Physics.Lorentz.LorentzConnectionVariation

/-!
# Fixed P506/L0 P286-algebraic matter--scalar delta

This module identifies the genuine read-after-write edge from the fixed
complete-joint temporal current to its action-generated algebraic P286
successor.  The successor is first identified with the generic canonical
joint candidate carrying the already generated fixed write.  Its scalar
covariant derivative and differential momentum then inherit the canonical
quadratic normal form at every spacetime point.

The post-write action equation is never used to claim that the pre-write
forcing or generated write vanishes.  The fixed write is instead transported
from an independently generated constitutive fixed point with the same six
action-data fields, whose native P286 Euler equation is already proved.
No residual coordinate, support branch, target field, or equation receipt
enters either producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECResidualTelescoping
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECMatterScalarDeltas
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginPhysicalRetention
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveZeroFiber
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeP286CanonicalJointActionFirstGerm
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeScalarVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterPointwiseEquation
open StageNineMatterCovariantDerivativeAffine
open StageNineP286ActionCauchySplit
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineLorentzConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineScalarPointwiseEquation
open StageNineTopologicalP286GaugeThreeFormDuality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource FixedInput

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
    FixedInput

private abbrev FixedWrite : P286GaugeOneForm :=
  fixedP506L0P286CanonicalGeneratedWrite

private abbrev Final : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev Constitutive : StageNineHolonomicConfiguration :=
  FixedP506FormNativeConstitutiveJointActionSuccessor

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-! ## Native fixed-write zero theorem -/

/-- The independently generated constitutive successor is a fixed point of
the canonical P286 candidate at zero response. -/
private theorem constitutive_is_zero_candidate :
    diracDualFormNativeP286CanonicalJointCandidate
        positiveSmoothUnifiedSource Constitutive 0 =
      Constitutive := by
  rw [diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  apply StageNineHolonomicConfiguration.ext <;>
    simp [formNativeP286GaugeConstitutiveReadout, Constitutive]
  rw [
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeAuxiliary]
  funext point
  unfold fixedP506FormNativeConstitutiveAuxiliaryField
  rw [
    fixedP506FormNativeConstitutiveJointActionSuccessor_coframe,
    fixedP506FormNativeConstitutiveJointActionSuccessor_curvature]

/-- The constitutive fixed point's native P286 Euler zero generates the zero
canonical write.  This direction is producer-sound: it does not infer a write
from a post-write acceptance equation. -/
private theorem constitutive_p286CanonicalGeneratedWrite_zero :
    diracDualFormNativeP286CanonicalGeneratedWrite
        positiveSmoothUnifiedSource Constitutive =
      0 := by
  apply p286GaugeOneFormPairingEquiv.injective
  unfold diracDualFormNativeP286CanonicalGeneratedWrite
  rw [p286GaugeOneFormPairingEquiv.apply_symm_apply, map_zero]
  unfold diracDualFormNativeP286CanonicalOriginActionForcing
    diracDualFormNativeP286CanonicalOriginActionDual
  rw [constitutive_is_zero_candidate]
  have eulerZero :
      StageNineFormNativeP286GaugeGeometricFirstVariation.holonomicFormNativeP286GaugeEulerThreeForm
          positiveSmoothUnifiedSource 0 Constitutive 0 =
        0 := by
    change
      (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection 0
        ).p286GaugeConnection = 0
    exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_origin_zero
  rw [eulerZero]
  exact (p286GaugeThreeFormWedgeLinearDual_eq_zero_iff 0).2 rfl

/-- The fixed temporal current and the constitutive fixed point present the
same six action-data fields to the canonical P286 producer. -/
private theorem temporal_p286CanonicalGeneratedWrite_eq_constitutive :
    diracDualFormNativeP286CanonicalGeneratedWrite
        positiveSmoothUnifiedSource Temporal =
      diracDualFormNativeP286CanonicalGeneratedWrite
        positiveSmoothUnifiedSource Constitutive := by
  apply diracDualFormNativeP286CanonicalGeneratedWrite_eq_of_actionData_eq
  · change
      (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
        FixedInput).coframe =
        Constitutive.coframe
    rw [completeJointGlobalTemporalCurrent,
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe,
      fixedP506FormNativeConstitutiveJointActionSuccessor_coframe]
  · rfl
  · calc
      Temporal.scalar 0 =
          FixedInput.scalar 0 := by
        simpa [Temporal, completeJointGlobalTemporalCurrent,
          canonicalCauchySlicePoint_zero_zero] using
          sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
            positiveSmoothUnifiedSource FixedInput
              (0 : StageNineSpatialPoint)
      _ = Constitutive.scalar 0 := by
        rw [fixedP506FormNativeConstitutiveJointActionSuccessor_scalar]
  · calc
      holonomicScalarCovariantDerivative Temporal 0 =
          holonomicScalarCovariantDerivative FixedInput 0 :=
        fixedP506L0CompleteJointGlobalTemporalCurrent_scalarCovariantDerivative_origin_eq_solved
      _ = holonomicScalarCovariantDerivative Constitutive 0 := by
        funext direction
        unfold holonomicScalarCovariantDerivative
        rw [
          fixedP506FormNativeConstitutiveJointActionSuccessor_scalar,
          fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]
  · calc
      Temporal.matter 0 =
          FixedInput.matter 0 := by
        simpa [Temporal, completeJointGlobalTemporalCurrent,
          canonicalCauchySlicePoint_zero_zero] using
          sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
            positiveSmoothUnifiedSource FixedInput
              (0 : StageNineSpatialPoint)
      _ = Constitutive.matter 0 :=
        fixedP506FormNativeConstitutiveJointActionSuccessor_matter_origin.symm
  · calc
      Temporal.conjugateMatter 0 =
          FixedInput.conjugateMatter 0 := by
        simpa [Temporal, completeJointGlobalTemporalCurrent,
          canonicalCauchySlicePoint_zero_zero] using
          sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
            positiveSmoothUnifiedSource FixedInput
              (0 : StageNineSpatialPoint)
      _ = Constitutive.conjugateMatter 0 :=
        fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter_origin.symm

/-- The fixed P506/L0 canonical P286 response is exactly zero, by native
action generation plus six-field action-data transport. -/
theorem fixedP506L0P286CanonicalGeneratedWrite_zero :
    FixedWrite = 0 := by
  calc
    FixedWrite =
        diracDualFormNativeP286CanonicalGeneratedWrite
          positiveSmoothUnifiedSource Temporal :=
      fixedP506L0CompleteJointGlobalTemporalCurrent_p286CanonicalGeneratedWrite.symm
    _ =
        diracDualFormNativeP286CanonicalGeneratedWrite
          positiveSmoothUnifiedSource Constitutive :=
      temporal_p286CanonicalGeneratedWrite_eq_constitutive
    _ = 0 := constitutive_p286CanonicalGeneratedWrite_zero

/-! ## Exact action-candidate identification -/

/-- The algebraic P286 leg is literally the generic canonical joint
candidate on the temporal current with the already generated fixed write.
This is the bridge that permits all generic canonical increment laws to be
consumed without replacing the fixed source/current producer. -/
theorem fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_candidate :
    Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate
        positiveSmoothUnifiedSource Temporal FixedWrite := by
  change
    diracDualFormNativeP286CanonicalGeneratedActual
        positiveSmoothUnifiedSource Temporal =
      diracDualFormNativeP286CanonicalJointCandidate
        positiveSmoothUnifiedSource Temporal FixedWrite
  unfold diracDualFormNativeP286CanonicalGeneratedActual
  rw [
    fixedP506L0CompleteJointGlobalTemporalCurrent_p286CanonicalGeneratedWrite]

/-- The fixed algebraic current is therefore the zero-response candidate,
with no residual coordinate used to select that value. -/
theorem fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate :
    Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate
        positiveSmoothUnifiedSource Temporal 0 := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_candidate,
    fixedP506L0P286CanonicalGeneratedWrite_zero]

private theorem algebraic_coframe_eq_temporal :
    Algebraic.coframe = Temporal.coframe := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rfl

private theorem algebraic_gravityConnection_eq_temporal :
    Algebraic.gravityConnection = Temporal.gravityConnection := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rfl

private theorem algebraic_gaugeConnection_eq_temporal :
    Algebraic.gaugeConnection = Temporal.gaugeConnection := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate,
    diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rfl

private theorem algebraic_scalar_eq_temporal :
    Algebraic.scalar = Temporal.scalar := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rfl

private theorem algebraic_matter_eq_temporal :
    Algebraic.matter = Temporal.matter := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rfl

private theorem algebraic_conjugateMatter_eq_temporal :
    Algebraic.conjugateMatter = Temporal.conjugateMatter := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rfl

private theorem algebraic_scalarCovariantDerivative_eq_temporal :
    holonomicScalarCovariantDerivative Algebraic =
      holonomicScalarCovariantDerivative Temporal := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [algebraic_scalar_eq_temporal, algebraic_gaugeConnection_eq_temporal]

private theorem algebraic_matterCovariantDerivative_eq_temporal :
    holonomicMatterCovariantDerivative Algebraic =
      holonomicMatterCovariantDerivative Temporal := by
  funext point direction
  unfold holonomicMatterCovariantDerivative
  rw [algebraic_matter_eq_temporal,
    algebraic_gravityConnection_eq_temporal,
    algebraic_gaugeConnection_eq_temporal]

/-! ## All-point scalar connection normal form -/

/-- At every spacetime point, the only new scalar covariant-derivative term
is the canonical quadratic connection increment generated by the same fixed
action write. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative
    (point : BasePoint) :
    holonomicScalarCovariantDerivative Algebraic point =
      holonomicScalarCovariantDerivative Temporal point +
        canonicalScalarCovariantIncrement Temporal FixedWrite point := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_candidate]
  exact
    canonicalJointCandidate_scalarCovariantDerivative_expansion
      Temporal FixedWrite point

/-- The scalar differential momentum after the P286 algebraic leg is the
temporal momentum plus the unique momentum increment induced by that same
canonical quadratic connection write. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarDifferentialMomentum
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource Algebraic
        direction derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource Temporal
          direction derivativeDirection +
        canonicalScalarMomentumIncrement Temporal FixedWrite direction
          derivativeDirection := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_candidate]
  exact
    canonicalJointCandidate_scalarDifferentialMomentum_eq
      Temporal FixedWrite direction derivativeDirection

/-- Exact all-point divergence normal form.  It deliberately keeps the
derivative on the generated momentum sum, so it remains valid under Lean's
canonical `fderiv = 0` convention even before any global smoothness theorem
is consumed. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarMomentumDivergence
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        Algebraic direction point =
      ∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative
          (fun candidate =>
            scalarDifferentialMomentum positiveSmoothUnifiedSource Temporal
                direction derivativeDirection candidate +
              canonicalScalarMomentumIncrement Temporal FixedWrite direction
                derivativeDirection candidate)
          point derivativeDirection := by
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarDifferentialMomentum]
  change
    fieldDirectionalDerivative
        (fun candidate =>
          scalarDifferentialMomentum positiveSmoothUnifiedSource Temporal
              direction derivativeDirection candidate +
            canonicalScalarMomentumIncrement Temporal FixedWrite direction
              derivativeDirection candidate)
        point derivativeDirection =
      _
  rfl

/-! ## Complete U1 -> U2 changed reads -/

/-- The exact scalar changed-read normal form.  Its first line is the
pointwise algebraic response to the canonical connection write; its second
line is the corresponding generated momentum-divergence change.  No
smoothness assumption or residual-derived correction is hidden in this
identity. -/
theorem fixedP506L0_scalar_p286Algebraic_delta_normalForm
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0ScalarEulerRead point) Temporal Algebraic =
      fun direction =>
        (diracDualScalarAlgebraicDirectionalCoefficient
            positiveSmoothUnifiedSource Algebraic direction point -
          diracDualScalarAlgebraicDirectionalCoefficient
            positiveSmoothUnifiedSource Temporal direction point) -
        ((∑ derivativeDirection : LorentzianIndex,
            fieldDirectionalDerivative
              (fun candidate =>
                scalarDifferentialMomentum positiveSmoothUnifiedSource
                    Temporal direction derivativeDirection candidate +
                  canonicalScalarMomentumIncrement Temporal FixedWrite
                    direction derivativeDirection candidate)
              point derivativeDirection) -
          scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
            Temporal direction point) := by
  funext direction
  unfold completeJointLiveElectricECReadDelta fixedP506L0ScalarEulerRead
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient
          positiveSmoothUnifiedSource Algebraic direction point -
        diracDualScalarEulerLagrangeDirectionalCoefficient
          positiveSmoothUnifiedSource Temporal direction point =
      _
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarMomentumDivergence]
  ring

/-- A canonical P286 connection write preserves the primal-matter
differential-momentum divergence as a whole field.  Hence the complete
primal changed read is purely the difference of the two action-algebraic
coefficients on the same U1 -> U2 edge. -/
theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matterMomentumDivergence
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        Algebraic direction =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        Temporal direction := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_candidate]
  exact
    canonicalJointCandidate_matterDifferentialMomentumDivergence_eq
      Temporal FixedWrite direction

theorem fixedP506L0_matter_p286Algebraic_delta_normalForm
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0MatterEulerRead point) Temporal Algebraic =
      fun direction =>
        diracDualMatterAlgebraicDirectionalCoefficient
            positiveSmoothUnifiedSource Algebraic direction point -
          diracDualMatterAlgebraicDirectionalCoefficient
            positiveSmoothUnifiedSource Temporal direction point := by
  funext direction
  unfold completeJointLiveElectricECReadDelta fixedP506L0MatterEulerRead
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient
          positiveSmoothUnifiedSource Algebraic direction point -
        diracDualMatterEulerLagrangeDirectionalCoefficient
          positiveSmoothUnifiedSource Temporal direction point =
      _
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [congrFun
    (fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matterMomentumDivergence
      direction) point]
  ring

/-- The adjoint Euler coefficient is already pointwise algebraic, so its
U1 -> U2 changed read is exactly the action-vector difference caused by the
same canonical P286 connection write. -/
theorem fixedP506L0_conjugateMatter_p286Algebraic_delta_normalForm
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0ConjugateMatterEulerRead point) Temporal Algebraic =
      fun direction =>
        diracDualConjugateMatterDirectionalCoefficient
            positiveSmoothUnifiedSource Algebraic direction point -
          diracDualConjugateMatterDirectionalCoefficient
            positiveSmoothUnifiedSource Temporal direction point := by
  rfl

/-! ## All-point zero settlement of the P286 algebraic edge -/

private theorem algebraic_scalarDifferentialMomentum_eq_temporal
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource Algebraic direction
        derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource Temporal direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [algebraic_coframe_eq_temporal,
    algebraic_scalarCovariantDerivative_eq_temporal]

private theorem algebraic_scalarMomentumDivergence_eq_temporal
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        Algebraic direction =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        Temporal direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [algebraic_scalarDifferentialMomentum_eq_temporal]

private theorem algebraic_scalarAlgebraic_eq_temporal
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource Algebraic direction point =
      diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource Temporal direction point := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarVariationAlgebraicDirection generatedVolumeDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
  simp only [toContinuumPointField]
  rw [algebraic_coframe_eq_temporal,
    algebraic_scalarCovariantDerivative_eq_temporal,
    algebraic_gaugeConnection_eq_temporal,
    algebraic_scalar_eq_temporal,
    algebraic_matter_eq_temporal,
    algebraic_conjugateMatter_eq_temporal]

/-- The action-generated zero P286 write leaves the scalar Euler read fixed
at every spacetime point. -/
theorem fixedP506L0_scalar_p286Algebraic_delta_zero
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0ScalarEulerRead point) Temporal Algebraic =
      0 := by
  unfold completeJointLiveElectricECReadDelta
  rw [sub_eq_zero]
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource Algebraic direction point =
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource Temporal direction point
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [algebraic_scalarAlgebraic_eq_temporal,
    congrFun (algebraic_scalarMomentumDivergence_eq_temporal direction) point]

private theorem algebraic_matterAlgebraic_eq_temporal
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    diracDualMatterAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource Algebraic direction point =
      diracDualMatterAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource Temporal direction point := by
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    holonomicMatterVariationAlgebraicDirection generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [algebraic_coframe_eq_temporal,
    algebraic_gravityConnection_eq_temporal,
    algebraic_gaugeConnection_eq_temporal,
    algebraic_scalar_eq_temporal,
    algebraic_conjugateMatter_eq_temporal]

/-- The same zero write leaves the primal-matter Euler read fixed globally. -/
theorem fixedP506L0_matter_p286Algebraic_delta_zero
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0MatterEulerRead point) Temporal Algebraic =
      0 := by
  rw [fixedP506L0_matter_p286Algebraic_delta_normalForm]
  funext direction
  rw [algebraic_matterAlgebraic_eq_temporal]
  simp

private theorem algebraic_conjugateMatterCoefficient_eq_temporal
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    diracDualConjugateMatterDirectionalCoefficient
        positiveSmoothUnifiedSource Algebraic direction point =
      diracDualConjugateMatterDirectionalCoefficient
        positiveSmoothUnifiedSource Temporal direction point := by
  unfold diracDualConjugateMatterDirectionalCoefficient
    generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [algebraic_coframe_eq_temporal,
    algebraic_scalar_eq_temporal,
    algebraic_matter_eq_temporal,
    algebraic_matterCovariantDerivative_eq_temporal]

/-- The same zero write leaves the adjoint-matter Euler read fixed globally. -/
theorem fixedP506L0_conjugateMatter_p286Algebraic_delta_zero
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0ConjugateMatterEulerRead point) Temporal Algebraic =
      0 := by
  rw [fixedP506L0_conjugateMatter_p286Algebraic_delta_normalForm]
  funext direction
  rw [algebraic_conjugateMatterCoefficient_eq_temporal]
  simp

/-! ## Direct final-U5 collapse -/

private theorem final_coframe_eq_algebraic :
    Final.coframe = Algebraic.coframe :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC.trans
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe
      positiveSmoothUnifiedSource FixedInput)

private theorem final_conjugateMatter_eq_algebraic :
    Final.conjugateMatter = Algebraic.conjugateMatter :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC.trans
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter
      positiveSmoothUnifiedSource FixedInput)

private theorem final_matterDifferentialMomentum_eq_algebraic
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource Final direction
        derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource Algebraic
        direction derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [final_coframe_eq_algebraic, final_conjugateMatter_eq_algebraic]

/-- All three connection-sensitive downstream legs preserve the primitive
inputs of the matter differential momentum.  Combined with the canonical
U1 -> U2 law, the final U5 divergence is exactly the U1 divergence. -/
theorem fixedP506L0_final_matterMomentumDivergence_eq_temporal
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        Final direction =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        Temporal direction := by
  calc
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
          Final direction =
        matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
          Algebraic direction := by
      funext point
      unfold matterDifferentialMomentumDivergence
      simp_rw [final_matterDifferentialMomentum_eq_algebraic]
    _ = matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
          Temporal direction :=
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matterMomentumDivergence
        direction

/-- The total primal-matter changed read from its native U1 settlement to
the final U5 actual is a single algebraic connection-action difference.
Thus the P286, Cartan, and EC deltas are collapsed together rather than
treated as three repair epochs. -/
theorem fixedP506L0_matter_final_delta_normalForm
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0MatterEulerRead point) Temporal Final =
      fun direction =>
        diracDualMatterAlgebraicDirectionalCoefficient
            positiveSmoothUnifiedSource Final direction point -
          diracDualMatterAlgebraicDirectionalCoefficient
            positiveSmoothUnifiedSource Temporal direction point := by
  funext direction
  unfold completeJointLiveElectricECReadDelta fixedP506L0MatterEulerRead
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient
          positiveSmoothUnifiedSource Final direction point -
        diracDualMatterEulerLagrangeDirectionalCoefficient
          positiveSmoothUnifiedSource Temporal direction point =
      _
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [congrFun
    (fixedP506L0_final_matterMomentumDivergence_eq_temporal direction) point]
  ring

/-- The total adjoint changed read from U1 to U5 is already the literal
pointwise Dirac--Yukawa action-vector difference. -/
theorem fixedP506L0_conjugateMatter_final_delta_normalForm
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0ConjugateMatterEulerRead point) Temporal Final =
      fun direction =>
        diracDualConjugateMatterDirectionalCoefficient
            positiveSmoothUnifiedSource Final direction point -
          diracDualConjugateMatterDirectionalCoefficient
            positiveSmoothUnifiedSource Temporal direction point := by
  rfl

/-- Final U5 scalar read in the unique U1 -> U2 canonical quadratic normal
form.  The live-electric, Cartan, and EC suffix has already been proved
silent for this reader. -/
theorem fixedP506L0_scalar_final_normalForm
    (point : BasePoint) :
    fixedP506L0ScalarEulerRead point Final =
      fixedP506L0ScalarEulerRead point Temporal +
        (fun direction =>
          (diracDualScalarAlgebraicDirectionalCoefficient
              positiveSmoothUnifiedSource Algebraic direction point -
            diracDualScalarAlgebraicDirectionalCoefficient
              positiveSmoothUnifiedSource Temporal direction point) -
          ((∑ derivativeDirection : LorentzianIndex,
              fieldDirectionalDerivative
                (fun candidate =>
                  scalarDifferentialMomentum positiveSmoothUnifiedSource
                      Temporal direction derivativeDirection candidate +
                    canonicalScalarMomentumIncrement Temporal FixedWrite
                      direction derivativeDirection candidate)
                point derivativeDirection) -
            scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
              Temporal direction point)) := by
  calc
    fixedP506L0ScalarEulerRead point Final =
        fixedP506L0ScalarEulerRead point Temporal +
          completeJointLiveElectricECReadDelta
            (fixedP506L0ScalarEulerRead point) Temporal Algebraic := by
      have actual :=
        fixedP506L0_scalar_final_eq_matterScalar_native_add_p286AlgebraicDelta
          point
      change
        fixedP506L0ScalarEulerRead point Final =
          fixedP506L0ScalarEulerRead point Temporal +
            completeJointLiveElectricECReadDelta
              (fixedP506L0ScalarEulerRead point) Temporal Algebraic
        at actual
      exact actual
    _ = _ := by
      rw [fixedP506L0_scalar_p286Algebraic_delta_normalForm]

/-- The entire P286/live-electric/Cartan/EC suffix is silent for the scalar
Euler reader: the final actual has exactly the native temporal scalar read at
every spacetime point. -/
theorem fixedP506L0_scalar_final_eq_temporal
    (point : BasePoint) :
    fixedP506L0ScalarEulerRead point Final =
      fixedP506L0ScalarEulerRead point Temporal := by
  calc
    fixedP506L0ScalarEulerRead point Final =
        fixedP506L0ScalarEulerRead point Temporal +
          completeJointLiveElectricECReadDelta
            (fixedP506L0ScalarEulerRead point) Temporal Algebraic := by
      have actual :=
        fixedP506L0_scalar_final_eq_matterScalar_native_add_p286AlgebraicDelta
          point
      change
        fixedP506L0ScalarEulerRead point Final =
          fixedP506L0ScalarEulerRead point Temporal +
            completeJointLiveElectricECReadDelta
              (fixedP506L0ScalarEulerRead point) Temporal Algebraic
        at actual
      exact actual
    _ = fixedP506L0ScalarEulerRead point Temporal := by
      rw [fixedP506L0_scalar_p286Algebraic_delta_zero]
      simp

/-! ## One whole Final--Temporal matter-connection support -/

private theorem final_gaugeConnection_eq_temporal :
    Final.gaugeConnection = Temporal.gaugeConnection := by
  calc
    Final.gaugeConnection = Algebraic.gaugeConnection :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC.trans
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
          positiveSmoothUnifiedSource FixedInput)
    _ = Temporal.gaugeConnection := algebraic_gaugeConnection_eq_temporal

private theorem final_scalar_eq_temporal :
    Final.scalar = Temporal.scalar := by
  calc
    Final.scalar = Algebraic.scalar :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC.trans
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar
          positiveSmoothUnifiedSource FixedInput)
    _ = Temporal.scalar := algebraic_scalar_eq_temporal

private theorem final_matter_eq_temporal :
    Final.matter = Temporal.matter := by
  calc
    Final.matter = Algebraic.matter :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC.trans
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter
          positiveSmoothUnifiedSource FixedInput)
    _ = Temporal.matter := algebraic_matter_eq_temporal

private theorem final_conjugateMatter_eq_temporal :
    Final.conjugateMatter = Temporal.conjugateMatter := by
  calc
    Final.conjugateMatter = Algebraic.conjugateMatter :=
      final_conjugateMatter_eq_algebraic
    _ = Temporal.conjugateMatter := algebraic_conjugateMatter_eq_temporal

private theorem final_coframe_eq_temporal :
    Final.coframe = Temporal.coframe :=
  final_coframe_eq_algebraic.trans algebraic_coframe_eq_temporal

private theorem
    ecFullCauchyConnection_eq_normalizedAffine_selfCurvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
      ).gravityConnection =
      normalizedAffineLorentzConnectionField
        ((sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
          source current).gravityConnection 0)
        (holonomicGravityCurvature
          (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
            source current) 0) := by
  rw [
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_eq_normalizedAffine]
  congr 1
  · rw [normalizedAffineLorentzConnectionField_zero]
  · unfold sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
    exact
      (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_curvature_zero
        source (diracDualFormNativeECEvolutionWrittenCurrent source current)).symm

private theorem temporal_gravityConnection_eq_fixedInput :
    Temporal.gravityConnection = FixedInput.gravityConnection :=
  rfl

private theorem fixedInput_gravityConnection_normalForm :
    FixedInput.gravityConnection =
      normalizedAffineLorentzConnectionField
        (FixedInput.gravityConnection 0)
        (holonomicGravityCurvature FixedInput 0) := by
  unfold FixedInput FixedP506FormNativeJointActionSolvedSuccessor
  exact
    ecFullCauchyConnection_eq_normalizedAffine_selfCurvature
      positiveSmoothUnifiedSource _

private theorem final_gravityConnection_origin_eq_fixedInput :
    Final.gravityConnection 0 = FixedInput.gravityConnection 0 := by
  calc
    Final.gravityConnection 0 =
        FixedP506JointActionSuccessor.gravityConnection 0 :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityConnection_origin_eq_jointAction
    _ = FixedInput.gravityConnection 0 :=
      fixedP506FormNativeJointActionSolvedSuccessor_gravityConnection_origin.symm

/-- The only primitive field through which the final Cartan--EC suffix can
change either matter reader.  It is a diagnostic difference of two already
generated actuals, never an input to a writer. -/
def fixedP506L0FinalTemporalGravityConnectionDelta
    (point : BasePoint) : PointwiseLorentzSpinConnection :=
  Final.gravityConnection point - Temporal.gravityConnection point

/-- Exact global normal form of the one remaining matter/adjoint dependency
edge.  The shared origin cancels; only the difference of the two
action-generated EC curvature targets remains. -/
theorem fixedP506L0FinalTemporalGravityConnectionDelta_normalForm
    (point : BasePoint) :
    fixedP506L0FinalTemporalGravityConnectionDelta point =
      normalizedAffineLorentzConnectionField
          (FixedInput.gravityConnection 0)
          fixedP506L0CompleteJointLiveElectricECGravityCurvatureTarget point -
        normalizedAffineLorentzConnectionField
          (FixedInput.gravityConnection 0)
          (holonomicGravityCurvature FixedInput 0) point := by
  unfold fixedP506L0FinalTemporalGravityConnectionDelta
  rw [congrFun
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityConnection_normalForm
    point]
  rw [final_gravityConnection_origin_eq_fixedInput]
  rw [temporal_gravityConnection_eq_fixedInput,
    congrFun fixedInput_gravityConnection_normalForm point]

/-- The induced connection action on a primal matter variation direction. -/
def fixedP506L0FinalTemporalPrimalConnectionVariation
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) (formDirection : LorentzianIndex) :
    DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
    (diracSpinConnectionLift
      (fixedP506L0FinalTemporalGravityConnectionDelta point) formDirection)
    (matterCoordinateEquiv.symm direction)

/-- The induced connection action on the already generated matter field,
which is the complete adjoint-reader support. -/
def fixedP506L0FinalTemporalAdjointConnectionVariation
    (point : BasePoint) (formDirection : LorentzianIndex) :
    DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
    (diracSpinConnectionLift
      (fixedP506L0FinalTemporalGravityConnectionDelta point) formDirection)
    (Temporal.matter point)

private theorem final_matterVariationAlgebraicDirection_eq_temporal_add
    (direction : MatterCoordinateCarrier) (point : BasePoint) :
    holonomicMatterVariationAlgebraicDirection Final direction point =
      holonomicMatterVariationAlgebraicDirection Temporal direction point +
        fixedP506L0FinalTemporalPrimalConnectionVariation direction point := by
  funext formDirection
  unfold holonomicMatterVariationAlgebraicDirection
    fixedP506L0FinalTemporalPrimalConnectionVariation
    fixedP506L0FinalTemporalGravityConnectionDelta
  rw [show
      Final.gravityConnection point =
        Temporal.gravityConnection point +
          (Final.gravityConnection point - Temporal.gravityConnection point) by
      abel]
  rw [diracSpinConnectionLift_add,
    diracMatrixMatterAction_add_matrix_local,
    final_gaugeConnection_eq_temporal]
  simp only [Pi.add_apply]
  abel

private theorem final_matterCovariantDerivative_eq_temporal_add
    (point : BasePoint) :
    holonomicMatterCovariantDerivative Final point =
      holonomicMatterCovariantDerivative Temporal point +
        fixedP506L0FinalTemporalAdjointConnectionVariation point := by
  funext formDirection
  unfold holonomicMatterCovariantDerivative
    fixedP506L0FinalTemporalAdjointConnectionVariation
    fixedP506L0FinalTemporalGravityConnectionDelta
  rw [final_matter_eq_temporal, final_gaugeConnection_eq_temporal]
  rw [show
      Final.gravityConnection point =
        Temporal.gravityConnection point +
          (Final.gravityConnection point - Temporal.gravityConnection point) by
      abel]
  rw [diracSpinConnectionLift_add,
    diracMatrixMatterAction_add_matrix_local]
  simp only [Pi.add_apply]
  abel

private theorem
    matterCovariantDerivativeVariationVector_finalField_eq_temporalField
    (point : BasePoint)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0
        point (toContinuumPointField Final point) variation =
      matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0
        point (toContinuumPointField Temporal point) variation := by
  unfold matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField]
  rw [final_coframe_eq_temporal]

private theorem final_yukawaVector_eq_temporal
    (point : BasePoint) :
    generatedContinuumDiracDualYukawaVector positiveSmoothUnifiedSource 0
        point (toContinuumPointField Final point) =
      generatedContinuumDiracDualYukawaVector positiveSmoothUnifiedSource 0
        point (toContinuumPointField Temporal point) := by
  unfold generatedContinuumDiracDualYukawaVector
  simp only [toContinuumPointField]
  rw [final_scalar_eq_temporal, final_matter_eq_temporal]

private theorem final_generatedMatterVector_eq_temporal_add
    (point : BasePoint) :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0
        point (toContinuumPointField Final point) =
      generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0
          point (toContinuumPointField Temporal point) +
        matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0
          point (toContinuumPointField Final point)
          (fixedP506L0FinalTemporalAdjointConnectionVariation point) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
  change
    matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0
          point (toContinuumPointField Final point)
          (holonomicMatterCovariantDerivative Final point) +
        generatedContinuumDiracDualYukawaVector positiveSmoothUnifiedSource 0
          point (toContinuumPointField Final point) =
      (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0
            point (toContinuumPointField Temporal point)
            (holonomicMatterCovariantDerivative Temporal point) +
          generatedContinuumDiracDualYukawaVector positiveSmoothUnifiedSource 0
            point (toContinuumPointField Temporal point)) +
        matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0
          point (toContinuumPointField Final point)
          (fixedP506L0FinalTemporalAdjointConnectionVariation point)
  rw [final_matterCovariantDerivative_eq_temporal_add,
    matterCovariantDerivativeVariationVector_add,
    matterCovariantDerivativeVariationVector_finalField_eq_temporalField
      point (holonomicMatterCovariantDerivative Temporal point),
    final_yukawaVector_eq_temporal]
  abel

/-- Exact all-point primal reader support.  The entire U1 -> U5 suffix has
collapsed to the action of one already generated Lorentz-connection
difference on the same matter direction. -/
theorem fixedP506L0_matter_final_delta_connectionAction
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0MatterEulerRead point) Temporal Final =
      fun direction =>
        generatedVolumeDensity (toContinuumPointField Final point) *
          (Final.conjugateMatter point
            (matterCovariantDerivativeVariationVector
              positiveSmoothUnifiedSource 0 point
              (toContinuumPointField Final point)
              (fixedP506L0FinalTemporalPrimalConnectionVariation
                direction point))).re := by
  rw [fixedP506L0_matter_final_delta_normalForm]
  funext direction
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector generatedVolumeDensity
  rw [final_matterVariationAlgebraicDirection_eq_temporal_add,
    matterCovariantDerivativeVariationVector_add]
  simp only [map_add, Complex.add_re]
  rw [
    matterCovariantDerivativeVariationVector_finalField_eq_temporalField
      point (holonomicMatterVariationAlgebraicDirection Temporal direction point)]
  simp only [toContinuumPointField]
  rw [final_coframe_eq_temporal, final_scalar_eq_temporal,
    final_conjugateMatter_eq_temporal]
  ring

/-- Exact all-point adjoint reader support on the same connection
difference.  Together with the preceding theorem this exhausts the
matter/adjoint downstream dependence; no sector-local repair remains hidden
behind either Euler wrapper. -/
theorem fixedP506L0_conjugateMatter_final_delta_connectionAction
    (point : BasePoint) :
    completeJointLiveElectricECReadDelta
        (fixedP506L0ConjugateMatterEulerRead point) Temporal Final =
      fun direction =>
        generatedVolumeDensity (toContinuumPointField Final point) *
          (matterDualOfCoordinates direction
            (matterCovariantDerivativeVariationVector
              positiveSmoothUnifiedSource 0 point
              (toContinuumPointField Final point)
              (fixedP506L0FinalTemporalAdjointConnectionVariation point))).re := by
  rw [fixedP506L0_conjugateMatter_final_delta_normalForm]
  funext direction
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [final_generatedMatterVector_eq_temporal_add]
  simp only [map_add, Complex.add_re]
  unfold generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [final_coframe_eq_temporal]
  ring

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
