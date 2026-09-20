import H0mework.Physics.FullOccurrence.FixedMatterScalarVerdict
import H0mework.Physics.ScalarJets.FixedJointP286AlgebraicMatterScalarDelta

/-!
# U6 matter/adjoint all-point temporal support

The final full-occurrence actual and the action-generated temporal current
share every primitive read by the matter sectors except the Lorentz
connection.  This file collapses both final Euler changed reads to the action
of that one already generated connection difference.  The difference is a
diagnostic read; it is never fed to a writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalMatterAdjointTemporalSupport

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalMatterScalarVerdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECAllPointMatterScalarReadTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECMatterScalarDeltas
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeScalarVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterPointwiseEquation
open StageNineConjugateMatterVariation
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source FixedInput

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev PreEC : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private theorem algebraic_eq_zeroCandidate :
    Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source Temporal 0 := by
  exact
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate

private theorem algebraic_coframe_eq_temporal :
    Algebraic.coframe = Temporal.coframe := by
  rw [algebraic_eq_zeroCandidate]
  rfl

private theorem algebraic_gaugeConnection_eq_temporal :
    Algebraic.gaugeConnection = Temporal.gaugeConnection := by
  rw [algebraic_eq_zeroCandidate,
    diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rfl

private theorem algebraic_scalar_eq_temporal :
    Algebraic.scalar = Temporal.scalar := by
  rw [algebraic_eq_zeroCandidate]
  rfl

private theorem algebraic_matter_eq_temporal :
    Algebraic.matter = Temporal.matter := by
  rw [algebraic_eq_zeroCandidate]
  rfl

private theorem algebraic_conjugateMatter_eq_temporal :
    Algebraic.conjugateMatter = Temporal.conjugateMatter := by
  rw [algebraic_eq_zeroCandidate]
  rfl

private theorem preEC_coframe_eq_temporal :
    PreEC.coframe = Temporal.coframe := by
  calc
    PreEC.coframe = Algebraic.coframe :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe
        Source FixedInput
    _ = Temporal.coframe := algebraic_coframe_eq_temporal

private theorem preEC_gaugeConnection_eq_temporal :
    PreEC.gaugeConnection = Temporal.gaugeConnection := by
  calc
    PreEC.gaugeConnection = Algebraic.gaugeConnection :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
        Source FixedInput
    _ = Temporal.gaugeConnection := algebraic_gaugeConnection_eq_temporal

private theorem preEC_scalar_eq_temporal :
    PreEC.scalar = Temporal.scalar := by
  calc
    PreEC.scalar = Algebraic.scalar :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar
        Source FixedInput
    _ = Temporal.scalar := algebraic_scalar_eq_temporal

private theorem preEC_matter_eq_temporal :
    PreEC.matter = Temporal.matter := by
  calc
    PreEC.matter = Algebraic.matter :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter
        Source FixedInput
    _ = Temporal.matter := algebraic_matter_eq_temporal

private theorem preEC_conjugateMatter_eq_temporal :
    PreEC.conjugateMatter = Temporal.conjugateMatter := by
  calc
    PreEC.conjugateMatter = Algebraic.conjugateMatter :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter
        Source FixedInput
    _ = Temporal.conjugateMatter := algebraic_conjugateMatter_eq_temporal

private theorem u6_coframe_eq_temporal : U6.coframe = Temporal.coframe := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source U5).coframe = Temporal.coframe
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
      Source U5).trans
      (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC.trans
        preEC_coframe_eq_temporal)

private theorem u6_gaugeConnection_eq_temporal :
    U6.gaugeConnection = Temporal.gaugeConnection := by
  exact
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current.trans
      (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC.trans
        preEC_gaugeConnection_eq_temporal)

private theorem u6_scalar_eq_temporal : U6.scalar = Temporal.scalar := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source U5).scalar = Temporal.scalar
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
      Source U5).trans
      (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC.trans
        preEC_scalar_eq_temporal)

private theorem u6_matter_eq_temporal : U6.matter = Temporal.matter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source U5).matter = Temporal.matter
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
      Source U5).trans
      (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC.trans
        preEC_matter_eq_temporal)

private theorem u6_conjugateMatter_eq_temporal :
    U6.conjugateMatter = Temporal.conjugateMatter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source U5).conjugateMatter = Temporal.conjugateMatter
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
      Source U5).trans
      (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC.trans
        preEC_conjugateMatter_eq_temporal)

/-- The scalar channel is completely insensitive to the P286, Cartan, EC,
and full-occurrence suffixes: U6 retains the same all-point read as the
source/action-generated temporal leg. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_scalarResidual_eq_temporal
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point).scalar =
      (diracDualFormNativePointwiseJointResidual Source Temporal point).scalar := by
  calc
    (diracDualFormNativePointwiseJointResidual Source U6 point).scalar =
        (diracDualFormNativePointwiseJointResidual Source PreEC point).scalar :=
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_scalarResidual_eq_preEC
        point
    _ =
        (diracDualFormNativePointwiseJointResidual Source U5 point).scalar :=
      (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalarResidual_eq_preEC
        point).symm
    _ =
        (diracDualFormNativePointwiseJointResidual Source Temporal point
          ).scalar := by
      simpa [fixedP506L0ScalarEulerRead] using
        fixedP506L0_scalar_final_eq_temporal point

/-- The sole primitive difference seen by the final matter/adjoint readers. -/
def fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalGravityConnectionDelta
    (point : BasePoint) : PointwiseLorentzSpinConnection :=
  U6.gravityConnection point - Temporal.gravityConnection point

def fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalPrimalConnectionVariation
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) (formDirection : LorentzianIndex) :
    DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
    (diracSpinConnectionLift
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalGravityConnectionDelta
        point) formDirection)
    (matterCoordinateEquiv.symm direction)

def fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionVariation
    (point : BasePoint) (formDirection : LorentzianIndex) :
    DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
    (diracSpinConnectionLift
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalGravityConnectionDelta
        point) formDirection)
    (Temporal.matter point)

/-- The primal Euler changed read induced by the generated Cartan connection
difference. -/
def fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalPrimalConnectionAction
    (point : BasePoint) : MatterCoordinateCarrier → ℝ :=
  fun direction =>
    generatedVolumeDensity (toContinuumPointField U6 point) *
      (U6.conjugateMatter point
        (matterCovariantDerivativeVariationVector Source 0 point
          (toContinuumPointField U6 point)
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalPrimalConnectionVariation
            direction point))).re

/-- The adjoint Euler changed read induced by the same generated Cartan
connection difference. -/
def fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionAction
    (point : BasePoint) : MatterCoordinateCarrier → ℝ :=
  fun direction =>
    generatedVolumeDensity (toContinuumPointField U6 point) *
      (matterDualOfCoordinates direction
        (matterCovariantDerivativeVariationVector Source 0 point
          (toContinuumPointField U6 point)
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionVariation
            point))).re

private theorem u6_matterVariationAlgebraicDirection_eq_temporal_add
    (direction : MatterCoordinateCarrier) (point : BasePoint) :
    holonomicMatterVariationAlgebraicDirection U6 direction point =
      holonomicMatterVariationAlgebraicDirection Temporal direction point +
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalPrimalConnectionVariation
          direction point := by
  funext formDirection
  unfold holonomicMatterVariationAlgebraicDirection
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalPrimalConnectionVariation
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalGravityConnectionDelta
  rw [show
      U6.gravityConnection point =
        Temporal.gravityConnection point +
          (U6.gravityConnection point - Temporal.gravityConnection point) by
      abel]
  rw [diracSpinConnectionLift_add,
    diracMatrixMatterAction_add_matrix_local,
    u6_gaugeConnection_eq_temporal]
  simp only [Pi.add_apply]
  abel

private theorem u6_matterCovariantDerivative_eq_temporal_add
    (point : BasePoint) :
    holonomicMatterCovariantDerivative U6 point =
      holonomicMatterCovariantDerivative Temporal point +
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionVariation
          point := by
  funext formDirection
  unfold holonomicMatterCovariantDerivative
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionVariation
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalGravityConnectionDelta
  rw [u6_matter_eq_temporal, u6_gaugeConnection_eq_temporal]
  rw [show
      U6.gravityConnection point =
        Temporal.gravityConnection point +
          (U6.gravityConnection point - Temporal.gravityConnection point) by
      abel]
  rw [diracSpinConnectionLift_add,
    diracMatrixMatterAction_add_matrix_local]
  simp only [Pi.add_apply]
  abel

private theorem
    matterCovariantDerivativeVariationVector_u6Field_eq_temporalField
    (point : BasePoint)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterCovariantDerivativeVariationVector Source 0 point
        (toContinuumPointField U6 point) variation =
      matterCovariantDerivativeVariationVector Source 0 point
        (toContinuumPointField Temporal point) variation := by
  unfold matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField]
  rw [u6_coframe_eq_temporal]

private theorem u6_yukawaVector_eq_temporal
    (point : BasePoint) :
    generatedContinuumDiracDualYukawaVector Source 0 point
        (toContinuumPointField U6 point) =
      generatedContinuumDiracDualYukawaVector Source 0 point
        (toContinuumPointField Temporal point) := by
  unfold generatedContinuumDiracDualYukawaVector
  simp only [toContinuumPointField]
  rw [u6_scalar_eq_temporal, u6_matter_eq_temporal]

private theorem u6_generatedMatterVector_eq_temporal_add
    (point : BasePoint) :
    generatedContinuumDiracDualMatterVector Source 0 point
        (toContinuumPointField U6 point) =
      generatedContinuumDiracDualMatterVector Source 0 point
          (toContinuumPointField Temporal point) +
        matterCovariantDerivativeVariationVector Source 0 point
          (toContinuumPointField U6 point)
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionVariation
            point) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
  change
    matterCovariantDerivativeVariationVector Source 0 point
          (toContinuumPointField U6 point)
          (holonomicMatterCovariantDerivative U6 point) +
        generatedContinuumDiracDualYukawaVector Source 0 point
          (toContinuumPointField U6 point) =
      (matterCovariantDerivativeVariationVector Source 0 point
            (toContinuumPointField Temporal point)
            (holonomicMatterCovariantDerivative Temporal point) +
          generatedContinuumDiracDualYukawaVector Source 0 point
            (toContinuumPointField Temporal point)) +
        matterCovariantDerivativeVariationVector Source 0 point
          (toContinuumPointField U6 point)
          (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionVariation
            point)
  rw [u6_matterCovariantDerivative_eq_temporal_add,
    matterCovariantDerivativeVariationVector_add,
    matterCovariantDerivativeVariationVector_u6Field_eq_temporalField
      point (holonomicMatterCovariantDerivative Temporal point),
    u6_yukawaVector_eq_temporal]
  abel

private theorem u6_matterDifferentialMomentum_eq_temporal
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum Source U6 direction derivativeDirection =
      matterDifferentialMomentum Source Temporal direction
        derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [u6_coframe_eq_temporal, u6_conjugateMatter_eq_temporal]

private theorem u6_matterMomentumDivergence_eq_temporal
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence Source U6 direction =
      matterDifferentialMomentumDivergence Source Temporal direction := by
  funext point
  unfold matterDifferentialMomentumDivergence
  simp_rw [u6_matterDifferentialMomentum_eq_temporal]

/-- Exact all-point primal support of U6 relative to the native temporal
matter read. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterResidual_sub_temporal_connectionAction
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point).matter -
      (diracDualFormNativePointwiseJointResidual Source Temporal point).matter =
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalPrimalConnectionAction
        point := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient Source U6 direction point -
        diracDualMatterEulerLagrangeDirectionalCoefficient Source Temporal
          direction point = _
  unfold
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalPrimalConnectionAction
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [congrFun (u6_matterMomentumDivergence_eq_temporal direction) point]
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector generatedVolumeDensity
  rw [u6_matterVariationAlgebraicDirection_eq_temporal_add,
    matterCovariantDerivativeVariationVector_add]
  simp only [map_add, Complex.add_re]
  rw [
    matterCovariantDerivativeVariationVector_u6Field_eq_temporalField
      point (holonomicMatterVariationAlgebraicDirection Temporal direction point)]
  simp only [toContinuumPointField]
  rw [u6_coframe_eq_temporal, u6_scalar_eq_temporal,
    u6_conjugateMatter_eq_temporal]
  ring

/-- Additive whole-reader form of the same primal changed read. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterResidual_eq_temporal_add_connectionAction
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point).matter =
      (diracDualFormNativePointwiseJointResidual Source Temporal point).matter +
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalPrimalConnectionAction
          point := by
  let connectionAction : MatterCoordinateCarrier → ℝ :=
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalPrimalConnectionAction
      point
  change
    (diracDualFormNativePointwiseJointResidual Source U6 point).matter =
      (diracDualFormNativePointwiseJointResidual Source Temporal point).matter +
        connectionAction
  have delta :
      (diracDualFormNativePointwiseJointResidual Source U6 point).matter -
          (diracDualFormNativePointwiseJointResidual Source Temporal point
            ).matter = connectionAction := by
    simpa only [connectionAction] using
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterResidual_sub_temporal_connectionAction
        point
  calc
    (diracDualFormNativePointwiseJointResidual Source U6 point).matter =
        connectionAction +
          (diracDualFormNativePointwiseJointResidual Source Temporal point
            ).matter :=
      sub_eq_iff_eq_add.mp delta
    _ =
        (diracDualFormNativePointwiseJointResidual Source Temporal point
          ).matter + connectionAction := add_comm _ _

/-- Exact all-point adjoint support on the same generated connection
difference. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_conjugateMatterResidual_sub_temporal_connectionAction
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point
        ).conjugateMatter -
      (diracDualFormNativePointwiseJointResidual Source Temporal point
          ).conjugateMatter =
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionAction
        point := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient Source U6 direction point -
        diracDualConjugateMatterDirectionalCoefficient Source Temporal direction
          point = _
  unfold
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionAction
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [u6_generatedMatterVector_eq_temporal_add]
  simp only [map_add, Complex.add_re]
  unfold generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [u6_coframe_eq_temporal]
  ring

/-- Additive whole-reader form of the same adjoint changed read. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_conjugateMatterResidual_eq_temporal_add_connectionAction
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point
        ).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual Source Temporal point
          ).conjugateMatter +
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionAction
          point := by
  let connectionAction : MatterCoordinateCarrier → ℝ :=
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionAction
      point
  change
    (diracDualFormNativePointwiseJointResidual Source U6 point
        ).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual Source Temporal point
          ).conjugateMatter + connectionAction
  have delta :
      (diracDualFormNativePointwiseJointResidual Source U6 point
          ).conjugateMatter -
          (diracDualFormNativePointwiseJointResidual Source Temporal point
            ).conjugateMatter = connectionAction := by
    simpa only [connectionAction] using
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_conjugateMatterResidual_sub_temporal_connectionAction
        point
  calc
    (diracDualFormNativePointwiseJointResidual Source U6 point
        ).conjugateMatter =
        connectionAction +
          (diracDualFormNativePointwiseJointResidual Source Temporal point
            ).conjugateMatter :=
      sub_eq_iff_eq_add.mp delta
    _ =
        (diracDualFormNativePointwiseJointResidual Source Temporal point
          ).conjugateMatter + connectionAction := add_comm _ _

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalMatterAdjointTemporalSupport
