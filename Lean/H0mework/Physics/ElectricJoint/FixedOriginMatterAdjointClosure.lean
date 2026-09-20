import H0mework.Physics.GlobalDevelopment.FixedOriginMatterDivergenceClosure
import H0mework.Physics.ElectricJoint.FixedFieldTransport

/-!
# Fixed P506/L0 live-electric matter/adjoint origin closure

The live-electric P286 auxiliary write preserves every primitive field read
by the matter and conjugate-matter Euler channels.  This module transports
those two readers individually from the preceding global actual and closes
them with the already generated primal/adjoint and divergence proofs.

The proof deliberately does not compare the complete residual carrier or use
whole-point-field reflexivity.  In particular, the changed P286 auxiliary is
not read by either transported channel.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginMatterAdjointClosure

open ProofFreeRicherAnholonomicSource
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginMatterDivergenceClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterPointwiseEquation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-- Stable mouth for the current live-electric common global actual. -/
abbrev fixedP506L0CompleteJointLiveElectricMatterAdjointOriginActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual

/-- Stable mouth for the preceding global actual whose action reads have
already been closed. -/
abbrev fixedP506L0CompleteJointExistingMatterAdjointOriginActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointGlobalDevelopmentActual

private abbrev LiveActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricMatterAdjointOriginActual

private abbrev ExistingActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointExistingMatterAdjointOriginActual

private theorem
    live_matterDifferentialMomentum_eq_existing
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource LiveActual
        direction derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource ExistingActual
        direction derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_eq_existing]

private theorem
    live_matterDifferentialMomentumDivergence_origin_eq_existing
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource LiveActual
        direction 0 =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        ExistingActual direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [live_matterDifferentialMomentum_eq_existing direction
    derivativeDirection]

private theorem
    live_matterAlgebraic_origin_eq_existing
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        LiveActual direction 0 =
      diracDualMatterAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource ExistingActual direction 0 := by
  have variationEquality :
      holonomicMatterVariationAlgebraicDirection LiveActual direction 0 =
        holonomicMatterVariationAlgebraicDirection ExistingActual direction
          0 := by
    funext formDirection
    unfold holonomicMatterVariationAlgebraicDirection
    rw [
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityConnection_eq_existing,
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeConnection_eq_existing]
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_eq_existing,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_eq_existing,
    variationEquality]

/-- The matter Euler reader is unchanged by the live-electric auxiliary
write.  This is a reader-specific equality, not a whole-residual extensional
comparison. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_origin_residual_eq_existing :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricMatterAdjointOriginActual 0).matter =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        fixedP506L0CompleteJointExistingMatterAdjointOriginActual 0).matter := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource LiveActual direction 0 =
      diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource ExistingActual direction 0
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [live_matterAlgebraic_origin_eq_existing,
    live_matterDifferentialMomentumDivergence_origin_eq_existing]

/-- The new live-electric actual therefore inherits the unconditional matter
origin zero on the same source lineage. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricMatterAdjointOriginActual 0).matter =
      0 := by
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_origin_residual_eq_existing]
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_matter_origin_zero

private theorem live_generatedMatterVector_origin_eq_existing :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField LiveActual 0) =
      generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField ExistingActual 0) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField]
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matterCovariantDerivative_eq_existing,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_eq_existing,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_eq_existing]

/-- The conjugate-matter reader likewise ignores the changed P286 auxiliary:
its volume and generated primal vector are preserved explicitly. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_origin_residual_eq_existing :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricMatterAdjointOriginActual 0
      ).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        fixedP506L0CompleteJointExistingMatterAdjointOriginActual 0
        ).conjugateMatter := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        LiveActual direction 0 =
      diracDualConjugateMatterDirectionalCoefficient
        positiveSmoothUnifiedSource ExistingActual direction 0
  unfold diracDualConjugateMatterDirectionalCoefficient
    generatedVolumeDensity
  change
    |Matrix.det (LiveActual.coframe 0)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector
            positiveSmoothUnifiedSource 0 0
            (toContinuumPointField LiveActual 0))).re =
      |Matrix.det (ExistingActual.coframe 0)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector
            positiveSmoothUnifiedSource 0 0
            (toContinuumPointField ExistingActual 0))).re
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing,
    live_generatedMatterVector_origin_eq_existing]

/-- The new live-electric actual therefore inherits the unconditional
conjugate-matter origin zero on the same source lineage. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricMatterAdjointOriginActual 0
      ).conjugateMatter =
      0 := by
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_origin_residual_eq_existing]
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_conjugateMatter_origin_zero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginMatterAdjointClosure
