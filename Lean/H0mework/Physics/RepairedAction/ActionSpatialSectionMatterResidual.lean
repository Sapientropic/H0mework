import H0mework.Physics.RepairedAction.ActionSpatialSectionMatterMomentumTransport
import H0mework.Physics.RepairedAction.ActionSpatialSectionResidual

/-!
# Matter residual of the repaired spatial section

This module substitutes the already-generated repaired section into both
Dirac-dual matter equations.  KIN-16 first-jet transport and the native primal
and adjoint action laws close the two channels on the same canonical slice.

Both equalities are producer-soundness readouts.  They do not define a write
from a residual coordinate or support branch.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterResidual

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterComparison
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterIdentityCoframeAcceptance
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterMomentumTransport
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineMatterPointwiseEquation
open StageNineMatterVariation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev RepairedActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor

private abbrev ComparisonActual : StageNineHolonomicConfiguration :=
  fixedP506FormNativeRepairedSpatialMatterSmoothComparison

private abbrev IdentityComparison : StageNineHolonomicConfiguration :=
  fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison

private theorem repairedActual_coframe_one_zeroSlice
    (space : StageNineSpatialPoint) :
    RepairedActual.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
  have jet := repairedSection_coframeFirstJet_zeroSlice space
  exact congrArg PointwiseLorentzianCoframeJet.coframe jet

private theorem comparisonActual_coframe_one_zeroSlice
    (space : StageNineSpatialPoint) :
    ComparisonActual.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
  have jet := repairedMatterComparison_coframeFirstJet_zeroSlice space
  exact congrArg PointwiseLorentzianCoframeJet.coframe jet

private theorem identityComparison_coframe_one
    (point : BasePoint) :
    IdentityComparison.coframe point = 1 := by
  rfl

theorem
    fixedP506FormNativeRepairedSpatialMatterComparison_algebraic_zeroSlice_eq_identity
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        ComparisonActual direction (canonicalCauchySlicePoint 0 space) =
      diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        IdentityComparison direction (canonicalCauchySlicePoint 0 space) := by
  rw [
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
      positiveSmoothUnifiedSource ComparisonActual direction
      (canonicalCauchySlicePoint 0 space)
      (comparisonActual_coframe_one_zeroSlice space),
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
      positiveSmoothUnifiedSource IdentityComparison direction
      (canonicalCauchySlicePoint 0 space)
      (identityComparison_coframe_one
        (canonicalCauchySlicePoint 0 space))]
  rfl

theorem fixedP506FormNativeRepairedSpatialMatterComparison_matterEuler_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource ComparisonActual direction
          (canonicalCauchySlicePoint 0 space) =
      0 := by
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [
    fixedP506FormNativeRepairedSpatialMatterComparison_algebraic_zeroSlice_eq_identity,
    fixedP506FormNativeRepairedSpatialMatterMomentumDivergence_zeroSlice_eq_comparison]
  exact
    fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison_matterEuler_zeroSlice
      space direction

private theorem repairedActual_matterMomentum_eq_comparison
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource RepairedActual
        direction derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource ComparisonActual
        direction derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [← repairedMatterComparison_coframe_eq_repaired,
    ← repairedMatterComparison_conjugateMatter_eq_repaired]

private theorem repairedActual_matterMomentumDivergence_eq_comparison
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        RepairedActual direction (canonicalCauchySlicePoint 0 space) =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        ComparisonActual direction (canonicalCauchySlicePoint 0 space) := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [repairedActual_matterMomentum_eq_comparison]

private theorem repairedActual_matterAlgebraic_zeroSlice_eq_comparison
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        RepairedActual direction (canonicalCauchySlicePoint 0 space) =
      diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        ComparisonActual direction (canonicalCauchySlicePoint 0 space) := by
  rw [
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
      positiveSmoothUnifiedSource RepairedActual direction
      (canonicalCauchySlicePoint 0 space)
      (repairedActual_coframe_one_zeroSlice space),
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
      positiveSmoothUnifiedSource ComparisonActual direction
      (canonicalCauchySlicePoint 0 space)
      (comparisonActual_coframe_one_zeroSlice space)]
  rw [← repairedMatterComparison_conjugateMatter_eq_repaired,
    ← repairedMatterComparison_algebraicOperator_zeroSlice]

/-- The adjoint Euler channel vanishes on the same repaired section and the
same generated slice. -/
theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_matterEuler_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource RepairedActual direction
          (canonicalCauchySlicePoint 0 space) =
      0 := by
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [repairedActual_matterAlgebraic_zeroSlice_eq_comparison,
    repairedActual_matterMomentumDivergence_eq_comparison]
  exact
    fixedP506FormNativeRepairedSpatialMatterComparison_matterEuler_zeroSlice
      space direction

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).matter =
      0 := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource RepairedActual direction
          (canonicalCauchySlicePoint 0 space) =
      0
  exact
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_matterEuler_zeroSlice
      space direction

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_conjugateMatter_zeroSlice
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).conjugateMatter =
      0 := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        RepairedActual direction (canonicalCauchySlicePoint 0 space) =
      0
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_matterVector_zeroSlice]
  simp

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterResidual
