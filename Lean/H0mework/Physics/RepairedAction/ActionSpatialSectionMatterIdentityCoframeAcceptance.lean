import H0mework.Physics.RepairedAction.ActionSpatialSectionMatterComparison

/-!
# Dirac-dual identity-coframe matter acceptance

This file isolates the generic calculus readout used by the fixed repaired
section.  It consumes a smooth configuration, an identity-coframe seam, and
the already generated adjoint action law.  It does not construct a field,
successor, residual repair, or branch.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterIdentityCoframeAcceptance

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineConjugateMatterActionTimeVelocity
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

theorem identityCoframeComparison_diracDualTimeActionLaw_iff
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeDerivative : Module.Dual ℂ DiracExteriorMatterCarrier) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
          (identityCoframeComparison configuration) point timeDerivative ↔
      HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
        configuration point timeDerivative :=
  Iff.rfl

theorem holonomicDiracDualIdentityCoframeMatterAlgebraicVector_of_coframe_eq_one
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint)
    (coframeOne : configuration.coframe point = 1) :
    diracDualMatterAlgebraicVariationVector source configuration direction
        point =
      holonomicDiracDualIdentityCoframeMatterAlgebraicOperator configuration
        point (matterCoordinateEquiv.symm direction) := by
  unfold diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField]
  rw [coframeOne]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
    identityCoframeMatterGeometry by rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  simp only [matterDerivativeFrameRelative_zeroChart]
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply]
  unfold holonomicMatterVariationAlgebraicDirection
  rfl

theorem holonomicDiracDualIdentityCoframeMatterAlgebraicVector
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    diracDualMatterAlgebraicVariationVector source configuration direction
        point =
      holonomicDiracDualIdentityCoframeMatterAlgebraicOperator configuration
        point (matterCoordinateEquiv.symm direction) := by
  exact
    holonomicDiracDualIdentityCoframeMatterAlgebraicVector_of_coframe_eq_one
      source configuration direction point (congrFun identityCoframe point)

theorem holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint)
    (coframeOne : configuration.coframe point = 1) :
    diracDualMatterAlgebraicDirectionalCoefficient source configuration
        direction point =
      (configuration.conjugateMatter point
        (holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
          configuration point
          (matterCoordinateEquiv.symm direction))).re := by
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [coframeOne]
  rw [Matrix.det_one, abs_one, one_mul,
    holonomicDiracDualIdentityCoframeMatterAlgebraicVector_of_coframe_eq_one
      source configuration direction point coframeOne]

theorem holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    diracDualMatterAlgebraicDirectionalCoefficient source configuration
        direction point =
      (configuration.conjugateMatter point
        (holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
          configuration point
          (matterCoordinateEquiv.symm direction))).re := by
  exact
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
      source configuration direction point (congrFun identityCoframe point)

def holonomicDiracDualIdentityCoframeConjugateMatterActionResidual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicDiracDualIdentityCoframeConjugateMatterKnownDual configuration
      point -
    (holonomicConjugateMatterDerivativeDual configuration point
      canonicalLorentzianTimeDirection).comp
      (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection)

theorem
    holonomicDiracDualIdentityCoframeMatterEulerLagrange_eq_actionResidual_re
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
        direction point =
      (holonomicDiracDualIdentityCoframeConjugateMatterActionResidual
        configuration point (matterCoordinateEquiv.symm direction)).re := by
  rw [show
    diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
        direction point =
      diracDualMatterAlgebraicDirectionalCoefficient source configuration
          direction point -
        matterDifferentialMomentumDivergence source configuration direction
          point by rfl]
  rw [
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient source
      configuration identityCoframe,
    holonomicIdentityCoframeMatterMomentumDivergence source configuration
      smooth identityCoframe]
  unfold holonomicDiracDualIdentityCoframeConjugateMatterActionResidual
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    Complex.sub_re]
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  simp only [Complex.add_re, canonicalLorentzianTimeDirection]
  simp
  ring

/-- Point-local form of the identity-coframe adjoint Euler readout.  Only
the adjoint-coordinate derivative at the occurrence is required; smoothness
of unrelated configuration fields is outside this equation's calculus
mouth. -/
theorem
    holonomicDiracDualIdentityCoframeMatterEulerLagrange_eq_actionResidual_re_of_differentiableAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
        direction point =
      (holonomicDiracDualIdentityCoframeConjugateMatterActionResidual
        configuration point (matterCoordinateEquiv.symm direction)).re := by
  rw [show
    diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
        direction point =
      diracDualMatterAlgebraicDirectionalCoefficient source configuration
          direction point -
        matterDifferentialMomentumDivergence source configuration direction
          point by rfl]
  rw [
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient source
      configuration identityCoframe,
    holonomicIdentityCoframeMatterMomentumDivergence_of_differentiableAt
      source configuration point coordinateDifferentiable identityCoframe]
  unfold holonomicDiracDualIdentityCoframeConjugateMatterActionResidual
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    Complex.sub_re]
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  simp only [Complex.add_re, canonicalLorentzianTimeDirection]
  simp
  ring

theorem
    holonomicDiracDualIdentityCoframeMatterEulerLagrange_eq_zero_of_actionLaw
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration)
    (point : BasePoint)
    (actionLaw :
      HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
        configuration point
        (holonomicConjugateMatterDerivativeDual configuration point
          canonicalLorentzianTimeDirection))
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
        direction point =
      0 := by
  rw [
    holonomicDiracDualIdentityCoframeMatterEulerLagrange_eq_actionResidual_re
      source configuration smooth identityCoframe]
  have residualZero :
      holonomicDiracDualIdentityCoframeConjugateMatterActionResidual
          configuration point =
        0 := by
    apply LinearMap.ext
    intro matter
    have lawAt := LinearMap.congr_fun actionLaw matter
    unfold
      holonomicDiracDualIdentityCoframeConjugateMatterActionResidual
      holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at lawAt
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [← lawAt]
    simp
  rw [residualZero]
  rfl

/-- A locally differentiable adjoint field satisfying the generated
identity-coframe action law has zero adjoint Euler coefficient at that same
occurrence. -/
theorem
    holonomicDiracDualIdentityCoframeMatterEulerLagrange_eq_zero_of_actionLaw_of_differentiableAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (identityCoframe : HasIdentityCoframe configuration)
    (actionLaw :
      HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
        configuration point
        (holonomicConjugateMatterDerivativeDual configuration point
          canonicalLorentzianTimeDirection))
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
        direction point =
      0 := by
  rw [
    holonomicDiracDualIdentityCoframeMatterEulerLagrange_eq_actionResidual_re_of_differentiableAt
      source configuration point coordinateDifferentiable identityCoframe]
  have residualZero :
      holonomicDiracDualIdentityCoframeConjugateMatterActionResidual
          configuration point =
        0 := by
    apply LinearMap.ext
    intro matter
    have lawAt := LinearMap.congr_fun actionLaw matter
    unfold
      holonomicDiracDualIdentityCoframeConjugateMatterActionResidual
      holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at lawAt
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [← lawAt]
    simp
  rw [residualZero]
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterIdentityCoframeAcceptance
