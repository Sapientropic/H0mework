import H0mework.Physics.IdentityHessian.CartanECNormalFixedGlobalMatterDualAdjointAcceptance
import H0mework.Physics.RepairedAction.ActionSpatialSectionGaugeScalarNormalForm

/-!
# Fixed repaired spatial-section matter comparison

This file prepares the local, fixed-lineage comparison needed to read the
densitized adjoint Euler equation.  The comparison replaces no generated
matter data: it keeps the repaired primal and adjoint fields verbatim and
uses the already smooth input fields for coordinates irrelevant to the
matter momentum.

The KIN-16 coframe is then read directly: its complete first jet is
identity/zero on the generated slice.  No residual coordinate or equation
receipt enters either definition.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterComparison

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointResponseRegularity
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionGaugeScalarNormalForm
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineMatterPointwiseEquation
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineCurrentP286CompleteActionResponseOperator
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev RepairedActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev PrimitiveDiagonalActual : StageNineHolonomicConfiguration :=
  positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual

/-! ## Fixed KIN-16 coframe seam -/

theorem repairedSection_coframe_eq_primitiveDiagonal :
    RepairedActual.coframe = PrimitiveDiagonalActual.coframe := by
  calc
    RepairedActual.coframe = InputActual.coframe :=
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe
        positiveSmoothUnifiedSource InputActual
    _ = FixedP506JointActionSuccessor.coframe :=
      fixedP506FormNativeJointActionSolvedSuccessor_coframe
    _ = FixedP506JointActual.coframe :=
      fixedP506JointActionSuccessor_coframe
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.coframe := by
      exact
        currentP286CompleteActionResponseOperator_coframe
          positiveSmoothUnifiedSource _
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe :=
      fixedGlobalMatterDualFullCauchy_coframe
    _ = PrimitiveDiagonalActual.coframe :=
      fixedGlobalFullCauchy_coframe

theorem repairedSection_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt RepairedActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  rw [repairedSection_coframe_eq_primitiveDiagonal]
  exact fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space

/-! ## Smooth matter-only comparison -/

def fixedP506FormNativeRepairedSpatialMatterCoordinates
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterCoordinateEquiv (RepairedActual.matter point)

theorem fixedP506FormNativeRepairedSpatialMatterCoordinates_contDiff :
    ContDiff ℝ ∞ fixedP506FormNativeRepairedSpatialMatterCoordinates := by
  unfold fixedP506FormNativeRepairedSpatialMatterCoordinates
  exact
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_matterCoordinates_contDiff

/-- A proof-only smooth carrier with exactly the repaired matter and adjoint
fields.  It is never used as a successor. -/
def fixedP506FormNativeRepairedSpatialMatterSmoothComparison :
    StageNineHolonomicConfiguration where
  coframe := InputActual.coframe
  gravityConnection := InputActual.gravityConnection
  gravityAuxiliary := InputActual.gravityAuxiliary
  gravitySimplicityMultiplier := InputActual.gravitySimplicityMultiplier
  gaugeConnection := InputActual.gaugeConnection
  gaugeAuxiliary := InputActual.gaugeAuxiliary
  scalar := InputActual.scalar
  matter := fun point =>
    matterCoordinateEquiv.symm
      (fixedP506FormNativeRepairedSpatialMatterCoordinates point)
  conjugateMatter := fun point =>
    matterDualOfCoordinates
      (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
        point)

theorem repairedMatterComparison_matter_eq_repaired :
    fixedP506FormNativeRepairedSpatialMatterSmoothComparison.matter =
      RepairedActual.matter := by
  funext point
  unfold fixedP506FormNativeRepairedSpatialMatterSmoothComparison
    fixedP506FormNativeRepairedSpatialMatterCoordinates
  exact matterCoordinateEquiv.symm_apply_apply _

theorem repairedMatterComparison_conjugateMatter_eq_repaired :
    fixedP506FormNativeRepairedSpatialMatterSmoothComparison.conjugateMatter =
      RepairedActual.conjugateMatter := by
  funext point
  unfold fixedP506FormNativeRepairedSpatialMatterSmoothComparison
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
  exact matterDualOfCoordinates_surjective _

theorem fixedP506FormNativeRepairedSpatialMatterSmoothComparison_smooth :
    fixedP506FormNativeRepairedSpatialMatterSmoothComparison.Smooth := by
  unfold StageNineHolonomicConfiguration.Smooth
  dsimp only [fixedP506FormNativeRepairedSpatialMatterSmoothComparison]
  rcases fixedP506FormNativeJointActionSolvedSuccessor_smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, _matterSmooth, _conjugateMatterSmooth⟩
  have matterSmooth :
      ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (matterCoordinateEquiv.symm
            (fixedP506FormNativeRepairedSpatialMatterCoordinates point)) := by
    simpa only [matterCoordinateEquiv.apply_symm_apply] using
      fixedP506FormNativeRepairedSpatialMatterCoordinates_contDiff
  have conjugateSmooth :
      ∀ index : MatterCoordinateIndex,
        ContDiff ℝ ∞ fun point =>
          matterDualOfCoordinates
              (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
                point)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
    intro index
    rw [show
      (fun point =>
        matterDualOfCoordinates
            (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
              point)
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) =
        fun point =>
          fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
            point index by
      funext point
      exact matterDualOfCoordinates_basis_apply _ _]
    let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj index).comp
        (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
    have projected :
        ContDiff ℝ ∞ fun point =>
          fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
            point index :=
        (projection.restrictScalars ℝ).contDiff.comp
          fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates_contDiff
    exact projected
  exact
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateSmooth⟩

theorem repairedMatterComparison_coframe_eq_repaired :
    fixedP506FormNativeRepairedSpatialMatterSmoothComparison.coframe =
      RepairedActual.coframe := by
  change InputActual.coframe = RepairedActual.coframe
  exact
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe
      positiveSmoothUnifiedSource InputActual).symm

theorem repairedMatterComparison_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        fixedP506FormNativeRepairedSpatialMatterSmoothComparison.coframe
        (canonicalCauchySlicePoint 0 space) =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  rw [repairedMatterComparison_coframe_eq_repaired]
  exact repairedSection_coframeFirstJet_zeroSlice space

theorem repairedMatterComparison_algebraicOperator_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        fixedP506FormNativeRepairedSpatialMatterSmoothComparison
        (canonicalCauchySlicePoint 0 space) =
      holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        RepairedActual (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  have gravityConnection :
      fixedP506FormNativeRepairedSpatialMatterSmoothComparison.gravityConnection
          point =
        RepairedActual.gravityConnection point := by
    change InputActual.gravityConnection point =
      RepairedActual.gravityConnection point
    exact
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityConnection_zeroSlice
        positiveSmoothUnifiedSource InputActual space).symm
  have gaugeConnection :
      fixedP506FormNativeRepairedSpatialMatterSmoothComparison.gaugeConnection =
        RepairedActual.gaugeConnection := by
    change InputActual.gaugeConnection = RepairedActual.gaugeConnection
    exact
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection
        positiveSmoothUnifiedSource InputActual).symm
  have scalar :
      fixedP506FormNativeRepairedSpatialMatterSmoothComparison.scalar =
        RepairedActual.scalar := by
    change InputActual.scalar = RepairedActual.scalar
    exact
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar
        positiveSmoothUnifiedSource InputActual).symm
  unfold holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  rw [gravityConnection, gaugeConnection, scalar]

/-- The smooth comparison carries the same repaired adjoint action law on
the generated slice. -/
theorem repairedMatterComparison_adjointActionLaw_zeroSlice
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      fixedP506FormNativeRepairedSpatialMatterSmoothComparison
      (canonicalCauchySlicePoint 0 space)
      (holonomicConjugateMatterDerivativeDual
        fixedP506FormNativeRepairedSpatialMatterSmoothComparison
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection) := by
  have derivativeDual
      (direction : LorentzianIndex) :
      holonomicConjugateMatterDerivativeDual
          fixedP506FormNativeRepairedSpatialMatterSmoothComparison
          (canonicalCauchySlicePoint 0 space) direction =
        holonomicConjugateMatterDerivativeDual RepairedActual
          (canonicalCauchySlicePoint 0 space) direction := by
    unfold holonomicConjugateMatterDerivativeDual
      holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates
    rw [repairedMatterComparison_conjugateMatter_eq_repaired]
  have spatialTransport :
      holonomicIdentityCoframeConjugateMatterSpatialTransport
          fixedP506FormNativeRepairedSpatialMatterSmoothComparison
          (canonicalCauchySlicePoint 0 space) =
        holonomicIdentityCoframeConjugateMatterSpatialTransport RepairedActual
          (canonicalCauchySlicePoint 0 space) := by
    unfold holonomicIdentityCoframeConjugateMatterSpatialTransport
    simp_rw [derivativeDual]
  have law :=
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_adjointActionLaw_zeroSlice
      space
  unfold HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
    at law ⊢
  rw [derivativeDual, spatialTransport,
    repairedMatterComparison_conjugateMatter_eq_repaired,
    repairedMatterComparison_algebraicOperator_zeroSlice]
  exact law

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterComparison
