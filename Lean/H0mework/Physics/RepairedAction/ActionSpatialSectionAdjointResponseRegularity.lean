import H0mework.Physics.RepairedAction.ActionSpatialSectionMatterFirstJet
import H0mework.Physics.ConnectionJets.P506CanonicalLorentzAdjointTemporalFirstGermSupport

/-!
# Repaired adjoint first jet of the global spatial section

For the fixed P506/L0 source, the adjoint field of the same repaired section
has the explicit normal form

```text
input adjoint
  + canonical time × repaired adjoint action response
      at the matching spatial contact.
```

The response is generated after the repaired primal write by the
authoritative live-coframe Dirac-dual action.  This module accepts no residual
coordinate, support branch, sign, target derivative, or zero-fiber witness.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointResponseRegularity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterVariation
open StageNineConjugateMatterActionTimeVelocity
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionVariationDensity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterNormalForm
open SU7ExteriorBreakingYukawa

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev SectionActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private def fixedRepairedSpatialInput
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  spatiallyRecenterHolonomicConfiguration InputActual space

private def fixedRepairedSpatialPrimalInput
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    (fixedRepairedSpatialInput space)

/-- The repaired adjoint correction selected after the repaired primal write
at the same recentered contact. -/
def fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite
    (space : StageNineSpatialPoint) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  liveCoframeConjugateMatterTimeResponseWrite
    (fixedRepairedSpatialPrimalInput space)

/-! ## Recentered action response -/

private theorem canonicalSpatialContactTranslation_zero_local
    (space : StageNineSpatialPoint) :
    canonicalSpatialContactTranslation space 0 =
      canonicalCauchySlicePoint 0 space := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalSpatialContactTranslation, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem canonicalSpatialContactTranslation_hasFDerivAt_local
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    HasFDerivAt (canonicalSpatialContactTranslation space)
      (ContinuousLinearMap.id ℝ BasePoint) point := by
  unfold canonicalSpatialContactTranslation
  fun_prop

private theorem
    fixedRepairedSpatialInput_conjugateMatterCoordinateDerivative_origin
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeCoordinates
        (fixedRepairedSpatialInput space) 0 direction =
      holonomicConjugateMatterDerivativeCoordinates InputActual
        (canonicalCauchySlicePoint 0 space) direction := by
  let coordinateField : BasePoint → MatterCoordinateCarrier :=
    holonomicConjugateMatterCoordinates InputActual
  have fieldDifferentiable :
      DifferentiableAt ℝ coordinateField
        (canonicalSpatialContactTranslation space 0) := by
    rw [canonicalSpatialContactTranslation_zero_local]
    exact
      ((holonomicConjugateMatterCoordinates_contDiff InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth)
        |>.differentiable (by simp)).differentiableAt
  have composed :=
    fieldDifferentiable.hasFDerivAt.comp 0
      (canonicalSpatialContactTranslation_hasFDerivAt_local space 0)
  unfold holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  change
    fderiv ℝ
        (coordinateField ∘ canonicalSpatialContactTranslation space)
        0 (coordinateDirection direction) =
      fderiv ℝ coordinateField (canonicalCauchySlicePoint 0 space)
        (coordinateDirection direction)
  rw [composed.fderiv]
  simp [canonicalSpatialContactTranslation_zero_local]

private theorem
    fixedRepairedSpatialPrimalInput_conjugateMatter_eq_recentered
    (space : StageNineSpatialPoint) :
    (fixedRepairedSpatialPrimalInput space).conjugateMatter =
      (fixedRepairedSpatialInput space).conjugateMatter :=
  rfl

private theorem
    fixedRepairedSpatialPrimalInput_conjugateMatterCoordinateDerivative_origin
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeCoordinates
        (fixedRepairedSpatialPrimalInput space) 0 direction =
      holonomicConjugateMatterDerivativeCoordinates InputActual
        (canonicalCauchySlicePoint 0 space) direction := by
  unfold holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [fixedRepairedSpatialPrimalInput_conjugateMatter_eq_recentered]
  exact
    fixedRepairedSpatialInput_conjugateMatterCoordinateDerivative_origin
      space direction

private theorem
    fixedRepairedSpatialPrimalInput_conjugateMatterDerivative_origin
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        (fixedRepairedSpatialPrimalInput space) 0 direction =
      holonomicConjugateMatterDerivativeDual InputActual
        (canonicalCauchySlicePoint 0 space) direction := by
  unfold holonomicConjugateMatterDerivativeDual
  rw [
    fixedRepairedSpatialPrimalInput_conjugateMatterCoordinateDerivative_origin]

private theorem
    fixedInput_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt InputActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      identityCoframeMatterGeometry := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]
  simpa [identityCoframeMatterGeometry] using
    fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space

private theorem
    fixedRepairedSpatialPrimalInput_coframeFirstJet_origin
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        (fixedRepairedSpatialPrimalInput space).coframe 0 =
      identityCoframeMatterGeometry := by
  unfold fixedRepairedSpatialPrimalInput
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe]
  calc
    holonomicCoframeFirstJetAt (fixedRepairedSpatialInput space).coframe 0 =
        holonomicCoframeFirstJetAt InputActual.coframe
          (canonicalCauchySlicePoint 0 space) := by
      apply coframeJet_eq_of_fields_eq
      · change InputActual.coframe
          (canonicalSpatialContactTranslation space 0) = _
        rw [canonicalSpatialContactTranslation_zero_local]
        rfl
      · funext derivativeDirection internal coordinate
        let component : BasePoint → ℝ := fun point =>
          InputActual.coframe point internal coordinate
        have fieldDifferentiable : DifferentiableAt ℝ component
            (canonicalSpatialContactTranslation space 0) :=
          ((fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
            internal coordinate).differentiable (by simp)).differentiableAt
        have composed :=
          fieldDifferentiable.hasFDerivAt.comp 0
            (canonicalSpatialContactTranslation_hasFDerivAt_local space 0)
        change
          fderiv ℝ
              (component ∘ canonicalSpatialContactTranslation space)
              0 (coordinateDirection derivativeDirection) =
            fderiv ℝ component (canonicalCauchySlicePoint 0 space)
              (coordinateDirection derivativeDirection)
        rw [composed.fderiv]
        simp [canonicalSpatialContactTranslation_zero_local]
    _ = identityCoframeMatterGeometry :=
      fixedInput_coframeFirstJet_zeroSlice space

private theorem
    fixedRepairedSpatialPrimalInput_identityAdjointActionVelocity_origin
    (space : StageNineSpatialPoint) :
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        (fixedRepairedSpatialPrimalInput space) 0 =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity InputActual
        (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    holonomicIdentityCoframeConjugateMatterSpatialTransport
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  simp_rw [
    fixedRepairedSpatialPrimalInput_conjugateMatterDerivative_origin]
  simp [fixedRepairedSpatialPrimalInput,
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual,
    fixedRepairedSpatialInput, spatiallyRecenterHolonomicConfiguration,
    canonicalSpatialContactTranslation_zero_local]

/-- On this fixed P506/L0 contact, the live producer reduces to the legacy
identity presentation because its actual coframe first jet is identity/zero.
This is a readout equality; the producer definition above remains live. -/
private theorem
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite_eq_identity
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite space =
      diracDualIdentityCoframeConjugateMatterTimeResponseWrite
        (fixedRepairedSpatialPrimalInput space) := by
  unfold fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite
  rw [liveCoframeConjugateMatterTimeResponseWrite_eq_rightChiralIdentity_of_firstJet
      _ (fixedRepairedSpatialPrimalInput_coframeFirstJet_origin space),
    ← diracDualIdentityCoframeConjugateMatterTimeResponseWrite_eq_rightChiralIdentity]

private theorem
    fixedRepairedSpatialPrimalInput_liveAdjointActionVelocity_origin
    (space : StageNineSpatialPoint) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (fixedRepairedSpatialPrimalInput space) 0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity InputActual
        (canonicalCauchySlicePoint 0 space) := by
  calc
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          (fixedRepairedSpatialPrimalInput space) 0 =
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          (fixedRepairedSpatialPrimalInput space) 0 :=
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _ (fixedRepairedSpatialPrimalInput_coframeFirstJet_origin space)
    _ = holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          (fixedRepairedSpatialPrimalInput space) 0 :=
      (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity
        _ _).symm
    _ = holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          InputActual (canonicalCauchySlicePoint 0 space) :=
      fixedRepairedSpatialPrimalInput_identityAdjointActionVelocity_origin
        space
    _ = holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          InputActual (canonicalCauchySlicePoint 0 space) :=
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity
        _ _
    _ = holonomicDiracDualLiveCoframeConjugateMatterActionVelocity InputActual
          (canonicalCauchySlicePoint 0 space) :=
      (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _ (fixedInput_coframeFirstJet_zeroSlice space)).symm

/-- The local repaired adjoint correction is the action velocity minus the
temporal raw derivative already carried by the input current. -/
theorem
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite_normalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite space =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity InputActual
          (canonicalCauchySlicePoint 0 space) -
        holonomicConjugateMatterDerivativeDual InputActual
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection := by
  unfold fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite
    liveCoframeConjugateMatterTimeResponseWrite
  rw [fixedRepairedSpatialPrimalInput_liveAdjointActionVelocity_origin,
    fixedRepairedSpatialPrimalInput_conjugateMatterDerivative_origin]

private theorem
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite_identityNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite space =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity InputActual
          (canonicalCauchySlicePoint 0 space) -
        holonomicConjugateMatterDerivativeDual InputActual
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection := by
  rw [
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite_eq_identity]
  unfold diracDualIdentityCoframeConjugateMatterTimeResponseWrite
  rw [fixedRepairedSpatialPrimalInput_identityAdjointActionVelocity_origin,
    fixedRepairedSpatialPrimalInput_conjugateMatterDerivative_origin]

/-! ## Smoothness of the repaired adjoint response family -/

private theorem canonicalZeroSlice_contDiff_local :
    ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
  rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
    funext space
    rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
    simp]
  exact canonicalSpatialInclusion.contDiff

private theorem
    fixedInput_conjugateMatterDerivative_apply_contDiff
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point =>
      holonomicConjugateMatterDerivativeDual InputActual point direction
        matter := by
  rw [show
    (fun point =>
      holonomicConjugateMatterDerivativeDual InputActual point direction
        matter) =
      fun point => ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv matter index *
          holonomicConjugateMatterDerivativeCoordinates InputActual point
            direction index by
    funext point
    exact matterDualOfCoordinates_apply _ _]
  apply ContDiff.sum
  intro index _
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have derivativeCoordinateSmooth : ContDiff ℝ ∞ fun point =>
      holonomicConjugateMatterDerivativeCoordinates InputActual point
        direction index :=
    (projection.restrictScalars ℝ).contDiff.comp
      (holonomicConjugateMatterDerivativeCoordinates_contDiff InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth direction)
  exact contDiff_const.mul derivativeCoordinateSmooth

private theorem varyingConjugateMatterDual_apply_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (vector : BasePoint → DiracExteriorMatterCarrier)
    (vectorSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (vector point)) :
    ContDiff ℝ ∞ fun point =>
      configuration.conjugateMatter point (vector point) := by
  rw [show (fun point =>
      configuration.conjugateMatter point (vector point)) =
    fun point => ∑ index : MatterCoordinateIndex,
      matterCoordinateEquiv (vector point) index *
        configuration.conjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) by
    funext point
    simpa only [matterCoordinateEquiv.symm_apply_apply] using
      matterDual_coordinate_expansion (configuration.conjugateMatter point)
        (matterCoordinateEquiv (vector point))]
  apply ContDiff.sum
  intro index _
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have vectorCoordinateSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (vector point) index :=
    (projection.restrictScalars ℝ).contDiff.comp vectorSmooth
  exact vectorCoordinateSmooth.mul
    (smooth.2.2.2.2.2.2.2.2 index)

private theorem repairedAdjointVelocity_apply_eq_historical_add_seam
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (matter : DiracExteriorMatterCarrier) :
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        configuration point matter =
      StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicIdentityCoframeConjugateMatterActionVelocity
          configuration point matter +
        configuration.conjugateMatter point
          (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm (configuration.scalar point))
              (identityCoframeMatterPrincipal
                canonicalLorentzianTimeDirection matter) -
            chiralExteriorYukawaAction
              (scalarCoordinateEquiv.symm (configuration.scalar point))
              (identityCoframeMatterPrincipal
                canonicalLorentzianTimeDirection matter)) := by
  unfold holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeConjugateMatterSpatialTransport
    holonomicIdentityCoframeMatterConnectionOperator
    holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
    StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicIdentityCoframeConjugateMatterActionVelocity
    StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicIdentityCoframeConjugateMatterKnownDual
    StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicIdentityCoframeMatterAlgebraicOperator
    StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicIdentityCoframeConjugateMatterSpatialTransport
    StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicIdentityCoframeMatterConnectionOperator
    StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicConjugateMatterDerivativeDual
    StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicConjugateMatterDerivativeCoordinates
    StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicConjugateMatterCoordinates
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, map_add, map_sub, map_smul,
    map_sum]
  module

private theorem repairedAdjointYukawaSeam_coordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm (configuration.scalar point)) matter -
          chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (configuration.scalar point))
            matter) := by
  have matterCoordinatesConstant : ContDiff ℝ ∞
      (fun _ : BasePoint => matterCoordinateEquiv matter) :=
    contDiff_const
  have repairedSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          matter) := by
    have actual :=
      (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        smooth.2.2.2.2.2.2.1).clm_apply matterCoordinatesConstant
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv matter))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have historicalSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          matter) := by
    have actual :=
      (chiralExteriorYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        smooth.2.2.2.2.2.2.1).clm_apply matterCoordinatesConstant
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv matter))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  simpa only [map_sub] using repairedSmooth.sub historicalSmooth

theorem holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_apply_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point =>
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        configuration point matter := by
  rw [show
    (fun point =>
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        configuration point matter) =
      (fun point =>
        StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicIdentityCoframeConjugateMatterActionVelocity
          configuration point matter) +
      (fun point =>
        configuration.conjugateMatter point
          (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm (configuration.scalar point))
              (identityCoframeMatterPrincipal
                canonicalLorentzianTimeDirection matter) -
            chiralExteriorYukawaAction
              (scalarCoordinateEquiv.symm (configuration.scalar point))
              (identityCoframeMatterPrincipal
                canonicalLorentzianTimeDirection matter))) by
    funext point
    exact repairedAdjointVelocity_apply_eq_historical_add_seam
      configuration point matter]
  exact
    (StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicIdentityCoframeConjugateMatterActionVelocity_apply_contDiff
      configuration smooth matter).add
      (varyingConjugateMatterDual_apply_contDiff configuration smooth _
        (repairedAdjointYukawaSeam_coordinate_contDiff configuration smooth
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection matter)))

theorem
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun space =>
      fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite space
        matter := by
  rw [show
    (fun space =>
      fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite space
        matter) =
      fun space =>
        holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
            InputActual (canonicalCauchySlicePoint 0 space) matter -
          holonomicConjugateMatterDerivativeDual InputActual
            (canonicalCauchySlicePoint 0 space)
            canonicalLorentzianTimeDirection matter by
    funext space
    rw [
      fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite_identityNormalForm]
    rfl]
  exact
    ((holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_apply_contDiff
      InputActual fixedP506FormNativeJointActionSolvedSuccessor_smooth
      matter).comp canonicalZeroSlice_contDiff_local).sub
      ((fixedInput_conjugateMatterDerivative_apply_contDiff
        canonicalLorentzianTimeDirection matter).comp
          canonicalZeroSlice_contDiff_local)

/-! ## Exact global adjoint normal form -/

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatterCoordinates_normalForm
    (point : BasePoint) :
    matterDualCoordinates (SectionActual.conjugateMatter point) =
      matterDualCoordinates (InputActual.conjugateMatter point) +
        canonicalTimeProjection point •
          matterDualCoordinates
            (fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite
              (canonicalSpatialProjection point)) := by
  rw [← canonicalCauchySlicePoint_projections point]
  change
    matterDualCoordinates
        ((diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
          positiveSmoothUnifiedSource InputActual).conjugateMatter
          (canonicalCauchySlicePoint (canonicalTimeProjection point)
            (canonicalSpatialProjection point))) =
      _
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_slice]
  unfold
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter,
    installConjugateMatterLinearTimeResponse_conjugateMatterCoordinates]
  unfold fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite
    fixedRepairedSpatialPrimalInput
    fixedRepairedSpatialInput
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    conjugateMatterLinearTimeCoordinateWrite
  simp [spatiallyRecenterHolonomicConfiguration,
    canonicalSpatialContactTranslation_timeAxis]

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatter_normalForm
    (point : BasePoint) :
    SectionActual.conjugateMatter point =
      InputActual.conjugateMatter point +
        canonicalTimeProjection point •
          fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite
            (canonicalSpatialProjection point) := by
  calc
    SectionActual.conjugateMatter point =
        matterDualOfCoordinates
          (matterDualCoordinates (SectionActual.conjugateMatter point)) := by
      exact
        (matterDualOfCoordinates_surjective
          (SectionActual.conjugateMatter point)).symm
    _ =
        matterDualOfCoordinates
          (matterDualCoordinates (InputActual.conjugateMatter point) +
            canonicalTimeProjection point •
              matterDualCoordinates
                (fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite
                  (canonicalSpatialProjection point))) := by
      rw [
        fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatterCoordinates_normalForm]
    _ = _ := by
      rw [matterDualOfCoordinates_add, matterDualOfCoordinates_real_smul,
        matterDualOfCoordinates_surjective,
        matterDualOfCoordinates_surjective]

/-! ## Adjoint first jet on the generated slice -/

private theorem canonicalTimeProjection_coordinateDirection_local
    (direction : LorentzianIndex) :
    canonicalTimeProjection (coordinateDirection direction) =
      if direction = canonicalLorentzianTimeDirection then 1 else 0 := by
  fin_cases direction <;>
    simp [canonicalTimeProjection, canonicalLorentzianTimeDirection,
      coordinateDirection, localBaseCoordinate_apply]

private theorem fixedInput_conjugateMatter_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point => InputActual.conjugateMatter point matter := by
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.matterDualCoordinateEvaluation
      matter).restrictScalars ℝ
  have composed : ContDiff ℝ ∞ fun point =>
      evaluation
        (holonomicConjugateMatterCoordinates InputActual point) :=
    evaluation.contDiff.comp
      (holonomicConjugateMatterCoordinates_contDiff InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth)
  rw [show
    (fun point =>
      evaluation (holonomicConjugateMatterCoordinates InputActual point)) =
      fun point => InputActual.conjugateMatter point matter by
    funext point
    dsimp only [evaluation]
    change
      StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.matterDualCoordinateEvaluation
          matter
          (holonomicConjugateMatterCoordinates InputActual point) =
        InputActual.conjugateMatter point matter
    rw [
      StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.matterDualCoordinateEvaluation_apply]
    unfold holonomicConjugateMatterCoordinates
    rw [matterDualOfCoordinates_surjective]] at composed
  exact composed

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatter_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point => SectionActual.conjugateMatter point matter := by
  rw [show
    (fun point => SectionActual.conjugateMatter point matter) =
      (fun point => InputActual.conjugateMatter point matter) +
        (fun point : BasePoint => canonicalTimeProjection point) •
          ((fun space =>
            fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite
              space matter) ∘ canonicalSpatialProjection) by
    funext point
    rw [
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatter_normalForm]
    rfl]
  exact
    (fixedInput_conjugateMatter_apply_contDiff matter).add
      (canonicalTimeProjection.contDiff.smul
        ((fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite_apply_contDiff
          matter).comp canonicalSpatialProjection.contDiff))

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointResponseRegularity
