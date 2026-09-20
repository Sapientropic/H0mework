import H0mework.Physics.RepairedAction.ActionSpatialSectionAdjointResponseRegularity

/-!
# Repaired adjoint first jet of the global spatial section

This module reads the first jet of the already-generated repaired adjoint
section.  Named finite coordinate fields prevent elaboration from repeatedly
unfolding the complete action operator.  They do not add data: every
coordinate is definitionally the coordinate readout of the same actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointFirstJet

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointResponseRegularity
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private def SectionActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor

private def InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-- Named faithful coordinates of the action-generated adjoint response. -/
def fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates
    (space : StageNineSpatialPoint) : MatterCoordinateCarrier :=
  matterDualCoordinates
    (fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite space)

/-- Named faithful coordinates of the one generated global section. -/
def fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterDualCoordinates
    (FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.conjugateMatter
      point)

/-- Named coordinates of the live-coframe repaired adjoint action velocity on
the fixed input current. -/
def fixedP506FormNativeRepairedConstitutiveSpatialAdjointVelocityCoordinates
    (space : StageNineSpatialPoint) : MatterCoordinateCarrier :=
  matterDualCoordinates
    (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
      FixedP506FormNativeJointActionSolvedSuccessor
      (canonicalCauchySlicePoint 0 space))

private theorem fixedInput_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        FixedP506FormNativeJointActionSolvedSuccessor.coframe
        (canonicalCauchySlicePoint 0 space) =
      identityCoframeMatterGeometry := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]
  simpa [identityCoframeMatterGeometry] using
    fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space

private theorem fixedInput_liveAdjointActionVelocity_eq_identity
    (space : StageNineSpatialPoint) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        FixedP506FormNativeJointActionSolvedSuccessor
        (canonicalCauchySlicePoint 0 space) =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        FixedP506FormNativeJointActionSolvedSuccessor
        (canonicalCauchySlicePoint 0 space) := by
  calc
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          FixedP506FormNativeJointActionSolvedSuccessor
          (canonicalCauchySlicePoint 0 space) =
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          FixedP506FormNativeJointActionSolvedSuccessor
          (canonicalCauchySlicePoint 0 space) :=
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _ (fixedInput_coframeFirstJet_zeroSlice space)
    _ = holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          FixedP506FormNativeJointActionSolvedSuccessor
          (canonicalCauchySlicePoint 0 space) :=
      (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity
        _ _).symm

/-! ## Finite-coordinate regularity -/

theorem matterDualCoordinates_contDiff_of_basis
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (dualField : E → Module.Dual ℂ DiracExteriorMatterCarrier)
    (basisSmooth : ∀ index : MatterCoordinateIndex,
      ContDiff ℝ ∞ fun point =>
        dualField point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) :
    ContDiff ℝ ∞ fun point => matterDualCoordinates (dualField point) := by
  let assemble : (MatterCoordinateIndex → ℂ) →L[ℝ]
      MatterCoordinateCarrier :=
    (EuclideanSpace.equiv MatterCoordinateIndex ℂ).symm.toContinuousLinearMap
      |>.restrictScalars ℝ
  have coordinateSmooth : ContDiff ℝ ∞ fun point index =>
      dualField point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ))) := by
    apply contDiff_pi'
    exact basisSmooth
  have assembled := assemble.contDiff.comp coordinateSmooth
  change ContDiff ℝ ∞ fun point =>
    (EuclideanSpace.equiv MatterCoordinateIndex ℂ).symm
      (fun index =>
        dualField point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))))
  exact assembled

theorem
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates_contDiff :
    ContDiff ℝ ∞
      fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates := by
  unfold
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates
  exact matterDualCoordinates_contDiff_of_basis _ fun index =>
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite_apply_contDiff
      _

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates_contDiff :
    ContDiff ℝ ∞
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates := by
  unfold
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
  exact matterDualCoordinates_contDiff_of_basis _ fun index =>
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatter_apply_contDiff
      _

private theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates_normalForm
    (point : BasePoint) :
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
        point =
      holonomicConjugateMatterCoordinates
          FixedP506FormNativeJointActionSolvedSuccessor point +
        canonicalTimeProjection point •
          fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates
            (canonicalSpatialProjection point) := by
  unfold
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates
    holonomicConjugateMatterCoordinates
  exact
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatterCoordinates_normalForm
      point

private theorem canonicalTimeProjection_coordinateDirection_local
    (direction : LorentzianIndex) :
    canonicalTimeProjection (coordinateDirection direction) =
      if direction = canonicalLorentzianTimeDirection then 1 else 0 := by
  fin_cases direction <;>
    simp [canonicalTimeProjection, canonicalLorentzianTimeDirection,
      coordinateDirection, localBaseCoordinate_apply]

/-! ## Coordinate and dual first jets -/

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates_firstJet_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
        (canonicalCauchySlicePoint 0 space) direction =
      holonomicConjugateMatterDerivativeCoordinates
          FixedP506FormNativeJointActionSolvedSuccessor
          (canonicalCauchySlicePoint 0 space) direction +
        if direction = canonicalLorentzianTimeDirection then
          fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates
            space
        else
          0 := by
  let point := canonicalCauchySlicePoint 0 space
  let correction : StageNineSpatialPoint → MatterCoordinateCarrier :=
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates
  have baseDerivative :
      HasFDerivAt
        (holonomicConjugateMatterCoordinates
          FixedP506FormNativeJointActionSolvedSuccessor)
        (fderiv ℝ
          (holonomicConjugateMatterCoordinates
            FixedP506FormNativeJointActionSolvedSuccessor) point)
        point :=
    (holonomicConjugateMatterCoordinates_contDiff
      FixedP506FormNativeJointActionSolvedSuccessor
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
      |>.differentiable (by simp) |>.differentiableAt).hasFDerivAt
  have correctionDerivative :
      HasFDerivAt correction (fderiv ℝ correction space) space :=
    (fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates_contDiff
      |>.differentiable (by simp) |>.differentiableAt).hasFDerivAt
  have composedCorrectionDerivative :
      HasFDerivAt (correction ∘ canonicalSpatialProjection)
        ((fderiv ℝ correction space).comp canonicalSpatialProjection)
        point := by
    have atProjection :
        HasFDerivAt correction (fderiv ℝ correction space)
          (canonicalSpatialProjection point) := by
      simpa [point] using correctionDerivative
    exact atProjection.comp point canonicalSpatialProjection.hasFDerivAt
  have linearDerivative :=
    canonicalTimeProjection.hasFDerivAt.smul composedCorrectionDerivative
  have totalDerivative := baseDerivative.add linearDerivative
  have functionEquality :
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates =
        holonomicConjugateMatterCoordinates
            FixedP506FormNativeJointActionSolvedSuccessor +
          (fun candidate : BasePoint =>
            canonicalTimeProjection candidate) •
            (correction ∘ canonicalSpatialProjection) := by
    funext candidate
    exact
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates_normalForm
        candidate
  unfold holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  rw [functionEquality, totalDerivative.fderiv]
  fin_cases direction <;>
    simp [point, correction,
      canonicalTimeProjection_coordinateDirection_local,
      canonicalLorentzianTimeDirection]

private theorem matterDualCoordinates_sub
    (first second : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterDualCoordinates (first - second) =
      matterDualCoordinates first - matterDualCoordinates second := by
  apply PiLp.ext
  intro index
  simp [matterDualCoordinates]

private theorem matterDualCoordinates_matterDualOfCoordinates
    (coordinates : MatterCoordinateCarrier) :
    matterDualCoordinates (matterDualOfCoordinates coordinates) =
      coordinates := by
  apply PiLp.ext
  intro index
  simp [matterDualCoordinates, matterDualOfCoordinates_basis_apply]

private theorem
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates_actionNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates
        space =
      fixedP506FormNativeRepairedConstitutiveSpatialAdjointVelocityCoordinates
          space -
        holonomicConjugateMatterDerivativeCoordinates
          FixedP506FormNativeJointActionSolvedSuccessor
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection := by
  unfold
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointVelocityCoordinates
  rw [
    fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseWrite_normalForm,
    matterDualCoordinates_sub]
  unfold holonomicConjugateMatterDerivativeDual
  rw [matterDualCoordinates_matterDualOfCoordinates]

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatterCoordinateFirstJet_actionNormalForm
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeCoordinates
        FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor
        (canonicalCauchySlicePoint 0 space) direction =
      if direction = canonicalLorentzianTimeDirection then
        fixedP506FormNativeRepairedConstitutiveSpatialAdjointVelocityCoordinates
          space
      else
        holonomicConjugateMatterDerivativeCoordinates
          FixedP506FormNativeJointActionSolvedSuccessor
          (canonicalCauchySlicePoint 0 space) direction := by
  unfold holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  change
    fieldDirectionalDerivative
        fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates
        (canonicalCauchySlicePoint 0 space) direction =
      _
  rw [
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionConjugateCoordinates_firstJet_zeroSlice]
  by_cases temporal : direction = canonicalLorentzianTimeDirection
  · subst direction
    rw [
      fixedP506FormNativeRepairedConstitutiveSpatialAdjointResponseCoordinates_actionNormalForm]
    simp
  · simp only [temporal, if_false, add_zero]
    rfl

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatterFirstJet_actionNormalForm
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor
        (canonicalCauchySlicePoint 0 space) direction =
      if direction = canonicalLorentzianTimeDirection then
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          FixedP506FormNativeJointActionSolvedSuccessor
          (canonicalCauchySlicePoint 0 space)
      else
        holonomicConjugateMatterDerivativeDual
          FixedP506FormNativeJointActionSolvedSuccessor
          (canonicalCauchySlicePoint 0 space) direction := by
  unfold holonomicConjugateMatterDerivativeDual
  rw [
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatterCoordinateFirstJet_actionNormalForm]
  by_cases temporal : direction = canonicalLorentzianTimeDirection
  · simp [temporal,
      fixedP506FormNativeRepairedConstitutiveSpatialAdjointVelocityCoordinates,
      matterDualOfCoordinates_surjective]
  · simp [temporal]

/-! ## Same-section adjoint action law -/

private theorem section_conjugateMatter_zeroSlice
    (space : StageNineSpatialPoint) :
    FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      FixedP506FormNativeJointActionSolvedSuccessor.conjugateMatter
        (canonicalCauchySlicePoint 0 space) := by
  rw [
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatter_normalForm]
  simp [canonicalTimeProjection, canonicalCauchySlicePoint,
    canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem section_gravityConnection_zeroSlice
    (space : StageNineSpatialPoint) :
    FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.gravityConnection
        (canonicalCauchySlicePoint 0 space) =
      FixedP506FormNativeJointActionSolvedSuccessor.gravityConnection
        (canonicalCauchySlicePoint 0 space) := by
  change
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor).gravityConnection
        (canonicalCauchySlicePoint 0 space) =
      _
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityConnection_slice]
  have localOrigin :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  rw [localOrigin,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gravityConnection_zero]
  have translationZero :
      canonicalSpatialContactTranslation space 0 =
        canonicalCauchySlicePoint 0 space := by
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [canonicalSpatialContactTranslation, canonicalCauchySlicePoint,
        canonicalLorentzianTimeDirection, Fin.sum_univ_three]
  simp [spatiallyRecenterHolonomicConfiguration, translationZero]

private theorem section_algebraicOperator_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor
        (canonicalCauchySlicePoint 0 space) =
      holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        FixedP506FormNativeJointActionSolvedSuccessor
        (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  rw [section_gravityConnection_zeroSlice]
  rw [
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor_preservedPrimitives.2.1,
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor_preservedPrimitives.2.2]

private theorem section_spatialTransport_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicIdentityCoframeConjugateMatterSpatialTransport
        FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor
        (canonicalCauchySlicePoint 0 space) =
      holonomicIdentityCoframeConjugateMatterSpatialTransport
        FixedP506FormNativeJointActionSolvedSuccessor
        (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicIdentityCoframeConjugateMatterSpatialTransport
  apply Finset.sum_congr rfl
  intro direction _
  rw [
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatterFirstJet_actionNormalForm]
  simp [canonicalLorentzianTimeDirection]

/-- The same repaired global section satisfies the adjoint action law at
every point of its canonical Cauchy slice. -/
theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_adjointActionLaw_zeroSlice
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor
      (canonicalCauchySlicePoint 0 space)
      (holonomicConjugateMatterDerivativeDual
        FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection) := by
  have generatedLaw :=
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_satisfies
      FixedP506FormNativeJointActionSolvedSuccessor
      (canonicalCauchySlicePoint 0 space)
  unfold HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
    at generatedLaw ⊢
  rw [
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_conjugateMatterFirstJet_actionNormalForm,
    section_spatialTransport_zeroSlice,
    section_conjugateMatter_zeroSlice,
    section_algebraicOperator_zeroSlice]
  simp only [if_pos]
  rw [fixedInput_liveAdjointActionVelocity_eq_identity]
  exact generatedLaw

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointFirstJet
