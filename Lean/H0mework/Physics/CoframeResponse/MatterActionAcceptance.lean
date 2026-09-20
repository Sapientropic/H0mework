import H0mework.Physics.IdentityHessian.CartanECNormalFixedGlobalMatterDualAdjointAcceptance
import H0mework.Physics.CoframeResponse.MatterActionResponse
import H0mework.Physics.RepairedAction.ActionSpatialSectionMatterIdentityCoframeAcceptance

/-!
# Point-local live-coframe adjoint action acceptance

This module turns an already generated live-coframe adjoint action law into
the adjoint Euler readout at the same occurrence when the actual coframe has
the identity complete first jet there.  The calculus hypotheses are local:
only differentiability of the coframe and adjoint coordinates at that point
is consumed.

The proof exposes the matter momentum as a point--coframe function, compares
the actual and frozen-coframe first derivatives, and then reuses the existing
identity-coframe Euler algebra.  It is an acceptance/readout theorem.  No
residual, target derivative, support branch, or successor is supplied to a
constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionAcceptance

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterIdentityCoframeAcceptance
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance liveAcceptanceMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Local regularity of the exposed momentum carrier -/

/-- The exposed point--coframe momentum is differentiable at a nondegenerate
coframe as soon as the actual adjoint coordinates are differentiable at the
same spacetime point. -/
theorem
    matterDifferentialMomentumPointCoframe_differentiableAt_of_conjugateMatterCoordinates
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (matterDifferentialMomentumPointCoframe source configuration
        direction derivativeDirection)
      (point, candidate) := by
  let vector := fun joint : BasePoint × LorentzianCoframe =>
    matterDifferentialVariationVector source joint.1
      (withCoframe
        (toContinuumPointField configuration joint.1) joint.2)
      direction derivativeDirection
  have gammaSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := joint.2, derivative := 0 } derivativeDirection)
      (point, candidate) := by
    have outer :=
      inverseCoframeDiracGamma_contDiffAt
        candidate candidateNondegenerate derivativeDirection
    rw [show
      (fun joint : BasePoint × LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := joint.2, derivative := 0 } derivativeDirection) =
        (fun localCoframe : LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := localCoframe, derivative := 0 }
            derivativeDirection) ∘
          (fun joint : BasePoint × LorentzianCoframe => joint.2) by
      rfl]
    exact outer.comp (point, candidate) contDiffAt_snd
  have vectorCoordinateSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (vector joint))
      (point, candidate) := by
    have actionSmooth :=
      (StageNineDiracMatterCoordinateCalculus.diracMatrixMatterCoordinateRealBilinear
        |>.toContinuousBilinearMap.contDiff.contDiffAt.comp
          (point, candidate) gammaSmooth).clm_apply
        (contDiffAt_const :
          ContDiffAt ℝ ∞
            (fun _ : BasePoint × LorentzianCoframe => direction)
            (point, candidate))
    have withISmooth : ContDiffAt ℝ ∞
        (fun joint : BasePoint × LorentzianCoframe =>
          Complex.I •
            StageNineDiracMatterCoordinateCalculus.diracMatrixMatterCoordinateRealBilinear
              (inverseCoframeDiracGamma
                { coframe := joint.2, derivative := 0 }
                derivativeDirection)
              direction)
        (point, candidate) :=
      (contDiffAt_const :
        ContDiffAt ℝ ∞
          (fun _ : BasePoint × LorentzianCoframe => (Complex.I : ℂ))
          (point, candidate)).smul actionSmooth
    simpa only [vector, matterDifferentialVariationVector, withCoframe,
      StageNineDiracMatterCoordinateCalculus.diracMatrixMatterCoordinateRealBilinear_apply,
      map_smul] using withISmooth
  have pairingDifferentiable : DifferentiableAt ℝ
      (fun joint : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter joint.1 (vector joint))
      (point, candidate) := by
    rw [show
      (fun joint : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter joint.1 (vector joint)) =
      fun joint =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector joint) index *
            configuration.conjugateMatter joint.1
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ))) by
      funext joint
      simpa only [matterCoordinateEquiv.symm_apply_apply] using
        coframeMatterDual_coordinate_expansion
          (configuration.conjugateMatter joint.1)
          (matterCoordinateEquiv (vector joint))]
    apply DifferentiableAt.fun_sum
    intro index _
    let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj index).comp
        (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
    have vectorEntryDifferentiable : DifferentiableAt ℝ
        (fun joint : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv (vector joint) index)
        (point, candidate) := by
      change DifferentiableAt ℝ
        (fun joint : BasePoint × LorentzianCoframe =>
          (projection.restrictScalars ℝ)
            (matterCoordinateEquiv (vector joint)))
        (point, candidate)
      exact
        (projection.restrictScalars ℝ).differentiableAt.comp
          (point, candidate)
          (vectorCoordinateSmooth.differentiableAt (by simp))
    have dualEntryDifferentiable : DifferentiableAt ℝ
        (fun joint : BasePoint × LorentzianCoframe =>
          configuration.conjugateMatter joint.1
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        (point, candidate) := by
      have entryAtPoint : DifferentiableAt ℝ
          (fun localPoint : BasePoint =>
            configuration.conjugateMatter localPoint
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ))))
          point := by
        have projected : DifferentiableAt ℝ
            (fun localPoint : BasePoint =>
              (projection.restrictScalars ℝ)
                (holonomicConjugateMatterCoordinates configuration
                  localPoint))
            point :=
          (projection.restrictScalars ℝ).differentiableAt.comp point
            coordinateDifferentiable
        simpa [projection, holonomicConjugateMatterCoordinates,
          matterDualCoordinates] using projected
      have fstDifferentiable : DifferentiableAt ℝ
          (fun joint : BasePoint × LorentzianCoframe => joint.1)
          (point, candidate) :=
        differentiableAt_fst
      exact
        entryAtPoint.comp (point, candidate) fstDifferentiable
    exact vectorEntryDifferentiable.mul dualEntryDifferentiable
  have volumeDifferentiable : DifferentiableAt ℝ
      (fun joint : BasePoint × LorentzianCoframe =>
        abs (Matrix.det joint.2))
      (point, candidate) :=
    ((coframe_volume_contDiffAt candidate candidateNondegenerate).comp
      (point, candidate) contDiffAt_snd).differentiableAt (by simp)
  unfold matterDifferentialMomentumPointCoframe generatedVolumeDensity
  simp only [withCoframe]
  exact
    volumeDifferentiable.mul
      (Complex.reCLM.differentiableAt.comp
        (point, candidate) pairingDifferentiable)

/-! ## Identity-first-jet transport -/

private theorem coframe_fderiv_coordinate_eq_zero_of_identity_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry)
    (direction : LorentzianIndex) :
    (fderiv ℝ configuration.coframe point)
        (coordinateDirection direction) =
      0 := by
  ext internal coordinate
  let evaluation : LorentzianCoframe →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate :
        (LorentzianIndex → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj internal :
        LorentzianCoframe →L[ℝ] (LorentzianIndex → ℝ))
  have evaluatedDerivative :
      HasFDerivAt
        (fun candidate : BasePoint =>
          evaluation (configuration.coframe candidate))
        (evaluation.comp (fderiv ℝ configuration.coframe point)) point :=
    evaluation.hasFDerivAt.comp point coframeDifferentiable.hasFDerivAt
  have componentDerivativeZero :=
    congrArg
      (fun jet => jet.derivative direction internal coordinate)
      firstJet
  have evaluatedFunctionEquality :
      (fun candidate : BasePoint =>
        evaluation (configuration.coframe candidate)) =
      (fun candidate : BasePoint =>
        configuration.coframe candidate internal coordinate) := by
    funext candidate
    rfl
  have evaluatedZero :
      (fderiv ℝ
          (fun candidate : BasePoint =>
            evaluation (configuration.coframe candidate)) point)
          (coordinateDirection direction) =
        0 := by
    rw [evaluatedFunctionEquality]
    simpa [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry,
      fieldDirectionalDerivative] using componentDerivativeZero
  rw [evaluatedDerivative.fderiv] at evaluatedZero
  change
    evaluation
        ((fderiv ℝ configuration.coframe point)
          (coordinateDirection direction)) =
      0 at evaluatedZero
  exact evaluatedZero

private theorem fderiv_pointCoframe_eq_frozen_of_identity_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry)
    (outer : BasePoint × LorentzianCoframe → ℝ)
    (outerDifferentiable : DifferentiableAt ℝ outer (point, 1))
    (direction : LorentzianIndex) :
    (fderiv ℝ
        (outer ∘ fun candidate =>
          (candidate, configuration.coframe candidate)) point)
        (coordinateDirection direction) =
      (fderiv ℝ
        (outer ∘ fun candidate =>
          (candidate, (1 : LorentzianCoframe))) point)
        (coordinateDirection direction) := by
  have coframeOne : configuration.coframe point = 1 :=
    coframe_eq_one_of_identity_firstJet configuration point firstJet
  have actualInner :
      HasFDerivAt
        (fun candidate : BasePoint =>
          (candidate, configuration.coframe candidate))
        ((ContinuousLinearMap.id ℝ BasePoint).prod
          (fderiv ℝ configuration.coframe point)) point :=
    HasFDerivAt.prodMk (hasFDerivAt_id (x := point))
      coframeDifferentiable.hasFDerivAt
  have frozenInner :
      HasFDerivAt
        (fun candidate : BasePoint =>
          (candidate, (1 : LorentzianCoframe)))
        ((ContinuousLinearMap.id ℝ BasePoint).prod
          (0 : BasePoint →L[ℝ] LorentzianCoframe)) point :=
    HasFDerivAt.prodMk (hasFDerivAt_id (x := point))
      (hasFDerivAt_const (x := point) (c := (1 : LorentzianCoframe)))
  have outerAtActual : DifferentiableAt ℝ outer
      (point, configuration.coframe point) := by
    simpa only [coframeOne] using outerDifferentiable
  have actualComposition := outerAtActual.hasFDerivAt.comp point actualInner
  have frozenComposition := outerDifferentiable.hasFDerivAt.comp point
    frozenInner
  rw [actualComposition.fderiv, frozenComposition.fderiv]
  rw [coframeOne]
  change
    (fderiv ℝ outer (point, 1))
        (coordinateDirection direction,
          (fderiv ℝ configuration.coframe point)
            (coordinateDirection direction)) =
      (fderiv ℝ outer (point, 1)) (coordinateDirection direction, 0)
  rw [coframe_fderiv_coordinate_eq_zero_of_identity_firstJet
    configuration point coframeDifferentiable firstJet direction]

theorem
    matterDifferentialMomentumDerivative_eq_identityCoframeComparison_of_identity_firstJet
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterDifferentialMomentum source configuration direction
          derivativeDirection) point derivativeDirection =
      fieldDirectionalDerivative
        (matterDifferentialMomentum source
          (identityCoframeComparison configuration) direction
          derivativeDirection) point derivativeDirection := by
  let outer :=
    matterDifferentialMomentumPointCoframe source configuration direction
      derivativeDirection
  have actualEq :
      matterDifferentialMomentum source configuration direction
          derivativeDirection =
        outer ∘ fun candidate =>
          (candidate, configuration.coframe candidate) := by
    exact
      matterDifferentialMomentum_eq_pointCoframe_actualSection
        source configuration direction derivativeDirection
  have comparisonEq :
      matterDifferentialMomentum source
          (identityCoframeComparison configuration) direction
          derivativeDirection =
        outer ∘ fun candidate =>
          (candidate, (1 : LorentzianCoframe)) := by
    calc
      _ = matterDifferentialMomentumPointCoframe source
            (identityCoframeComparison configuration) direction
              derivativeDirection ∘
            fun candidate =>
              (candidate,
                (identityCoframeComparison configuration).coframe candidate) :=
        matterDifferentialMomentum_eq_pointCoframe_actualSection
          source (identityCoframeComparison configuration) direction
            derivativeDirection
      _ = _ := by
        rw [
          matterDifferentialMomentumPointCoframe_identityCoframeComparison
            source configuration direction derivativeDirection]
        rfl
  have outerDifferentiable : DifferentiableAt ℝ outer (point, 1) :=
    matterDifferentialMomentumPointCoframe_differentiableAt_of_conjugateMatterCoordinates
      source configuration point 1 (by norm_num) coordinateDifferentiable
      direction derivativeDirection
  unfold fieldDirectionalDerivative
  rw [actualEq, comparisonEq]
  exact
    fderiv_pointCoframe_eq_frozen_of_identity_firstJet configuration point
      coframeDifferentiable firstJet outer outerDifferentiable
      derivativeDirection

theorem
    matterDifferentialMomentumDivergence_eq_identityCoframeComparison_of_identity_firstJet
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence source configuration direction
        point =
      matterDifferentialMomentumDivergence source
        (identityCoframeComparison configuration) direction point := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact
    matterDifferentialMomentumDerivative_eq_identityCoframeComparison_of_identity_firstJet
      source configuration point coframeDifferentiable
      coordinateDifferentiable firstJet direction derivativeDirection

theorem
    diracDualMatterAlgebraicDirectionalCoefficient_eq_identityCoframeComparison_of_identity_firstJet
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient source configuration
        direction point =
      diracDualMatterAlgebraicDirectionalCoefficient source
        (identityCoframeComparison configuration) direction point := by
  have coframeOne :=
    coframe_eq_one_of_identity_firstJet configuration point firstJet
  rw [
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
      source configuration direction point coframeOne,
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
      source (identityCoframeComparison configuration) direction point (by
        rfl)]
  rfl

/-! ## Same-occurrence Euler acceptance -/

private theorem identityCoframeComparison_actionLaw_of_liveActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry)
    (liveLaw :
      HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw configuration
        point
        (holonomicConjugateMatterDerivativeDual configuration point
          canonicalLorentzianTimeDirection)) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      (identityCoframeComparison configuration) point
      (holonomicConjugateMatterDerivativeDual
        (identityCoframeComparison configuration) point
        canonicalLorentzianTimeDirection) := by
  have rightLaw :
      HolonomicDiracDualRightChiralIdentityCoframeConjugateMatterTimeActionLaw
        configuration point
        (holonomicConjugateMatterDerivativeDual configuration point
          canonicalLorentzianTimeDirection) :=
    (holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_iff_rightChiralIdentity_of_firstJet
      configuration point
      (holonomicConjugateMatterDerivativeDual configuration point
        canonicalLorentzianTimeDirection)
      firstJet).1 liveLaw
  have identityLaw :
      HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
        configuration point
        (holonomicConjugateMatterDerivativeDual configuration point
          canonicalLorentzianTimeDirection) := by
    have knownLaw :
        (holonomicConjugateMatterDerivativeDual configuration point
          canonicalLorentzianTimeDirection).comp
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection) =
          holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
            configuration point := by
      rw [
        holonomicDiracDualIdentityCoframeConjugateMatterKnownDual_eq_rightChiralIdentity]
      exact rightLaw
    unfold holonomicDiracDualIdentityCoframeConjugateMatterKnownDual at knownLaw
    unfold HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
    exact (eq_sub_iff_add_eq).mp knownLaw
  have derivativeEquality :
      holonomicConjugateMatterDerivativeDual
          (identityCoframeComparison configuration) point
          canonicalLorentzianTimeDirection =
        holonomicConjugateMatterDerivativeDual configuration point
          canonicalLorentzianTimeDirection := by
    unfold holonomicConjugateMatterDerivativeDual
      holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates identityCoframeComparison
    rfl
  rw [derivativeEquality]
  exact
    (identityCoframeComparison_diracDualTimeActionLaw_iff configuration point
      _).2 identityLaw

/-- Same-occurrence acceptance for a generated live-coframe adjoint action
law at an identity complete coframe first jet. -/
theorem
    holonomicDiracDualMatterEulerLagrange_eq_zero_of_liveActionLaw_identity_firstJet
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe point =
        identityCoframeMatterGeometry)
    (liveLaw :
      HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw configuration
        point
        (holonomicConjugateMatterDerivativeDual configuration point
          canonicalLorentzianTimeDirection))
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
        direction point =
      0 := by
  let comparison := identityCoframeComparison configuration
  have comparisonCoordinatesDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates comparison) point := by
    have coordinatesEquality :
        holonomicConjugateMatterCoordinates comparison =
          holonomicConjugateMatterCoordinates configuration := by
      funext candidate
      unfold comparison identityCoframeComparison
        holonomicConjugateMatterCoordinates
      rfl
    rw [coordinatesEquality]
    exact coordinateDifferentiable
  have comparisonEuler :
      diracDualMatterEulerLagrangeDirectionalCoefficient source comparison
          direction point =
        0 :=
    holonomicDiracDualIdentityCoframeMatterEulerLagrange_eq_zero_of_actionLaw_of_differentiableAt
      source comparison point comparisonCoordinatesDifferentiable
      (identityCoframeComparison_hasIdentityCoframe configuration)
      (identityCoframeComparison_actionLaw_of_liveActionLaw configuration
        point firstJet liveLaw)
      direction
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient at comparisonEuler ⊢
  rw [
    diracDualMatterAlgebraicDirectionalCoefficient_eq_identityCoframeComparison_of_identity_firstJet
      source configuration point firstJet direction,
    matterDifferentialMomentumDivergence_eq_identityCoframeComparison_of_identity_firstJet
      source configuration point coframeDifferentiable
      coordinateDifferentiable firstJet direction]
  exact comparisonEuler

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionAcceptance
