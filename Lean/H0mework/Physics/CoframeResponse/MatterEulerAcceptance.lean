import H0mework.Physics.CoframeResponse.MatterActionAcceptance
import H0mework.Physics.JointVariation.AdjointTemporalLocalRegularity

/-!
# Live-coframe conjugate-matter Euler acceptance

This module turns the drift-aware live-coframe adjoint action law into the
actual matter Euler–Lagrange zero readout at the same configuration and point.
The coframe-density drift remains part of the generated momentum divergence.
-/

namespace SaturationMonoid.PhysicsCore

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeCompleteJointAdjointTemporalLocalRegularity
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionAcceptance
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

private theorem diracDualMatterAlgebraicDirectionalCoefficient_eq_liveDual
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient source configuration
        direction point =
      (holonomicDiracDualLiveCoframeAlgebraicDual configuration point
        (matterCoordinateEquiv.symm direction)).re := by
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    holonomicDiracDualLiveCoframeAlgebraicDual
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    holonomicMatterVariationAlgebraicDirection
    holonomicIdentityCoframeMatterConnectionOperator
    liveCoframeMatterPrincipal
  simp only [matterDerivativeFrameRelative_zeroChart,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sum, map_smul]
  simp only [toContinuumPointField]
  rw [Finset.smul_sum]
  simp_rw [smul_add]
  norm_num
  ring

private theorem matterDifferentialMomentumPointCoframe_eq_liveCoordinates
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (candidate : LorentzianCoframe)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentumPointCoframe source configuration direction
        derivativeDirection (point, candidate) =
      (matterDualOfCoordinates
        (liveCoframeDensitizedAdjointMomentumCoordinates derivativeDirection
          (candidate,
            holonomicConjugateMatterCoordinates configuration point))
        (matterCoordinateEquiv.symm direction)).re := by
  unfold matterDifferentialMomentumPointCoframe
    liveCoframeDensitizedAdjointMomentumCoordinates
    liveCoframeMatterPrincipal
    matterDifferentialVariationVector
    holonomicConjugateMatterCoordinates
  rw [matterDualOfCoordinates_surjective]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul,
    toContinuumPointField]
  unfold generatedVolumeDensity
  rw [matterDualOfCoordinates_surjective]
  simp only [withCoframe]
  norm_num

private def liveAcceptanceCoframeJetAffineLinear
    (jet : PointwiseLorentzianCoframeJet) :
    BasePoint →L[ℝ] LorentzianCoframe :=
  ContinuousLinearMap.pi fun internal =>
    ContinuousLinearMap.pi fun coordinate =>
      coframeJetAffineComponentLinear jet internal coordinate

private theorem coframeJetAffineLinear_holonomic_apply
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point)
    (direction : LorentzianIndex) :
    coframeJetAffineLinear
        (holonomicCoframeFirstJetAt configuration.coframe point)
        (coordinateDirection direction) =
      (fderiv ℝ configuration.coframe point)
        (coordinateDirection direction) := by
  ext internal coordinate
  change
    coframeJetAffineComponentLinear
        (holonomicCoframeFirstJetAt configuration.coframe point)
        internal coordinate (coordinateDirection direction) = _
  rw [coframeJetAffineComponentLinear_coordinateDirection]
  let evaluation : LorentzianCoframe →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate :
      (LorentzianIndex → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj internal :
        LorentzianCoframe →L[ℝ] (LorentzianIndex → ℝ))
  have derivative : HasFDerivAt
      (fun candidate => evaluation (configuration.coframe candidate))
      (evaluation.comp (fderiv ℝ configuration.coframe point)) point :=
    evaluation.hasFDerivAt.comp point coframeDifferentiable.hasFDerivAt
  change
    (fderiv ℝ (fun candidate =>
      evaluation (configuration.coframe candidate)) point)
        (coordinateDirection direction) =
      evaluation
        ((fderiv ℝ configuration.coframe point)
          (coordinateDirection direction))
  rw [derivative.fderiv]
  rfl

private theorem matterDifferentialMomentumDerivative_split_liveCoframe
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterDifferentialMomentum source configuration direction
          derivativeDirection) point derivativeDirection =
      fieldDirectionalDerivative
          (fun candidate =>
            matterDifferentialMomentumPointCoframe source configuration
              direction derivativeDirection
              (candidate, configuration.coframe point))
          point derivativeDirection +
        fieldDirectionalDerivative
          (fun localPoint =>
            matterDifferentialMomentumPointCoframe source configuration
              direction derivativeDirection
              (point,
                affineCoframeFieldOfJet
                  (holonomicCoframeFirstJetAt configuration.coframe point)
                  localPoint))
          0 derivativeDirection := by
  let outer :=
    matterDifferentialMomentumPointCoframe source configuration direction
      derivativeDirection
  have outerDifferentiable : DifferentiableAt ℝ outer
      (point, configuration.coframe point) :=
    matterDifferentialMomentumPointCoframe_differentiableAt_of_conjugateMatterCoordinates
      source configuration point (configuration.coframe point)
      nondegenerate coordinateDifferentiable direction derivativeDirection
  have actualInner : HasFDerivAt
      (fun candidate : BasePoint =>
        (candidate, configuration.coframe candidate))
      ((ContinuousLinearMap.id ℝ BasePoint).prod
        (fderiv ℝ configuration.coframe point)) point :=
    let coframeDerivative : HasFDerivAt configuration.coframe
        (fderiv ℝ configuration.coframe point) point :=
      coframeDifferentiable.hasFDerivAt
    HasFDerivAt.prodMk (hasFDerivAt_id (x := point)) coframeDerivative
  have frozenInner : HasFDerivAt
      (fun candidate : BasePoint =>
        (candidate, configuration.coframe point))
      ((ContinuousLinearMap.id ℝ BasePoint).prod
        (0 : BasePoint →L[ℝ] LorentzianCoframe)) point :=
    HasFDerivAt.prodMk (hasFDerivAt_id (x := point))
      (hasFDerivAt_const (x := point) (c := configuration.coframe point))
  have coframeInner : HasFDerivAt
      (fun localPoint : BasePoint =>
        (point,
          affineCoframeFieldOfJet
            (holonomicCoframeFirstJetAt configuration.coframe point)
            localPoint))
      ((0 : BasePoint →L[ℝ] BasePoint).prod
        (coframeJetAffineLinear
          (holonomicCoframeFirstJetAt configuration.coframe point))) 0 :=
    HasFDerivAt.prodMk
      (hasFDerivAt_const (x := (0 : BasePoint)) (c := point))
      (affineCoframeFieldOfJet_hasFDerivAt
        (holonomicCoframeFirstJetAt configuration.coframe point) 0)
  have actualComposition :=
    outerDifferentiable.hasFDerivAt.comp point actualInner
  have frozenComposition :=
    outerDifferentiable.hasFDerivAt.comp point frozenInner
  have outerAtCoframePath : DifferentiableAt ℝ outer
      (point,
        affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt configuration.coframe point) 0) := by
    rw [affineCoframeFieldOfJet_origin]
    exact outerDifferentiable
  have coframeComposition :=
    outerAtCoframePath.hasFDerivAt.comp 0 coframeInner
  have actualEq :
      matterDifferentialMomentum source configuration direction
          derivativeDirection =
        outer ∘ fun candidate =>
          (candidate, configuration.coframe candidate) :=
    matterDifferentialMomentum_eq_pointCoframe_actualSection
      source configuration direction derivativeDirection
  have frozenEq :
      (fun candidate =>
        matterDifferentialMomentumPointCoframe source configuration
          direction derivativeDirection
          (candidate, configuration.coframe point)) =
        outer ∘ fun candidate =>
          (candidate, configuration.coframe point) := by
    rfl
  have coframeEq :
      (fun localPoint =>
        matterDifferentialMomentumPointCoframe source configuration
          direction derivativeDirection
          (point,
            affineCoframeFieldOfJet
              (holonomicCoframeFirstJetAt configuration.coframe point)
              localPoint)) =
        outer ∘ fun localPoint =>
          (point,
            affineCoframeFieldOfJet
              (holonomicCoframeFirstJetAt configuration.coframe point)
              localPoint) := by
    rfl
  unfold fieldDirectionalDerivative
  rw [actualEq, frozenEq, coframeEq, actualComposition.fderiv,
    frozenComposition.fderiv, coframeComposition.fderiv]
  rw [affineCoframeFieldOfJet_origin]
  change
    (fderiv ℝ outer (point, configuration.coframe point))
        (coordinateDirection derivativeDirection,
          (fderiv ℝ configuration.coframe point)
            (coordinateDirection derivativeDirection)) =
      (fderiv ℝ outer (point, configuration.coframe point))
          (coordinateDirection derivativeDirection, 0) +
        (fderiv ℝ outer (point, configuration.coframe point))
          (0, coframeJetAffineLinear
            (holonomicCoframeFirstJetAt configuration.coframe point)
            (coordinateDirection derivativeDirection))
  rw [coframeJetAffineLinear_holonomic_apply configuration point
    coframeDifferentiable derivativeDirection]
  rw [← map_add]
  congr 1
  ext <;> simp

private theorem matterDifferentialMomentumFrozenDerivative_eq_transport
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate =>
          matterDifferentialMomentumPointCoframe source configuration
            direction derivativeDirection
            (candidate, configuration.coframe point))
        point derivativeDirection =
      ((((generatedVolumeDensity
          (toContinuumPointField configuration point) : ℝ) : ℂ) •
          (holonomicConjugateMatterDerivativeDual configuration point
            derivativeDirection).comp
              (liveCoframeMatterPrincipal (configuration.coframe point)
                derivativeDirection))
        (matterCoordinateEquiv.symm direction)).re := by
  let vector :=
    liveCoframeMatterPrincipal (configuration.coframe point)
      derivativeDirection (matterCoordinateEquiv.symm direction)
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (matterDualCoordinateEvaluation vector).restrictScalars ℝ
  have evaluationIdentity :
      (fun candidate =>
        configuration.conjugateMatter candidate vector) =
        fun candidate =>
          evaluation
            (holonomicConjugateMatterCoordinates configuration candidate) := by
    funext candidate
    change configuration.conjugateMatter candidate vector =
      matterDualCoordinateEvaluation vector
        (matterDualCoordinates (configuration.conjugateMatter candidate))
    rw [matterDualCoordinateEvaluation_apply,
      matterDualOfCoordinates_surjective]
  have complexDifferentiable : DifferentiableAt ℝ
      (fun candidate =>
        configuration.conjugateMatter candidate vector) point := by
    rw [evaluationIdentity]
    exact evaluation.differentiableAt.comp point coordinateDifferentiable
  have evaluationDifferentiable : DifferentiableAt ℝ
      (fun candidate =>
        (configuration.conjugateMatter candidate vector).re) point := by
    exact Complex.reCLM.differentiableAt.comp point complexDifferentiable
  have frozenIdentity :
      (fun candidate =>
        matterDifferentialMomentumPointCoframe source configuration
          direction derivativeDirection
          (candidate, configuration.coframe point)) =
        fun candidate =>
          generatedVolumeDensity (toContinuumPointField configuration point) *
            (configuration.conjugateMatter candidate vector).re := by
    funext candidate
    rfl
  unfold fieldDirectionalDerivative
  rw [frozenIdentity, fderiv_const_mul evaluationDifferentiable]
  simp only [smul_apply, smul_eq_mul,
    LinearMap.smul_apply, LinearMap.comp_apply]
  change
    generatedVolumeDensity (toContinuumPointField configuration point) *
        fieldDirectionalDerivative
          (fun candidate =>
            (configuration.conjugateMatter candidate vector).re)
          point derivativeDirection = _
  rw [← holonomicConjugateMatterDerivativeDual_apply_re_of_differentiableAt
    configuration point derivativeDirection vector coordinateDifferentiable]
  change _ =
    (((generatedVolumeDensity
      (toContinuumPointField configuration point) : ℝ) : ℂ) *
      holonomicConjugateMatterDerivativeDual configuration point
        derivativeDirection vector).re
  norm_num

private theorem matterDifferentialMomentumCoframeDerivative_eq_drift
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun localPoint =>
          matterDifferentialMomentumPointCoframe source configuration
            direction derivativeDirection
            (point,
              affineCoframeFieldOfJet
                (holonomicCoframeFirstJetAt configuration.coframe point)
                localPoint))
        0 derivativeDirection =
      (matterDualOfCoordinates
        (holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
          configuration point derivativeDirection)
        (matterCoordinateEquiv.symm direction)).re := by
  let jet := holonomicCoframeFirstJetAt configuration.coframe point
  let coordinates := holonomicConjugateMatterCoordinates configuration point
  let coordinatePath : BasePoint → MatterCoordinateCarrier :=
    fun localPoint =>
      liveCoframeDensitizedAdjointMomentumCoordinates derivativeDirection
        (affineCoframeFieldOfJet jet localPoint, coordinates)
  have jetCoframe : jet.coframe = configuration.coframe point := by
    rfl
  have outerDifferentiable : DifferentiableAt ℝ
      (liveCoframeDensitizedAdjointMomentumCoordinates derivativeDirection)
      (configuration.coframe point, coordinates) :=
    (liveCoframeDensitizedAdjointMomentumCoordinates_contDiffAt
      derivativeDirection (configuration.coframe point) coordinates
      nondegenerate).differentiableAt (by simp)
  have coframePathDifferentiable : DifferentiableAt ℝ
      (affineCoframeFieldOfJet jet) 0 := by
    rw [show affineCoframeFieldOfJet jet = fun candidate =>
        jet.coframe + liveAcceptanceCoframeJetAffineLinear jet candidate by
      funext candidate internal coordinate
      rfl]
    exact
      ((liveAcceptanceCoframeJetAffineLinear jet).hasFDerivAt.const_add
        jet.coframe).differentiableAt
  have innerDifferentiable : DifferentiableAt ℝ
      (fun localPoint : BasePoint =>
        (affineCoframeFieldOfJet jet localPoint, coordinates)) 0 :=
    coframePathDifferentiable.prodMk
      (differentiableAt_const (c := coordinates))
  have coordinatePathDifferentiable : DifferentiableAt ℝ coordinatePath 0 := by
    have outerAtInner : DifferentiableAt ℝ
        (liveCoframeDensitizedAdjointMomentumCoordinates derivativeDirection)
        (affineCoframeFieldOfJet jet 0, coordinates) := by
      rw [affineCoframeFieldOfJet_origin, jetCoframe]
      exact outerDifferentiable
    change DifferentiableAt ℝ
      (liveCoframeDensitizedAdjointMomentumCoordinates derivativeDirection ∘
        fun localPoint : BasePoint =>
          (affineCoframeFieldOfJet jet localPoint, coordinates)) 0
    exact outerAtInner.comp 0 innerDifferentiable
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℝ :=
    Complex.reCLM.comp
      ((matterDualCoordinateEvaluation (matterCoordinateEquiv.symm direction)
        ).restrictScalars ℝ)
  have scalarIdentity :
      (fun localPoint =>
        matterDifferentialMomentumPointCoframe source configuration
          direction derivativeDirection
          (point, affineCoframeFieldOfJet jet localPoint)) =
        evaluation ∘ coordinatePath := by
    funext localPoint
    rw [matterDifferentialMomentumPointCoframe_eq_liveCoordinates
      source configuration point (affineCoframeFieldOfJet jet localPoint)
      direction derivativeDirection]
    unfold Function.comp evaluation
    simp only [ContinuousLinearMap.comp_apply]
    change _ =
      (matterDualCoordinateEvaluation (matterCoordinateEquiv.symm direction)
        (coordinatePath localPoint)).re
    rw [matterDualCoordinateEvaluation_apply]
  have evaluatedDerivative :=
    evaluation.hasFDerivAt.comp 0 coordinatePathDifferentiable.hasFDerivAt
  have driftIdentity :
      fieldDirectionalDerivative coordinatePath 0 derivativeDirection =
        holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
          configuration point derivativeDirection := by
    rfl
  unfold fieldDirectionalDerivative
  rw [show
    (fun localPoint =>
      matterDifferentialMomentumPointCoframe source configuration
        direction derivativeDirection
        (point,
          affineCoframeFieldOfJet
            (holonomicCoframeFirstJetAt configuration.coframe point)
            localPoint)) = evaluation ∘ coordinatePath by
      simpa only [jet] using scalarIdentity,
    evaluatedDerivative.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  change evaluation
      (fieldDirectionalDerivative coordinatePath 0 derivativeDirection) = _
  rw [driftIdentity]
  unfold evaluation
  simp only [ContinuousLinearMap.comp_apply]
  change
    (matterDualCoordinateEvaluation (matterCoordinateEquiv.symm direction)
      (holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
        configuration point derivativeDirection)).re = _
  rw [matterDualCoordinateEvaluation_apply]

private theorem matterDifferentialMomentumDerivative_eq_liveTransport_add_drift
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterDifferentialMomentum source configuration direction
          derivativeDirection) point derivativeDirection =
      ((((generatedVolumeDensity
          (toContinuumPointField configuration point) : ℝ) : ℂ) •
          (holonomicConjugateMatterDerivativeDual configuration point
            derivativeDirection).comp
              (liveCoframeMatterPrincipal (configuration.coframe point)
                derivativeDirection))
        (matterCoordinateEquiv.symm direction)).re +
      (matterDualOfCoordinates
        (holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
          configuration point derivativeDirection)
        (matterCoordinateEquiv.symm direction)).re := by
  rw [matterDifferentialMomentumDerivative_split_liveCoframe
    source configuration point coframeDifferentiable coordinateDifferentiable
    nondegenerate direction derivativeDirection]
  rw [matterDifferentialMomentumFrozenDerivative_eq_transport
    source configuration point coordinateDifferentiable direction
    derivativeDirection]
  rw [matterDifferentialMomentumCoframeDerivative_eq_drift
    source configuration point nondegenerate direction derivativeDirection]

private theorem matterDifferentialMomentumDivergence_eq_liveBalance
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence source configuration direction point =
      ((((generatedVolumeDensity
          (toContinuumPointField configuration point) : ℝ) : ℂ) •
          (holonomicConjugateMatterDerivativeDual configuration point
            canonicalLorentzianTimeDirection).comp
              (currentCoframeMatterTemporalPrincipal
                (configuration.coframe point)))
        (matterCoordinateEquiv.symm direction)).re +
      (matterDualOfCoordinates
        (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
          configuration point)
        (matterCoordinateEquiv.symm direction)).re +
      (matterDualOfCoordinates
        (holonomicLiveCoframeSpatialPrincipalDriftCoordinates
          configuration point)
        (matterCoordinateEquiv.symm direction)).re +
      (matterDualOfCoordinates
        (holonomicLiveCoframeTemporalPrincipalDriftCoordinates
          configuration point)
        (matterCoordinateEquiv.symm direction)).re := by
  unfold matterDifferentialMomentumDivergence
  rw [Fin.sum_univ_four]
  simp_rw [matterDifferentialMomentumDerivative_eq_liveTransport_add_drift
    source configuration point coframeDifferentiable coordinateDifferentiable
    nondegenerate direction]
  unfold holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates
  simp [Fin.sum_univ_three, canonicalLorentzianTimeDirection,
    matterDualOfCoordinates_add, matterDualOfCoordinates_surjective,
    LinearMap.add_apply, Complex.add_re]
  have timePrincipal :
      liveCoframeMatterPrincipal (configuration.coframe point) 0 =
        currentCoframeMatterTemporalPrincipal
          (configuration.coframe point) := by
    exact liveCoframeMatterPrincipal_time (configuration.coframe point)
  rw [timePrincipal]
  ring

/-- The live-coframe matter Euler coefficient is the real evaluation of the
densitized adjoint action defect on the same variation. -/
theorem
    diracDualMatterEulerLagrangeDirectionalCoefficient_eq_liveCoframeActionDefect_re
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
        direction point =
      ((holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
            configuration point -
          ((generatedVolumeDensity
              (toContinuumPointField configuration point) : ℂ)) •
            (holonomicConjugateMatterDerivativeDual configuration point
              canonicalLorentzianTimeDirection).comp
              (currentCoframeMatterTemporalPrincipal
                (configuration.coframe point)))
        (matterCoordinateEquiv.symm direction)).re := by
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [diracDualMatterAlgebraicDirectionalCoefficient_eq_liveDual
    source configuration point direction]
  rw [matterDifferentialMomentumDivergence_eq_liveBalance source
    configuration point coframeDifferentiable coordinateDifferentiable
    nondegenerate direction]
  unfold holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Complex.sub_re]
  ring

/-- A generated live-coframe adjoint action law closes the actual adjoint
Euler coefficient at the same nondegenerate occurrence. -/
theorem holonomicDiracDualMatterEulerLagrange_eq_zero_of_liveCoframeActionLaw
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (liveLaw :
      HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw configuration
        point
        (holonomicConjugateMatterDerivativeDual configuration point
          canonicalLorentzianTimeDirection))
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
        direction point = 0 := by
  let vector := matterCoordinateEquiv.symm direction
  have appliedLaw := congrArg
    (fun dual : Module.Dual ℂ DiracExteriorMatterCarrier => (dual vector).re)
    liveLaw
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [diracDualMatterAlgebraicDirectionalCoefficient_eq_liveDual
    source configuration point direction]
  rw [matterDifferentialMomentumDivergence_eq_liveBalance source
    configuration point coframeDifferentiable coordinateDifferentiable
    nondegenerate direction]
  unfold HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual at appliedLaw
  simp only [vector, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, Complex.sub_re] at appliedLaw ⊢
  linarith

end
end SaturationMonoid.PhysicsCore
