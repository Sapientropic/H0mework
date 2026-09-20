import H0mework.Physics.Coframe.CoframeNativeMatterDualGlobalRadialActionWrite

/-!
# First-germ acceptance of the global frame-radial matter write

The whole-field writer is already premise-free.  This module reads its exact
source germ and accepts the primal and adjoint frame action laws on the same
ordered output.  Local continuity is a readout hypothesis only; it is never
fed back into the constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCoframeNativeMatterDualGlobalRadialActionAcceptance

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeNativeConjugateMatterFrameAction
open StageNineCoframeNativeConjugateMatterOriginActionWrite
open StageNineCoframeNativeMatterDualGlobalRadialActionWrite
open StageNineCoframeNativeMatterFrameAction
open StageNineCoframeNativeMatterOriginActionWrite
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineP286ActionCauchySplit
open StageNineRadialCurveIntegralFirstJet
open DiracCliffordRepresentation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Generated origin germs -/

theorem coframeNativeGlobalMatterRadialIncrement_hasFDerivAt_origin
    (current : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (coframeNativeGlobalMatterResponseOneForm current) 0) :
    HasFDerivAt
      (coframeNativeGlobalMatterRadialIncrement current)
      (coframeNativeGlobalMatterResponseOneForm current 0) 0 := by
  unfold coframeNativeGlobalMatterRadialIncrement
  apply HasFDerivAt.curveIntegral_segment_source'
  filter_upwards [regular.eventually (by simp)] with point pointRegular
  exact pointRegular.continuousAt

theorem coframeNativeGlobalConjugateMatterRadialIncrement_hasFDerivAt_origin
    (current : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm current) 0) :
    HasFDerivAt
      (coframeNativeGlobalConjugateMatterRadialIncrement current)
      (coframeNativeGlobalConjugateMatterResponseOneForm current 0) 0 := by
  unfold coframeNativeGlobalConjugateMatterRadialIncrement
  apply HasFDerivAt.curveIntegral_segment_source'
  filter_upwards [regular.eventually (by simp)] with point pointRegular
  exact pointRegular.continuousAt

/-! ## Primal origin acceptance -/

private theorem globalMatterResponseOneForm_coordinate
    (current : StageNineHolonomicConfiguration)
    (direction : LorentzianIndex) :
    coframeNativeGlobalMatterResponseOneForm current 0
        (coordinateDirection direction) =
      matterCoordinateEquiv
        ((current.coframe 0 0 direction : ℂ) •
          originFrameTimeMatterResponse current) := by
  unfold coframeNativeGlobalMatterResponseOneForm
  rw [globalFrameTimeMatterResponseAt_origin]
  change
    coframeRowLinearFunctional (current.coframe 0)
          (coordinateDirection direction) •
        matterCoordinateEquiv (originFrameTimeMatterResponse current) = _
  rw [coframeRowLinearFunctional_coordinateDirection, map_smul]
  rfl

theorem actionGeneratedGlobalFrameTimeMatterActual_coordinateDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalMatterResponseOneForm current) 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((actionGeneratedGlobalFrameTimeMatterActual current).matter point))
        0 direction =
      fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (current.matter point))
          0 direction +
        matterCoordinateEquiv
          ((current.coframe 0 0 direction : ℂ) •
            originFrameTimeMatterResponse current) := by
  have incrementDerivative :=
    coframeNativeGlobalMatterRadialIncrement_hasFDerivAt_origin
      current responseRegular
  have incrementDifferentiable := incrementDerivative.differentiableAt
  unfold fieldDirectionalDerivative
  rw [show
    (fun point => matterCoordinateEquiv
      ((actionGeneratedGlobalFrameTimeMatterActual current).matter point)) =
        (fun point => matterCoordinateEquiv (current.matter point)) +
          coframeNativeGlobalMatterRadialIncrement current by
    funext point
    exact actionGeneratedGlobalFrameTimeMatterActual_matterCoordinates
      current point]
  rw [fderiv_add matterDifferentiable incrementDifferentiable,
    add_apply, incrementDerivative.fderiv]
  change _ +
      coframeNativeGlobalMatterResponseOneForm current 0
        (coordinateDirection direction) = _
  rw [globalMatterResponseOneForm_coordinate]

theorem
    holonomicMatterCovariantDerivative_actionGeneratedGlobalFrameTimeMatterActual_origin
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalMatterResponseOneForm current) 0)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (actionGeneratedGlobalFrameTimeMatterActual current) 0 direction =
      holonomicMatterCovariantDerivative current 0 direction +
        coframeRowCoordinateMatterResponse (current.coframe 0)
          (originFrameTimeMatterResponse current) direction := by
  unfold holonomicMatterCovariantDerivative
  rw [actionGeneratedGlobalFrameTimeMatterActual_coordinateDerivative_origin
    current matterDifferentiable responseRegular direction]
  simp only [map_add, matterCoordinateEquiv.symm_apply_apply,
    actionGeneratedGlobalFrameTimeMatterActual_gravityConnection,
    actionGeneratedGlobalFrameTimeMatterActual_gaugeConnection,
    actionGeneratedGlobalFrameTimeMatterActual_matter_origin]
  unfold coframeRowCoordinateMatterResponse
  module

theorem actionGeneratedGlobalFrameTimeMatterActual_frameDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalMatterResponseOneForm current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    frameMatterDerivative
        ((actionGeneratedGlobalFrameTimeMatterActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedGlobalFrameTimeMatterActual current) 0) =
      fun internal =>
        frameMatterDerivative (current.coframe 0)
            (holonomicMatterCovariantDerivative current 0) internal +
          frameTimeOnlyMatterResponse
            (originFrameTimeMatterResponse current) internal := by
  rw [actionGeneratedGlobalFrameTimeMatterActual_coframe]
  rw [show
    holonomicMatterCovariantDerivative
        (actionGeneratedGlobalFrameTimeMatterActual current) 0 =
      fun direction =>
        holonomicMatterCovariantDerivative current 0 direction +
          coframeRowCoordinateMatterResponse (current.coframe 0)
            (originFrameTimeMatterResponse current) direction by
    funext direction
    exact
      holonomicMatterCovariantDerivative_actionGeneratedGlobalFrameTimeMatterActual_origin
        current matterDifferentiable responseRegular direction]
  exact frameMatterDerivative_add_coframeRowResponse
    (current.coframe 0) nondegenerate
    (holonomicMatterCovariantDerivative current 0)
    (originFrameTimeMatterResponse current)

theorem actionGeneratedGlobalFrameTimeMatterActual_frameTimeDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalMatterResponseOneForm current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    frameMatterDerivative
        ((actionGeneratedGlobalFrameTimeMatterActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedGlobalFrameTimeMatterActual current) 0) 0 =
      originFrameTimeMatterGeneratedDerivative current := by
  have effect := congrFun
    (actionGeneratedGlobalFrameTimeMatterActual_frameDerivative_origin
      current matterDifferentiable responseRegular nondegenerate)
    (0 : LorentzianIndex)
  simpa [frameTimeOnlyMatterResponse, originFrameTimeMatterResponse] using
    effect

private theorem actionGeneratedGlobalFrameTimeMatterActual_knownVector_origin
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalMatterResponseOneForm current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    frameTimeMatterKnownVector
        ((actionGeneratedGlobalFrameTimeMatterActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedGlobalFrameTimeMatterActual current) 0)
        (scalarCoordinateEquiv.symm
          ((actionGeneratedGlobalFrameTimeMatterActual current).scalar 0))
        ((actionGeneratedGlobalFrameTimeMatterActual current).matter 0) =
      frameTimeMatterKnownVector (current.coframe 0)
        (holonomicMatterCovariantDerivative current 0)
        (scalarCoordinateEquiv.symm (current.scalar 0))
        (current.matter 0) := by
  rw [actionGeneratedGlobalFrameTimeMatterActual_coframe,
    actionGeneratedGlobalFrameTimeMatterActual_scalar,
    actionGeneratedGlobalFrameTimeMatterActual_matter_origin]
  unfold frameTimeMatterKnownVector
  apply congrArg₂ (· + ·)
  · apply congrArg (Complex.I • ·)
    apply Finset.sum_congr rfl
    intro spatial _
    have effect := congrFun
      (actionGeneratedGlobalFrameTimeMatterActual_frameDerivative_origin
        current matterDifferentiable responseRegular nondegenerate)
      spatial.succ
    simpa [frameTimeOnlyMatterResponse] using
      congrArg (diracMatrixMatterAction (diracGamma spatial.succ)) effect
  · rfl

/-- Re-substitution of the emitted origin germ into the same primal frame
action law.  This is producer soundness, not an independent constraint. -/
theorem actionGeneratedGlobalFrameTimeMatterActual_satisfies_actionLaw_origin
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalMatterResponseOneForm current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    FrameTimeMatterActionLaw
      ((actionGeneratedGlobalFrameTimeMatterActual current).coframe 0)
      (holonomicMatterCovariantDerivative
        (actionGeneratedGlobalFrameTimeMatterActual current) 0)
      (scalarCoordinateEquiv.symm
        ((actionGeneratedGlobalFrameTimeMatterActual current).scalar 0))
      ((actionGeneratedGlobalFrameTimeMatterActual current).matter 0)
      (frameMatterDerivative
        ((actionGeneratedGlobalFrameTimeMatterActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedGlobalFrameTimeMatterActual current) 0) 0) := by
  have generatedLaw :=
    originFrameTimeMatterGeneratedDerivative_satisfies_actionLaw current
  unfold OriginFrameTimeMatterActionLaw at generatedLaw
  unfold FrameTimeMatterActionLaw at generatedLaw ⊢
  rw [actionGeneratedGlobalFrameTimeMatterActual_knownVector_origin
      current matterDifferentiable responseRegular nondegenerate,
    actionGeneratedGlobalFrameTimeMatterActual_frameTimeDerivative_origin
      current matterDifferentiable responseRegular nondegenerate]
  exact generatedLaw

/-! ## Adjoint origin acceptance -/

private theorem globalConjugateMatterResponseOneForm_coordinate
    (current : StageNineHolonomicConfiguration)
    (direction : LorentzianIndex) :
    coframeNativeGlobalConjugateMatterResponseOneForm current 0
        (coordinateDirection direction) =
      matterDualCoordinates
        ((current.coframe 0 0 direction : ℂ) •
          originFrameTimeConjugateMatterResponse current) := by
  unfold coframeNativeGlobalConjugateMatterResponseOneForm
  rw [globalFrameTimeConjugateMatterResponseAt_origin]
  change
    coframeRowLinearFunctional (current.coframe 0)
          (coordinateDirection direction) •
        matterDualCoordinates
          (originFrameTimeConjugateMatterResponse current) = _
  rw [coframeRowLinearFunctional_coordinateDirection,
    matterDualCoordinates_smul]
  rfl

theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_coordinateDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm current) 0)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeCoordinates
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current)
        0 direction =
      holonomicConjugateMatterDerivativeCoordinates current 0 direction +
        matterDualCoordinates
          ((current.coframe 0 0 direction : ℂ) •
            originFrameTimeConjugateMatterResponse current) := by
  have incrementDerivative :=
    coframeNativeGlobalConjugateMatterRadialIncrement_hasFDerivAt_origin
      current responseRegular
  have incrementDifferentiable := incrementDerivative.differentiableAt
  unfold holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  rw [show
    holonomicConjugateMatterCoordinates
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current) =
      holonomicConjugateMatterCoordinates current +
        coframeNativeGlobalConjugateMatterRadialIncrement current by
    funext point
    exact actionGeneratedGlobalFrameTimeConjugateMatterActual_coordinates
      current point]
  rw [fderiv_add conjugateDifferentiable incrementDifferentiable, add_apply,
    incrementDerivative.fderiv]
  change _ +
      coframeNativeGlobalConjugateMatterResponseOneForm current 0
        (coordinateDirection direction) = _
  rw [globalConjugateMatterResponseOneForm_coordinate]

theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_derivativeDual_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm current) 0)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current)
        0 direction =
      holonomicConjugateMatterDerivativeDual current 0 direction +
        coframeRowCoordinateConjugateMatterResponse
          (current.coframe 0)
          (originFrameTimeConjugateMatterResponse current) direction := by
  unfold holonomicConjugateMatterDerivativeDual
  rw [actionGeneratedGlobalFrameTimeConjugateMatterActual_coordinateDerivative_origin
    current conjugateDifferentiable responseRegular direction,
    matterDualOfCoordinates_add,
    matterDualOfCoordinates_surjective]
  rfl

theorem actionGeneratedGlobalFrameTimeConjugateMatterActual_frameDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    holonomicFrameConjugateMatterDerivative
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current) 0 =
      fun internal =>
        holonomicFrameConjugateMatterDerivative current 0 internal +
          frameTimeOnlyConjugateMatterResponse
            (originFrameTimeConjugateMatterResponse current) internal := by
  unfold holonomicFrameConjugateMatterDerivative
  rw [actionGeneratedGlobalFrameTimeConjugateMatterActual_coframe]
  rw [show
    holonomicConjugateMatterDerivativeDual
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current) 0 =
      fun direction =>
        holonomicConjugateMatterDerivativeDual current 0 direction +
          coframeRowCoordinateConjugateMatterResponse
            (current.coframe 0)
            (originFrameTimeConjugateMatterResponse current) direction by
    funext direction
    exact
      actionGeneratedGlobalFrameTimeConjugateMatterActual_derivativeDual_origin
        current conjugateDifferentiable responseRegular direction]
  exact frameConjugateMatterDerivative_add_coframeRowResponse
    (current.coframe 0) nondegenerate
    (holonomicConjugateMatterDerivativeDual current 0)
    (originFrameTimeConjugateMatterResponse current)

theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_frameTimeDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    holonomicFrameConjugateMatterDerivative
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current) 0 0 =
      originFrameTimeConjugateMatterGeneratedDerivative current := by
  have effect := congrFun
    (actionGeneratedGlobalFrameTimeConjugateMatterActual_frameDerivative_origin
      current conjugateDifferentiable responseRegular nondegenerate)
    (0 : LorentzianIndex)
  simpa [frameTimeOnlyConjugateMatterResponse,
    originFrameTimeConjugateMatterResponse] using effect

theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_frameSpatialDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (spatial : Fin 3) :
    holonomicFrameConjugateMatterDerivative
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current)
        0 spatial.succ =
      holonomicFrameConjugateMatterDerivative current 0 spatial.succ := by
  have effect := congrFun
    (actionGeneratedGlobalFrameTimeConjugateMatterActual_frameDerivative_origin
      current conjugateDifferentiable responseRegular nondegenerate)
    spatial.succ
  simpa [frameTimeOnlyConjugateMatterResponse] using effect

private theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_pointField_origin
    (current : StageNineHolonomicConfiguration) :
    toContinuumPointField
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current) 0 =
      toContinuumPointField current 0 := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  exact actionGeneratedGlobalFrameTimeConjugateMatterActual_origin current

private theorem actionGeneratedGlobalFrameTimeConjugateMatterActual_drift_origin
    (current : StageNineHolonomicConfiguration)
    (direction : LorentzianIndex) :
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current)
        0 direction =
      holonomicLiveCoframeDensitizedPrincipalDriftCoordinates current
        0 direction := by
  unfold holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
    holonomicLiveCoframeAffineGerm holonomicConjugateMatterCoordinates
  rw [actionGeneratedGlobalFrameTimeConjugateMatterActual_coframe,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_origin]

private theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_algebraicDual_origin
    (current : StageNineHolonomicConfiguration) :
    holonomicDiracDualLiveCoframeAlgebraicDual
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current) 0 =
      holonomicDiracDualLiveCoframeAlgebraicDual current 0 := by
  unfold holonomicDiracDualLiveCoframeAlgebraicDual
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  rw [actionGeneratedGlobalFrameTimeConjugateMatterActual_pointField_origin,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_origin,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_coframe,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_gravityConnection,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_gaugeConnection,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_scalar]

private theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_totalDrift_origin
    (current : StageNineHolonomicConfiguration) :
    holonomicLiveCoframeTotalDensitizedPrincipalDriftDual
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current) 0 =
      holonomicLiveCoframeTotalDensitizedPrincipalDriftDual current 0 := by
  have spatialEq :
      holonomicLiveCoframeSpatialPrincipalDriftCoordinates
          (actionGeneratedGlobalFrameTimeConjugateMatterActual current) 0 =
        holonomicLiveCoframeSpatialPrincipalDriftCoordinates current 0 := by
    unfold holonomicLiveCoframeSpatialPrincipalDriftCoordinates
    apply Finset.sum_congr rfl
    intro direction _
    exact actionGeneratedGlobalFrameTimeConjugateMatterActual_drift_origin
      current direction.succ
  have temporalEq :
      holonomicLiveCoframeTemporalPrincipalDriftCoordinates
          (actionGeneratedGlobalFrameTimeConjugateMatterActual current) 0 =
        holonomicLiveCoframeTemporalPrincipalDriftCoordinates current 0 := by
    unfold holonomicLiveCoframeTemporalPrincipalDriftCoordinates
    exact actionGeneratedGlobalFrameTimeConjugateMatterActual_drift_origin
      current canonicalLorentzianTimeDirection
  unfold holonomicLiveCoframeTotalDensitizedPrincipalDriftDual
  rw [spatialEq, temporalEq]

private theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_spatialPrincipalSum_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    (∑ spatial : Fin 3,
        (holonomicFrameConjugateMatterDerivative
          (actionGeneratedGlobalFrameTimeConjugateMatterActual current)
          0 spatial.succ).comp
            (identityCoframeMatterPrincipal spatial.succ)) =
      ∑ spatial : Fin 3,
        (holonomicFrameConjugateMatterDerivative current 0 spatial.succ).comp
          (identityCoframeMatterPrincipal spatial.succ) := by
  apply Finset.sum_congr rfl
  intro spatial _
  rw [actionGeneratedGlobalFrameTimeConjugateMatterActual_frameSpatialDerivative_origin
    current conjugateDifferentiable responseRegular nondegenerate spatial]

theorem actionGeneratedGlobalFrameTimeConjugateMatterActual_knownDual_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current) 0 =
      holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
        current 0 := by
  unfold holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
  rw [actionGeneratedGlobalFrameTimeConjugateMatterActual_algebraicDual_origin,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_pointField_origin,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_spatialPrincipalSum_origin
      current conjugateDifferentiable responseRegular nondegenerate,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_totalDrift_origin]

/-- Re-substitution of the radial adjoint source germ into the complete
drift-aware frame law on the same emitted actual. -/
theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_satisfies_actionLaw_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (responseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
      (actionGeneratedGlobalFrameTimeConjugateMatterActual current) 0
      (holonomicFrameConjugateMatterDerivative
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current) 0 0) := by
  have generatedLaw :=
    originFrameTimeConjugateMatterGeneratedDerivative_satisfies_actionLaw
      current nondegenerate
  unfold OriginFrameTimeConjugateMatterActionLaw at generatedLaw
  unfold HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
    at generatedLaw ⊢
  rw [actionGeneratedGlobalFrameTimeConjugateMatterActual_pointField_origin,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_knownDual_origin
      current conjugateDifferentiable responseRegular nondegenerate,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_frameTimeDerivative_origin
      current conjugateDifferentiable responseRegular nondegenerate]
  exact generatedLaw

/-! ## Ordered primal–adjoint acceptance on one output -/

private theorem
    holonomicMatterCovariantDerivative_globalConjugateWrite_eq
    (current : StageNineHolonomicConfiguration) :
    holonomicMatterCovariantDerivative
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current) =
      holonomicMatterCovariantDerivative current := by
  funext point direction
  unfold holonomicMatterCovariantDerivative
  rw [actionGeneratedGlobalFrameTimeConjugateMatterActual_gravityConnection,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_gaugeConnection,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_matter]

theorem actionGeneratedGlobalFrameMatterDualActual_primalActionLaw_origin
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (matterResponseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalMatterResponseOneForm current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    FrameTimeMatterActionLaw
      ((actionGeneratedGlobalFrameMatterDualActual current).coframe 0)
      (holonomicMatterCovariantDerivative
        (actionGeneratedGlobalFrameMatterDualActual current) 0)
      (scalarCoordinateEquiv.symm
        ((actionGeneratedGlobalFrameMatterDualActual current).scalar 0))
      ((actionGeneratedGlobalFrameMatterDualActual current).matter 0)
      (frameMatterDerivative
        ((actionGeneratedGlobalFrameMatterDualActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedGlobalFrameMatterDualActual current) 0) 0) := by
  let primal := actionGeneratedGlobalFrameTimeMatterActual current
  change FrameTimeMatterActionLaw
    ((actionGeneratedGlobalFrameTimeConjugateMatterActual primal).coframe 0)
    (holonomicMatterCovariantDerivative
      (actionGeneratedGlobalFrameTimeConjugateMatterActual primal) 0)
    (scalarCoordinateEquiv.symm
      ((actionGeneratedGlobalFrameTimeConjugateMatterActual primal).scalar 0))
    ((actionGeneratedGlobalFrameTimeConjugateMatterActual primal).matter 0)
    (frameMatterDerivative
      ((actionGeneratedGlobalFrameTimeConjugateMatterActual primal).coframe 0)
      (holonomicMatterCovariantDerivative
        (actionGeneratedGlobalFrameTimeConjugateMatterActual primal) 0) 0)
  rw [actionGeneratedGlobalFrameTimeConjugateMatterActual_coframe,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_scalar,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_matter,
    holonomicMatterCovariantDerivative_globalConjugateWrite_eq]
  exact actionGeneratedGlobalFrameTimeMatterActual_satisfies_actionLaw_origin
    current matterDifferentiable matterResponseRegular nondegenerate

theorem actionGeneratedGlobalFrameMatterDualActual_adjointActionLaw_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates
        (actionGeneratedGlobalFrameTimeMatterActual current)) 0)
    (adjointResponseRegular : ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm
        (actionGeneratedGlobalFrameTimeMatterActual current)) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
      (actionGeneratedGlobalFrameMatterDualActual current) 0
      (holonomicFrameConjugateMatterDerivative
        (actionGeneratedGlobalFrameMatterDualActual current) 0 0) := by
  apply
    actionGeneratedGlobalFrameTimeConjugateMatterActual_satisfies_actionLaw_origin
  · exact conjugateDifferentiable
  · exact adjointResponseRegular
  · simpa using nondegenerate

end

end
  SaturationMonoid.PhysicsCore.StageNineCoframeNativeMatterDualGlobalRadialActionAcceptance
