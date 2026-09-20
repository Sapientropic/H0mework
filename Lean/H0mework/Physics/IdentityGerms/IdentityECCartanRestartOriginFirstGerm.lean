import H0mework.Physics.CartanAction.CartanPointCoframeRegularity
import H0mework.Physics.CartanAction.CartanReactionCurrentRestart
import H0mework.Physics.IdentityGerms.IdentityECNonlinearLeviCivitaFirstGerm
import H0mework.Physics.Holonomic.HolonomicGravityCurvatureFirstGermCongruence

/-!
# Identity-EC Cartan restart origin first-germ seam

Let a current have the identity coframe with zero first jet, and let its
primitive connection already be the action-native Cartan producer on that
same current.  The identity-EC Hessian write then changes the coframe only at
second order and installs the complete affine Levi--Civita first germ.

This module compares the subsequent current-native Cartan restart with that
installed primitive connection.  The proof is deliberately split into:

* the nonlinear Levi--Civita first germ;
* the W13 point--coframe first germ;
* the algebraic KIN-3/KIN-2 contorsion germ; and
* the dependency-light curvature congruence.

No curvature target, settlement, response derivative, residual endpoint, or
branch certificate is accepted.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECCartanRestartOriginFirstGerm

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCartanAffineConnectionActualization
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureFirstGermCongruence
open StageNineLorentzConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! ## The actual identity-plus-quadratic coframe -/

/-- Under the identity/zero-jet lineage, the coframe installed by the Hessian
write is exactly the nonlinear identity-EC quadratic realization used by the
Levi--Civita first-germ theorem. -/
theorem
    identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_eq_quadratic
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1) :
    (identityECHolonomicCoframeHessianIncrementLocalActualLift
      current increment).coframe =
        identityECQuadraticCoframeField increment := by
  funext point internal coordinate
  simp [identityECHolonomicCoframeHessianIncrementLocalActualLift,
    identityECQuadraticCoframeField, coframeFieldOfFirstAndSecondJet,
    affineCoframeFieldOfJet, identityECZeroCoframeFirstJet,
    coframeJetAffineComponentLinear, currentCoframe]

/-- The quadratic coframe installed by the Hessian write has zero Fréchet
first derivative at the origin. -/
theorem
    identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_hasFDerivAt_origin
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1) :
    HasFDerivAt
      (identityECHolonomicCoframeHessianIncrementLocalActualLift
        current increment).coframe
      (0 : BasePoint →L[ℝ] LorentzianCoframe) 0 := by
  rw [
    identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_eq_quadratic
      current increment currentCoframe]
  have zeroAffine :
      coframeJetAffineLinear identityECZeroCoframeFirstJet = 0 := by
    have componentZero
        (internal coordinate : LorentzianIndex) :
        coframeJetAffineComponentLinear identityECZeroCoframeFirstJet
            internal coordinate = 0 := by
      ext point
      simp [coframeJetAffineComponentLinear, identityECZeroCoframeFirstJet]
    ext point internal coordinate
    change
      coframeJetAffineComponentLinear identityECZeroCoframeFirstJet
          internal coordinate point = 0
    rw [componentZero]
    rfl
  simpa only [identityECQuadraticCoframeField,
    zeroAffine,
    map_zero, add_zero] using
    (coframeFieldOfFirstAndSecondJet_hasFDerivAt
      identityECZeroCoframeFirstJet increment 0)

/-- The actual nonlinear Levi--Civita producer on the written coframe has the
same origin first germ as the affine connection increment installed by the
Hessian write. -/
theorem
    identityECHolonomicCoframeHessianIncrementLocalActualLift_leviCivita_firstGerm
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt
            (identityECHolonomicCoframeHessianIncrementLocalActualLift
              current increment).coframe point).lorentzSpinConnection
              formDirection (pairFirst internalPair)
                (pairSecond internalPair))
        0 derivativeDirection =
      fieldDirectionalDerivative
        (fun point =>
          identityECLeviCivitaAffineConnectionIncrement increment point
            formDirection (pairFirst internalPair)
              (pairSecond internalPair))
        0 derivativeDirection := by
  rw [
    identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_eq_quadratic
      current increment currentCoframe]
  exact identityECNonlinearLeviCivitaConnection_firstGerm_eq_affineIncrement
    increment derivativeDirection formDirection internalPair

/-- The nonlinear Levi--Civita component on the written quadratic coframe is
genuinely differentiable at the origin.  This is the regularity side of the
preceding first-germ equality, exposed for downstream affine sums. -/
theorem
    identityECHolonomicCoframeHessianIncrementLocalActualLift_leviCivita_differentiableAt_origin
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1)
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        (holonomicCoframeFirstJetAt
          (identityECHolonomicCoframeHessianIncrementLocalActualLift
            current increment).coframe point).lorentzSpinConnection
              formDirection internalOut internalIn) 0 := by
  rw [
    identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_eq_quadratic
      current increment currentCoframe]
  have functionEquality :
      (fun point =>
        (holonomicCoframeFirstJetAt
          (identityECQuadraticCoframeField increment) point)
            |>.lorentzSpinConnection formDirection internalOut internalIn) =
        (identityECSpinConnectionComponentOfCarrier
          formDirection internalOut internalIn) ∘
            identityECActualQuadraticJetCarrierPath increment := by
    funext point
    rw [holonomicCoframeFirstJetAt_identityECQuadraticCoframeField]
    rfl
  rw [functionEquality]
  have outerAtActual : DifferentiableAt ℝ
      (identityECSpinConnectionComponentOfCarrier
        formDirection internalOut internalIn)
      (identityECActualQuadraticJetCarrierPath increment 0) := by
    simpa using
      (identityECSpinConnectionComponentOfCarrier_differentiableAt
        formDirection internalOut internalIn)
  exact outerAtActual.comp 0
    (identityECActualQuadraticJetCarrierPath_hasFDerivAt_origin
      increment).differentiableAt

/-- The Levi--Civita producer on the identity coframe with zero derivative
vanishes componentwise. -/
theorem identityECZeroCoframeFirstJet_spinConnection_component_eq_zero
    (formDirection internalOut internalIn : LorentzianIndex) :
    identityECSpinConnectionComponentOfCarrier
        formDirection internalOut internalIn
        ((1 : LorentzianCoframe),
          (fun _ _ _ => 0 : LorentzianCoframeDerivative)) = 0 := by
  have frozenAtOrigin :=
    identityECSpinConnectionComponent_frozen_eq_firstGerm
      (0 : CoframeHolonomicSecondJet) 0
        formDirection internalOut internalIn
  simpa [identityECFrozenCoframeJetCarrierPath,
    identityECQuadraticCoframeDerivativeLinear,
    identityECLeviCivitaSpinConnectionFirstGermComponent] using
      frozenAtOrigin

/-- A current whose primitive coframe is constantly the identity has a
vanishing nonlinear Levi--Civita connection at every contact. -/
theorem currentIdentityCoframe_leviCivita_component_eq_zero
    (current : StageNineHolonomicConfiguration)
    (currentCoframe : current.coframe = fun _ => 1)
    (point : BasePoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    (holonomicCoframeFirstJetAt current.coframe point).lorentzSpinConnection
        formDirection internalOut internalIn = 0 := by
  have jetEquality :
      holonomicCoframeFirstJetAt current.coframe point =
        pointwiseCoframeJetOfCarrier
          ((1 : LorentzianCoframe),
            (fun _ _ _ => 0 : LorentzianCoframeDerivative)) := by
    apply coframeJet_eq_of_fields_eq
    · rw [currentCoframe]
      rfl
    · funext derivativeDirection internal coordinate
      rw [currentCoframe]
      unfold holonomicCoframeFirstJetAt pointwiseCoframeJetOfCarrier
      simp
  rw [jetEquality]
  exact identityECZeroCoframeFirstJet_spinConnection_component_eq_zero
    formDirection internalOut internalIn

/-! ## W13 is unchanged to first order -/

private def identityECHessianPointCoframePath
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet) :
    BasePoint → BasePoint × LorentzianCoframe :=
  fun point =>
    (point,
      (identityECHolonomicCoframeHessianIncrementLocalActualLift
        current increment).coframe point)

private def identityECFrozenPointCoframePath :
    BasePoint → BasePoint × LorentzianCoframe :=
  fun point => (point, (1 : LorentzianCoframe))

private theorem identityECHessianPointCoframePath_hasFDerivAt_origin
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1) :
    HasFDerivAt (identityECHessianPointCoframePath current increment)
      ((ContinuousLinearMap.id ℝ BasePoint).prod
        (0 : BasePoint →L[ℝ] LorentzianCoframe)) 0 := by
  exact HasFDerivAt.prodMk (hasFDerivAt_id (x := (0 : BasePoint)))
    (identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_hasFDerivAt_origin
      current increment currentCoframe)

private theorem identityECFrozenPointCoframePath_hasFDerivAt_origin :
    HasFDerivAt identityECFrozenPointCoframePath
      ((ContinuousLinearMap.id ℝ BasePoint).prod
        (0 : BasePoint →L[ℝ] LorentzianCoframe)) 0 := by
  exact HasFDerivAt.prodMk (hasFDerivAt_id (x := (0 : BasePoint)))
    (hasFDerivAt_const (x := (0 : BasePoint))
      (c := (1 : LorentzianCoframe)))

/-- The two W13 response paths have the same complete Fréchet derivative at
the origin.  The statement is kept at the `fderiv` readout layer so the
canonical normed structures of the finite coordinate carriers remain the
single source of analytic instances. -/
theorem
    diracDualFormNativeActionSpinResponseAt_identityECHessian_fderiv_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1)
    (currentSmooth : current.Smooth) :
    fderiv ℝ
        (fun point : BasePoint =>
          diracDualFormNativeActionSpinResponseAt source
            (identityECHolonomicCoframeHessianIncrementLocalActualLift
              current increment) point) 0 =
      fderiv ℝ
        (fun point : BasePoint =>
          diracDualFormNativeActionSpinResponseAt source current point) 0 := by
  let outer :=
    diracDualFormNativeActionSpinResponsePointCoframe source current
  have outerDifferentiable : DifferentiableAt ℝ outer
      ((0 : BasePoint), (1 : LorentzianCoframe)) :=
    (diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
      source current currentSmooth 0 1 (by simp)).differentiableAt (by simp)
  have actualPathDerivative :=
    identityECHessianPointCoframePath_hasFDerivAt_origin
      current increment currentCoframe
  have frozenPathDerivative :=
    identityECFrozenPointCoframePath_hasFDerivAt_origin
  have outerDifferentiableAtActual : DifferentiableAt ℝ outer
      (identityECHessianPointCoframePath current increment 0) := by
    simpa [identityECHessianPointCoframePath, currentCoframe] using
      outerDifferentiable
  have outerDifferentiableAtFrozen : DifferentiableAt ℝ outer
      (identityECFrozenPointCoframePath 0) := by
    simpa [identityECFrozenPointCoframePath] using outerDifferentiable
  have actualFunctionEquality :
      (fun point : BasePoint =>
        diracDualFormNativeActionSpinResponseAt source
          (identityECHolonomicCoframeHessianIncrementLocalActualLift
            current increment) point) =
        outer ∘ identityECHessianPointCoframePath current increment := by
    funext point
    exact
      diracDualFormNativeActionSpinResponseAt_eq_pointCoframe_of_fields_at
        source
        (identityECHolonomicCoframeHessianIncrementLocalActualLift
          current increment)
        current point
        ((identityECHolonomicCoframeHessianIncrementLocalActualLift
          current increment).coframe point)
        rfl rfl rfl
  have frozenFunctionEquality :
      (fun point : BasePoint =>
        diracDualFormNativeActionSpinResponseAt source current point) =
        outer ∘ identityECFrozenPointCoframePath := by
    funext point
    exact
      diracDualFormNativeActionSpinResponseAt_eq_pointCoframe_of_fields_at
        source current current point 1
        (congrFun currentCoframe point) rfl rfl
  have actualCompositionDerivative :=
    outerDifferentiableAtActual.hasFDerivAt.comp
      (0 : BasePoint) actualPathDerivative
  have frozenCompositionDerivative :=
    outerDifferentiableAtFrozen.hasFDerivAt.comp
      (0 : BasePoint) frozenPathDerivative
  rw [actualFunctionEquality, frozenFunctionEquality,
    actualCompositionDerivative.fderiv,
    frozenCompositionDerivative.fderiv]
  simp [identityECHessianPointCoframePath,
    identityECFrozenPointCoframePath, currentCoframe]

/-! ## Origin value of the full Cartan restart -/

/-- W13 also agrees at the origin as a complete response value. -/
theorem
    diracDualFormNativeActionSpinResponseAt_identityECHessian_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet) :
    diracDualFormNativeActionSpinResponseAt source
        (identityECHolonomicCoframeHessianIncrementLocalActualLift
          current increment) 0 =
      diracDualFormNativeActionSpinResponseAt source current 0 := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
  · exact
      identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_origin
        current increment
  · rfl
  · rfl

/-- The algebraic KIN-3/KIN-2 contorsion therefore agrees at the origin. -/
theorem
    diracDualFormNativeActionCartanContorsionAt_identityECHessian_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet) :
    diracDualFormNativeActionCartanContorsionAt source
        (identityECHolonomicCoframeHessianIncrementLocalActualLift
          current increment) 0 =
      diracDualFormNativeActionCartanContorsionAt source current 0 := by
  unfold diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [
    identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_origin,
    diracDualFormNativeActionSpinResponseAt_identityECHessian_origin]

private def identityECHessianCoframeResponsePath
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet) :
    BasePoint → LorentzianCoframe × PhysicalBivectorThreeForm :=
  fun point =>
    ((identityECHolonomicCoframeHessianIncrementLocalActualLift
        current increment).coframe point,
      diracDualFormNativeActionSpinResponseAt source
        (identityECHolonomicCoframeHessianIncrementLocalActualLift
          current increment) point)

private def identityECFrozenCoframeResponsePath
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    BasePoint → LorentzianCoframe × PhysicalBivectorThreeForm :=
  fun point =>
    (current.coframe point,
      diracDualFormNativeActionSpinResponseAt source current point)

/-- The KIN-3/KIN-2 input paths are differentiable and have the same complete
Fréchet derivative.  Their coframe components both have zero first germ, and
their W13 components agree by the preceding action readout. -/
private theorem identityECCoframeResponsePaths_firstGerm
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1)
    (currentSmooth : current.Smooth) :
    DifferentiableAt ℝ
        (identityECHessianCoframeResponsePath source current increment) 0 ∧
      DifferentiableAt ℝ
        (identityECFrozenCoframeResponsePath source current) 0 ∧
      fderiv ℝ
          (identityECHessianCoframeResponsePath source current increment) 0 =
        fderiv ℝ
          (identityECFrozenCoframeResponsePath source current) 0 := by
  have actualCoframeDerivative :=
    identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_hasFDerivAt_origin
      current increment currentCoframe
  have currentCoframeDerivative : HasFDerivAt current.coframe
      (0 : BasePoint →L[ℝ] LorentzianCoframe) 0 := by
    rw [currentCoframe]
    exact hasFDerivAt_const (x := (0 : BasePoint))
      (c := (1 : LorentzianCoframe))
  let pointCoframeOuter :=
    diracDualFormNativeActionSpinResponsePointCoframe source current
  have pointCoframeOuterDifferentiable : DifferentiableAt ℝ pointCoframeOuter
      ((0 : BasePoint), (1 : LorentzianCoframe)) :=
    (diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
      source current currentSmooth 0 1 (by simp)).differentiableAt (by simp)
  have actualPointCoframeDerivative :=
    identityECHessianPointCoframePath_hasFDerivAt_origin
      current increment currentCoframe
  have frozenPointCoframeDerivative :=
    identityECFrozenPointCoframePath_hasFDerivAt_origin
  have outerAtActual : DifferentiableAt ℝ pointCoframeOuter
      (identityECHessianPointCoframePath current increment 0) := by
    simpa [identityECHessianPointCoframePath, currentCoframe] using
      pointCoframeOuterDifferentiable
  have outerAtFrozen : DifferentiableAt ℝ pointCoframeOuter
      (identityECFrozenPointCoframePath 0) := by
    simpa [identityECFrozenPointCoframePath] using
      pointCoframeOuterDifferentiable
  have actualResponseFunctionEquality :
      (fun point : BasePoint =>
        diracDualFormNativeActionSpinResponseAt source
          (identityECHolonomicCoframeHessianIncrementLocalActualLift
            current increment) point) =
        pointCoframeOuter ∘
          identityECHessianPointCoframePath current increment := by
    funext point
    exact
      diracDualFormNativeActionSpinResponseAt_eq_pointCoframe_of_fields_at
        source
        (identityECHolonomicCoframeHessianIncrementLocalActualLift
          current increment)
        current point
        ((identityECHolonomicCoframeHessianIncrementLocalActualLift
          current increment).coframe point)
        rfl rfl rfl
  have frozenResponseFunctionEquality :
      (fun point : BasePoint =>
        diracDualFormNativeActionSpinResponseAt source current point) =
        pointCoframeOuter ∘ identityECFrozenPointCoframePath := by
    funext point
    exact
      diracDualFormNativeActionSpinResponseAt_eq_pointCoframe_of_fields_at
        source current current point 1
        (congrFun currentCoframe point) rfl rfl
  have actualResponseDifferentiable : DifferentiableAt ℝ
      (fun point : BasePoint =>
        diracDualFormNativeActionSpinResponseAt source
          (identityECHolonomicCoframeHessianIncrementLocalActualLift
            current increment) point) 0 := by
    rw [actualResponseFunctionEquality]
    exact outerAtActual.comp (0 : BasePoint)
      actualPointCoframeDerivative.differentiableAt
  have frozenResponseDifferentiable : DifferentiableAt ℝ
      (fun point : BasePoint =>
        diracDualFormNativeActionSpinResponseAt source current point) 0 := by
    rw [frozenResponseFunctionEquality]
    exact outerAtFrozen.comp (0 : BasePoint)
      frozenPointCoframeDerivative.differentiableAt
  have actualInputDifferentiable : DifferentiableAt ℝ
      (identityECHessianCoframeResponsePath source current increment) 0 := by
    exact actualCoframeDerivative.differentiableAt.prodMk
      actualResponseDifferentiable
  have frozenInputDifferentiable : DifferentiableAt ℝ
      (identityECFrozenCoframeResponsePath source current) 0 := by
    exact currentCoframeDerivative.differentiableAt.prodMk
      frozenResponseDifferentiable
  refine ⟨actualInputDifferentiable, frozenInputDifferentiable, ?_⟩
  unfold identityECHessianCoframeResponsePath
    identityECFrozenCoframeResponsePath
  have actualProductDerivative :=
    actualCoframeDerivative.differentiableAt.fderiv_prodMk
      actualResponseDifferentiable
  have frozenProductDerivative :=
    currentCoframeDerivative.differentiableAt.fderiv_prodMk
      frozenResponseDifferentiable
  calc
    _ = (fderiv ℝ
          (identityECHolonomicCoframeHessianIncrementLocalActualLift
            current increment).coframe 0).prod
          (fderiv ℝ
            (fun point : BasePoint =>
              diracDualFormNativeActionSpinResponseAt source
                (identityECHolonomicCoframeHessianIncrementLocalActualLift
                  current increment) point) 0) := by
        exact actualProductDerivative
    _ = (fderiv ℝ current.coframe 0).prod
          (fderiv ℝ
            (fun point : BasePoint =>
              diracDualFormNativeActionSpinResponseAt source current point)
            0) := by
        rw [actualCoframeDerivative.fderiv,
          currentCoframeDerivative.fderiv,
          diracDualFormNativeActionSpinResponseAt_identityECHessian_fderiv_eq
            source current increment currentCoframe currentSmooth]
    _ = _ := by
      exact frozenProductDerivative.symm

/-- Both scalar KIN-3/KIN-2 component paths used in the first-germ comparison
are genuinely differentiable at the origin.  This analytic seam is exposed
separately so downstream linear lifts may transport the already generated
component germ without assuming a response derivative. -/
theorem
    diracDualFormNativeActionCartanContorsionAt_identityECHessian_differentiableAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1)
    (currentSmooth : current.Smooth)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    DifferentiableAt ℝ
        (fun point : BasePoint =>
          diracDualFormNativeActionCartanContorsionAt source
            (identityECHolonomicCoframeHessianIncrementLocalActualLift
              current increment) point formDirection internalPair) 0 ∧
      DifferentiableAt ℝ
        (fun point : BasePoint =>
          diracDualFormNativeActionCartanContorsionAt source current point
            formDirection internalPair) 0 := by
  rcases identityECCoframeResponsePaths_firstGerm
      source current increment currentCoframe currentSmooth with
    ⟨actualInputDifferentiable, frozenInputDifferentiable, _⟩
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have inputOriginEquality :
      identityECHessianCoframeResponsePath source current increment 0 =
        identityECFrozenCoframeResponsePath source current 0 := by
    simp [identityECHessianCoframeResponsePath,
      identityECFrozenCoframeResponsePath,
      diracDualFormNativeActionSpinResponseAt_identityECHessian_origin]
  have outerAtFrozen : DifferentiableAt ℝ outer
      (identityECFrozenCoframeResponsePath source current 0) := by
    simpa [outer, identityECFrozenCoframeResponsePath, currentCoframe] using
      (cartanContorsionCoframeResponseComponent_differentiableAt
        (1 : LorentzianCoframe)
        (diracDualFormNativeActionSpinResponseAt source current 0)
        (by simp) formDirection internalPair)
  have outerAtActual : DifferentiableAt ℝ outer
      (identityECHessianCoframeResponsePath source current increment 0) := by
    rw [inputOriginEquality]
    exact outerAtFrozen
  have actualFunctionEquality :
      (fun point : BasePoint =>
        diracDualFormNativeActionCartanContorsionAt source
          (identityECHolonomicCoframeHessianIncrementLocalActualLift
            current increment) point formDirection internalPair) =
        outer ∘
          identityECHessianCoframeResponsePath source current increment := by
    rfl
  have frozenFunctionEquality :
      (fun point : BasePoint =>
        diracDualFormNativeActionCartanContorsionAt source current point
          formDirection internalPair) =
        outer ∘ identityECFrozenCoframeResponsePath source current := by
    rfl
  constructor
  · rw [actualFunctionEquality]
    exact outerAtActual.comp 0 actualInputDifferentiable
  · rw [frozenFunctionEquality]
    exact outerAtFrozen.comp 0 frozenInputDifferentiable

/-- The scalar KIN-3/KIN-2 component reads have the same complete Fréchet
derivative after the Hessian write. -/
theorem
    diracDualFormNativeActionCartanContorsionAt_identityECHessian_fderiv_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1)
    (currentSmooth : current.Smooth)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fderiv ℝ
        (fun point : BasePoint =>
          diracDualFormNativeActionCartanContorsionAt source
            (identityECHolonomicCoframeHessianIncrementLocalActualLift
              current increment) point formDirection internalPair) 0 =
      fderiv ℝ
        (fun point : BasePoint =>
          diracDualFormNativeActionCartanContorsionAt source current point
            formDirection internalPair) 0 := by
  rcases identityECCoframeResponsePaths_firstGerm
      source current increment currentCoframe currentSmooth with
    ⟨actualInputDifferentiable, frozenInputDifferentiable,
      inputDerivativeEquality⟩
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have inputOriginEquality :
      identityECHessianCoframeResponsePath source current increment 0 =
        identityECFrozenCoframeResponsePath source current 0 := by
    simp [identityECHessianCoframeResponsePath,
      identityECFrozenCoframeResponsePath,
      diracDualFormNativeActionSpinResponseAt_identityECHessian_origin]
  have outerAtFrozen : DifferentiableAt ℝ outer
      (identityECFrozenCoframeResponsePath source current 0) := by
    simpa [outer, identityECFrozenCoframeResponsePath, currentCoframe] using
      (cartanContorsionCoframeResponseComponent_differentiableAt
        (1 : LorentzianCoframe)
        (diracDualFormNativeActionSpinResponseAt source current 0)
        (by simp) formDirection internalPair)
  have outerAtActual : DifferentiableAt ℝ outer
      (identityECHessianCoframeResponsePath source current increment 0) := by
    rw [inputOriginEquality]
    exact outerAtFrozen
  have actualCompositionDerivative :=
    outerAtActual.hasFDerivAt.comp (0 : BasePoint)
      actualInputDifferentiable.hasFDerivAt
  have frozenCompositionDerivative :=
    outerAtFrozen.hasFDerivAt.comp (0 : BasePoint)
      frozenInputDifferentiable.hasFDerivAt
  have actualFunctionEquality :
      (fun point : BasePoint =>
        diracDualFormNativeActionCartanContorsionAt source
          (identityECHolonomicCoframeHessianIncrementLocalActualLift
            current increment) point formDirection internalPair) =
        outer ∘
          identityECHessianCoframeResponsePath source current increment := by
    rfl
  have frozenFunctionEquality :
      (fun point : BasePoint =>
        diracDualFormNativeActionCartanContorsionAt source current point
          formDirection internalPair) =
        outer ∘ identityECFrozenCoframeResponsePath source current := by
    rfl
  rw [actualFunctionEquality, frozenFunctionEquality,
    actualCompositionDerivative.fderiv,
    frozenCompositionDerivative.fderiv,
    inputOriginEquality, inputDerivativeEquality]


end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECCartanRestartOriginFirstGerm
