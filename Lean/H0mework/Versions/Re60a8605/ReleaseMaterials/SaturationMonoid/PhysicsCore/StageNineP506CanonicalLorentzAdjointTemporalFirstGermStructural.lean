import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermFreshResponseCore
import H0mework.Physics.ConnectionJets.P506CanonicalLorentzAdjointTemporalFirstGermSupport

/-!
# C3h197: structural adjoint temporal first-germ reduction

This module differentiates the adjoint Euler--Lagrange coefficient along the
already generated C3h196 frozen-input affine actual and reduces the result to
finite connection/coframe coordinates.  The multiplier is read from the same
C3h187 action graph through explicit projections.  No fixed-response equality,
second jet, residual inverse, or independent-constraint claim is introduced.

The analytic derivative chain is kept in one module so that the final germ is
tied to the same actual and the same action throughout; numerical stress
evaluation and the final diagnostic are isolated in successor modules.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermStructural

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open StageNineCanonicalCauchyState
open StageNineCanonicalLocalFullActionResponseOperator
open StageNineCoframeSectorStress
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCoframeScalarMatterRegularity
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLinearPlebanskiGravityCoupledCoframeActionResponse
open StageNineCurrentCanonicalFullActionLorentzAdjointCauchyUpdate
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineDynamicBreakingVacuum
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineFullSynchronizedActionResponseOperator
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionVariation
open StageNineMatterPointwiseEquation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalGravityPreservingLorentzDualResponse
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzActualFirstJetLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzP286SpatialCauchyClosure
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzOriginProvenance
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzScalarConstraint
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCompleteFirstGermCanonicalPrimitiveCauchyUpdate
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance c3h197MatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

def c3h196Probe : DiracExteriorMatterCarrier :=
  Complex.I • diracSpinTwoMatterProbe

def c3h196AlgebraicOperator
    (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  holonomicIdentityCoframeMatterAlgebraicOperator c3h196Actual point

theorem c3h196AlgebraicOperator_apply
    (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    c3h196AlgebraicOperator point matter =
      holonomicIdentityCoframeMatterAlgebraicOperator c3h196Actual point
        matter :=
  rfl

abbrev c3h196Velocity
    (space : StageNineSpatialPoint) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  positiveP506MatterCurrentCanonicalLorentzAdjointVelocity space

abbrev c3h196Principal
    (direction : LorentzianIndex) : Module.End ℂ DiracExteriorMatterCarrier :=
  identityCoframeMatterPrincipal direction

theorem c3h196Principal_apply
    (direction : LorentzianIndex) (matter : DiracExteriorMatterCarrier) :
    c3h196Principal direction matter =
      identityCoframeMatterPrincipal direction matter :=
  rfl

def c3h196TimeAxis (time : ℝ) : BasePoint :=
  time • coordinateDirection canonicalLorentzianTimeDirection

def c3h196SpatialDirection (axis : Fin 3) : StageNineSpatialPoint :=
  EuclideanSpace.single axis 1

def c3h196VelocitySpatialDerivative
    (axis : Fin 3) (matter : DiracExteriorMatterCarrier) : ℂ :=
  fderiv ℝ (fun space => c3h196Velocity space matter) 0
    (c3h196SpatialDirection axis)

def c3h196GravityConnectionJet
    (derivativeDirection : LorentzianIndex) :
    PointwiseLorentzSpinConnection :=
  lorentzSkewConnectionOfBivectorOneForm fun formDirection internalPair =>
    linearPlebanskiActionGeneratedLorentzLocalConnectionJet c3h196SeedState 0
      derivativeDirection formDirection internalPair

def c3h196GaugeConnectionJet
    (derivativeDirection formDirection : LorentzianIndex) :
    P286LieBlockData :=
  p286CoordinateEquiv.symm
    (sourceGeneratedP286ActionLocalConnectionJet positiveSmoothUnifiedSource
      c3h196SeedState 0 derivativeDirection formDirection)

def c3h196ConnectionOperatorJet
    (derivativeDirection formDirection : LorentzianIndex) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
      (diracSpinConnectionLift
        (c3h196GravityConnectionJet derivativeDirection) formDirection) +
    diracExteriorMotherLieAction
      (p286LieBlockEmbed
        (c3h196GaugeConnectionJet derivativeDirection formDirection))

def c3h196AlgebraicOperatorJet
    (derivativeDirection : LorentzianIndex) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ formDirection : LorentzianIndex,
      (diracMatrixMatterAction (diracGamma formDirection)).comp
        (c3h196ConnectionOperatorJet derivativeDirection formDirection)

def c3h196AlgebraicTimeDerivative
    (matter : DiracExteriorMatterCarrier) : DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
    (fderiv ℝ
      (fun point => matterCoordinateEquiv
        (c3h196AlgebraicOperator point matter))
      0 (coordinateDirection canonicalLorentzianTimeDirection))

def c3h196AlgebraicSpatialDerivative
    (axis : Fin 3) (matter : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
    (fderiv ℝ
      (fun point => matterCoordinateEquiv
        (c3h196AlgebraicOperator point matter))
      0 (coordinateDirection axis.succ))

def c3h196CauchyAlgebraicSpatialDerivative
    (axis : Fin 3) (matter : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
    (fderiv ℝ
      (fun space => matterCoordinateEquiv
        (actionGeneratedMatterAlgebraicOperator c3h196FinalState space
          matter))
      0 (c3h196SpatialDirection axis))

private theorem c3h196Actual_smooth : c3h196Actual.Smooth := by
  exact
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_smooth

theorem c3h196_gravityConnection_eq_linearPlebanskiGerm :
    c3h196Actual.gravityConnection =
      linearPlebanskiActionGeneratedLorentzLocalConnection
        c3h196SeedState 0 := by
  rw [show c3h196Actual.gravityConnection =
      c3h196PriorActual.gravityConnection by
    exact
      positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_retainsPriorFields.2.1]
  rfl

theorem c3h196_gaugeConnection_eq_sourceGeneratedGerm :
    c3h196Actual.gaugeConnection =
      (sourceGeneratedP286ActionLocalActualLift positiveSmoothUnifiedSource
        c3h196SeedState 0).gaugeConnection := by
  rw [show c3h196Actual.gaugeConnection =
      c3h196PriorActual.gaugeConnection by
    exact
      positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_retainsPriorFields.2.2.2.2.1]
  exact
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gaugeConnection_eq_sourceGenerated

theorem c3h196_scalar_vacuum :
    c3h196Actual.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  rw [show c3h196Actual.scalar = c3h196PriorActual.scalar by
    exact
      positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_retainsPriorFields.2.2.2.2.2.2.1]
  exact
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalar_vacuum

private theorem linearPlebanskiLocalIncrement_axis
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    linearPlebanskiActionGeneratedLorentzLocalIncrement state space
        formDirection internalPair
        (time • coordinateDirection derivativeDirection) =
      time *
        linearPlebanskiActionGeneratedLorentzLocalConnectionJet state space
          derivativeDirection formDirection internalPair := by
  rw [map_smul]
  simp only [smul_eq_mul]
  apply congrArg (fun value : ℝ => time * value)
  calc
    linearPlebanskiActionGeneratedLorentzLocalIncrement state space
          formDirection internalPair
          (coordinateDirection derivativeDirection) =
        fieldDirectionalDerivative
          (fun point =>
            linearPlebanskiActionGeneratedLorentzLocalConnectionCoordinate
              state space point formDirection internalPair)
          0 derivativeDirection :=
      (linearPlebanskiActionGeneratedLorentzLocalConnectionCoordinate_derivative
        state space derivativeDirection formDirection internalPair).symm
    _ = fieldDirectionalDerivative
          (fun point =>
            loweredLorentzConnectionCoefficient
              (linearPlebanskiActionGeneratedLorentzLocalConnection state space
                point)
              formDirection internalPair)
          0 derivativeDirection := by
      apply congrArg (fun field : BasePoint → ℝ =>
        fieldDirectionalDerivative field 0 derivativeDirection)
      funext point
      exact
        (linearPlebanskiActionGeneratedLorentzLocalConnection_loweredCoordinate
          state space point formDirection internalPair).symm
    _ = linearPlebanskiActionGeneratedLorentzLocalConnectionJet state space
          derivativeDirection formDirection internalPair :=
      linearPlebanskiActionGeneratedLorentzLocalConnection_loweredDerivative
        state space derivativeDirection formDirection internalPair

private theorem sourceGeneratedP286LocalIncrement_axis
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (derivativeDirection formDirection : LorentzianIndex) :
    sourceGeneratedP286ActionLocalIncrement source state space formDirection
        (time • coordinateDirection derivativeDirection) =
      time •
        sourceGeneratedP286ActionLocalConnectionJet source state space
          derivativeDirection formDirection := by
  rw [map_smul]
  apply congrArg (fun value : P286CoordinateCarrier => time • value)
  exact
    (sourceGeneratedP286ActionLocalConnectionCoordinate_derivative source state
      space derivativeDirection formDirection).symm.trans
      (sourceGeneratedP286ActionLocalConnection_derivative_eq_jet source state
        space derivativeDirection formDirection)

theorem c3h196_gravityConnection_axis
    (time : ℝ) (derivativeDirection : LorentzianIndex) :
    c3h196Actual.gravityConnection
        (time • coordinateDirection derivativeDirection) =
      c3h196Actual.gravityConnection 0 +
        time • c3h196GravityConnectionJet derivativeDirection := by
  rw [c3h196_gravityConnection_eq_linearPlebanskiGerm,
    linearPlebanskiActionGeneratedLorentzLocalConnection_origin]
  unfold linearPlebanskiActionGeneratedLorentzLocalConnection
  rw [show
    linearPlebanskiActionGeneratedLorentzLocalBivectorIncrement
        c3h196SeedState 0
          (time • coordinateDirection derivativeDirection) =
      time • fun formDirection internalPair =>
        linearPlebanskiActionGeneratedLorentzLocalConnectionJet
          c3h196SeedState 0 derivativeDirection formDirection internalPair by
    funext formDirection internalPair
    exact linearPlebanskiLocalIncrement_axis c3h196SeedState 0 time
      derivativeDirection formDirection internalPair]
  rw [lorentzSkewConnectionOfBivectorOneForm_smul]
  unfold c3h196GravityConnectionJet
  simp

theorem c3h196_gaugeConnection_axis
    (time : ℝ) (derivativeDirection : LorentzianIndex) :
    c3h196Actual.gaugeConnection
        (time • coordinateDirection derivativeDirection) =
      c3h196Actual.gaugeConnection 0 +
        time • fun formDirection =>
          c3h196GaugeConnectionJet derivativeDirection formDirection := by
  rw [c3h196_gaugeConnection_eq_sourceGeneratedGerm]
  funext formDirection
  unfold sourceGeneratedP286ActionLocalActualLift
    sourceGeneratedP286ActionLocalConnection
    sourceGeneratedP286ActionLocalConnectionCoordinate
    c3h196GaugeConnectionJet
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [← p286CoordinateEquiv.symm.map_smul,
    ← p286CoordinateEquiv.symm.map_add]
  apply p286CoordinateEquiv.injective
  simp only [p286CoordinateEquiv.apply_symm_apply]
  rw [sourceGeneratedP286LocalIncrement_axis]
  simp [sourceGeneratedP286ActionLocalIncrement]

theorem c3h196ConnectionOperator_axis_apply
    (time : ℝ) (derivativeDirection formDirection : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    holonomicIdentityCoframeMatterConnectionOperator c3h196Actual
        (time • coordinateDirection derivativeDirection) formDirection matter =
      holonomicIdentityCoframeMatterConnectionOperator c3h196Actual 0
          formDirection matter +
        (time : ℂ) •
          c3h196ConnectionOperatorJet derivativeDirection formDirection
            matter := by
  unfold holonomicIdentityCoframeMatterConnectionOperator
    c3h196ConnectionOperatorJet
  rw [c3h196_gravityConnection_axis time derivativeDirection,
    c3h196_gaugeConnection_axis time derivativeDirection]
  simp only [Pi.add_apply, Pi.smul_apply, LinearMap.add_apply,
    diracSpinConnectionLift_add, diracSpinConnectionLift_real_smul,
    p286LieBlockEmbed_add,
    StageNineP286GaugeConnectionVariation.p286LieBlockEmbed_real_smul,
    StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_add,
    StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_real_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [diracMatrixMatterAction_add_matrix,
    diracMatrixMatterAction_smul_matrix, LinearMap.smul_apply, smul_add]
  module

theorem c3h196AlgebraicOperator_axis_apply
    (time : ℝ) (derivativeDirection : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    c3h196AlgebraicOperator
        (time • coordinateDirection derivativeDirection) matter =
      c3h196AlgebraicOperator 0 matter +
        (time : ℂ) •
          c3h196AlgebraicOperatorJet derivativeDirection matter := by
  unfold c3h196AlgebraicOperator
    holonomicIdentityCoframeMatterAlgebraicOperator
    c3h196AlgebraicOperatorJet
  rw [c3h196_scalar_vacuum]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, Pi.zero_apply]
  simp_rw [c3h196ConnectionOperator_axis_apply time derivativeDirection]
  simp only [map_add, map_smul, Finset.sum_add_distrib,
    smul_add, Finset.smul_sum, smul_smul]
  rw [mul_comm Complex.I (time : ℂ)]
  abel

theorem c3h196SeedState_gravityAuxiliary_simple
    (space : StageNineSpatialPoint) :
    c3h196SeedState.gravityAuxiliary space =
      physicalIIPlusBivector 1 := by
  unfold c3h196SeedState
  exact
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gravityAuxiliary_simple
      space

theorem c3h196SeedState_gravitySpatialDerivative_zero
    (axis : Fin 3) (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    cauchyLoweredLorentzSpatialConnectionDerivativeCoordinate
        c3h196SeedState 0 axis formDirection internalPair = 0 := by
  unfold cauchyLoweredLorentzSpatialConnectionDerivativeCoordinate
  rw [show
    (fun candidate =>
      minkowskiInternalSign (pairFirst internalPair) *
        c3h196SeedState.gravityConnection candidate formDirection
          (pairFirst internalPair) (pairSecond internalPair)) =
      fun _ : StageNineSpatialPoint =>
        minkowskiInternalSign (pairFirst internalPair) *
          (lorentzSkewConnectionOfBivectorOneForm
            positiveP506MatterCurrentEinsteinCartanContorsionCoordinates)
            formDirection (pairFirst internalPair)
              (pairSecond internalPair) by
    funext candidate
    unfold c3h196SeedState
    rw [positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gravityConnection_contorsion]]
  simp

theorem c3h196_gravityConnection_origin_contorsion :
    c3h196Actual.gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveP506MatterCurrentEinsteinCartanContorsionCoordinates := by
  rw [c3h196_gravityConnection_eq_linearPlebanskiGerm]
  rw [linearPlebanskiActionGeneratedLorentzLocalConnection_origin]
  unfold c3h196SeedState
  exact
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gravityConnection_contorsion
      0

theorem c3h196_gaugeConnection_origin_zero :
    c3h196Actual.gaugeConnection 0 = 0 := by
  rw [c3h196_gaugeConnection_eq_sourceGeneratedGerm]
  funext direction
  change
    sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
        c3h196SeedState 0 0 direction =
      0
  rw [sourceGeneratedP286ActionLocalConnection_origin]
  unfold c3h196SeedState
  exact
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeConnection_origin_zero
      direction

theorem c3h196AlgebraicOperator_origin_apply_normalForm
    (matter : DiracExteriorMatterCarrier) :
    c3h196AlgebraicOperator 0 matter =
      Complex.I •
          ∑ direction : LorentzianIndex,
            diracMatrixMatterAction (diracGamma direction)
              (diracMatrixMatterAction
                (diracSpinConnectionLift
                  (lorentzSkewConnectionOfBivectorOneForm
                    positiveP506MatterCurrentEinsteinCartanContorsionCoordinates)
                  direction)
                matter) +
        chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm
            (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
          matter := by
  unfold c3h196AlgebraicOperator
    holonomicIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  rw [c3h196_gravityConnection_origin_contorsion,
    c3h196_gaugeConnection_origin_zero, c3h196_scalar_vacuum]
  simp only [Pi.zero_apply, p286LieBlockEmbed_zero,
    diracExteriorMotherLieAction_zero_matrix,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, add_zero]

private theorem fixedMatterDual_fderiv_eq_coordinateFderiv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (field : X → DiracExteriorMatterCarrier)
    (point direction : X)
    (smooth : ContDiff ℝ ∞ (fun candidate =>
      matterCoordinateEquiv (field candidate))) :
    fderiv ℝ (fun candidate => dual (field candidate)) point direction =
      dual (matterCoordinateEquiv.symm
        (fderiv ℝ (fun candidate =>
          matterCoordinateEquiv (field candidate)) point direction)) := by
  let evaluationLinear : MatterCoordinateCarrier →ₗ[ℂ] ℂ :=
    dual.comp matterCoordinateEquiv.symm.toLinearMap
  let evaluation : MatterCoordinateCarrier →L[ℂ] ℂ :=
    ⟨evaluationLinear,
      evaluationLinear.continuous_of_finiteDimensional⟩
  have coordinateDifferentiable : DifferentiableAt ℝ
      (fun candidate => matterCoordinateEquiv (field candidate)) point :=
    (smooth.differentiable (by simp)).differentiableAt
  have derivative := (evaluation.restrictScalars ℝ).hasFDerivAt.comp point
    coordinateDifferentiable.hasFDerivAt
  have functionEquality :
      (fun candidate => dual (field candidate)) =
        evaluation.restrictScalars ℝ ∘
          (fun candidate => matterCoordinateEquiv (field candidate)) := by
    funext candidate
    change dual (field candidate) =
      dual (matterCoordinateEquiv.symm
        (matterCoordinateEquiv (field candidate)))
    rw [matterCoordinateEquiv.symm_apply_apply]
  rw [functionEquality, derivative.fderiv]
  rfl

private theorem c3h196_zeroSlice :
    canonicalCauchyRestriction 0 c3h196Actual = c3h196FinalState := by
  unfold c3h196Actual c3h196FinalState
  exact
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_zeroSlice

@[simp] theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem c3h196AlgebraicOperator_origin_eq_cauchy :
    c3h196AlgebraicOperator 0 =
      actionGeneratedMatterAlgebraicOperator c3h196FinalState 0 := by
  have gravity := congrArg
    (fun state : StageNineCauchyState => state.gravityConnection 0)
    c3h196_zeroSlice
  have gauge := congrArg
    (fun state : StageNineCauchyState => state.gaugeConnection 0)
    c3h196_zeroSlice
  have scalar := congrArg
    (fun state : StageNineCauchyState => state.scalar 0)
    c3h196_zeroSlice
  change c3h196Actual.gravityConnection
      (canonicalCauchySlicePoint 0 0) =
    c3h196FinalState.gravityConnection 0 at gravity
  change c3h196Actual.gaugeConnection
      (canonicalCauchySlicePoint 0 0) =
    c3h196FinalState.gaugeConnection 0 at gauge
  change c3h196Actual.scalar (canonicalCauchySlicePoint 0 0) =
    c3h196FinalState.scalar 0 at scalar
  simp only [canonicalCauchySlicePoint_zero_zero] at gravity gauge scalar
  unfold c3h196AlgebraicOperator
    holonomicIdentityCoframeMatterAlgebraicOperator
    actionGeneratedMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
    cauchyMatterVariationConnectionOperator
  rw [gravity, gauge, scalar]

theorem c3h196AlgebraicOperator_zeroSlice
    (space : StageNineSpatialPoint) :
    c3h196AlgebraicOperator (canonicalCauchySlicePoint 0 space) =
      actionGeneratedMatterAlgebraicOperator c3h196FinalState space := by
  have gravity := congrArg
    (fun state : StageNineCauchyState => state.gravityConnection space)
    c3h196_zeroSlice
  have gauge := congrArg
    (fun state : StageNineCauchyState => state.gaugeConnection space)
    c3h196_zeroSlice
  have scalar := congrArg
    (fun state : StageNineCauchyState => state.scalar space)
    c3h196_zeroSlice
  change c3h196Actual.gravityConnection
      (canonicalCauchySlicePoint 0 space) =
    c3h196FinalState.gravityConnection space at gravity
  change c3h196Actual.gaugeConnection
      (canonicalCauchySlicePoint 0 space) =
    c3h196FinalState.gaugeConnection space at gauge
  change c3h196Actual.scalar (canonicalCauchySlicePoint 0 space) =
    c3h196FinalState.scalar space at scalar
  unfold c3h196AlgebraicOperator
    holonomicIdentityCoframeMatterAlgebraicOperator
    actionGeneratedMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
    cauchyMatterVariationConnectionOperator
  rw [gravity, gauge, scalar]

theorem c3h196CauchyAlgebraicSpatialDerivative_eq_holonomic
    (axis : Fin 3) (matter : DiracExteriorMatterCarrier) :
    c3h196CauchyAlgebraicSpatialDerivative axis matter =
      c3h196AlgebraicSpatialDerivative axis matter := by
  have outerDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv
        (c3h196AlgebraicOperator point matter)) 0 := by
    exact
      ((by
        unfold c3h196AlgebraicOperator
        exact
          holonomicIdentityCoframeMatterAlgebraicOperator_coordinate_contDiff
            c3h196Actual c3h196Actual_smooth matter :
        ContDiff ℝ ∞ (fun point => matterCoordinateEquiv
          (c3h196AlgebraicOperator point matter))).differentiable
        (by simp)).differentiableAt
  have outerDifferentiableAtSlice : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv
        (c3h196AlgebraicOperator point matter))
      (canonicalCauchySlicePoint 0 0) := by
    simpa only [canonicalCauchySlicePoint_zero_zero] using outerDifferentiable
  have sliceDerivative := outerDifferentiableAtSlice.hasFDerivAt.comp
    (0 : StageNineSpatialPoint)
    (canonicalCauchySlicePoint_hasFDerivAt 0 0)
  rw [canonicalCauchySlicePoint_zero_zero] at sliceDerivative
  have functionEquality :
      (fun space => matterCoordinateEquiv
        (actionGeneratedMatterAlgebraicOperator c3h196FinalState space
          matter)) =
      (fun point => matterCoordinateEquiv
        (c3h196AlgebraicOperator point matter)) ∘
          canonicalCauchySlicePoint 0 := by
    funext space
    simp only [Function.comp_apply]
    rw [c3h196AlgebraicOperator_zeroSlice]
  unfold c3h196CauchyAlgebraicSpatialDerivative
    c3h196AlgebraicSpatialDerivative
  apply congrArg matterCoordinateEquiv.symm
  rw [functionEquality, sliceDerivative.fderiv]
  change
    fderiv ℝ
          (fun point => matterCoordinateEquiv
            (c3h196AlgebraicOperator point matter))
          0
          (canonicalSpatialInclusion (c3h196SpatialDirection axis)) =
      fderiv ℝ
          (fun point => matterCoordinateEquiv
            (c3h196AlgebraicOperator point matter))
          0 (coordinateDirection axis.succ)
  rw [show c3h196SpatialDirection axis =
      canonicalSpatialCoordinateDirection axis by rfl,
    canonicalSpatialInclusion_coordinateDirection]

theorem c3h196_conjugateMatter_apply_normalForm
    (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    c3h196Actual.conjugateMatter point matter =
      diracSpinZeroMatterCoordinate matter +
        canonicalTimeProjection point •
          c3h196Velocity (canonicalSpatialProjection point) matter := by
  unfold c3h196Actual
  rw [show
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual.conjugateMatter
        point matter =
      (positiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate
        (canonicalTimeProjection point)).conjugateMatter
          (canonicalSpatialProjection point) matter by
    rfl]
  unfold positiveP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate
  rw [currentCanonicalFullActionLorentzAdjointCauchyUpdate_conjugateMatter_apply]
  change
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0).conjugateMatter
          (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))
          matter +
        canonicalTimeProjection point •
          c3h196Velocity (canonicalSpatialProjection point) matter = _
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_conjugateMatter_canonicalZeroSlice]

theorem c3h196Velocity_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun space => c3h196Velocity space matter) := by
  rw [show
    (fun space => c3h196Velocity space matter) =
      fun space => diracSpinZeroMatterCoordinate
        (actionGeneratedMatterAlgebraicOperator
          positiveP506MatterCurrentCanonicalLorentzFinalCauchyState space
          (c3h196Principal canonicalLorentzianTimeDirection matter)) by
    funext space
    exact positiveVelocity_apply_eq_algebraic space matter]
  exact fixedMatterDual_apply_coordinate_contDiff
    diracSpinZeroMatterCoordinate _
    (positiveFinalState_algebraicResponse_coordinate_contDiff
      (c3h196Principal canonicalLorentzianTimeDirection matter))

theorem c3h196Velocity_apply_eq_cauchyAlgebraic
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier) :
    c3h196Velocity space matter =
      diracSpinZeroMatterCoordinate
        (actionGeneratedMatterAlgebraicOperator c3h196FinalState space
          (c3h196Principal canonicalLorentzianTimeDirection matter)) := by
  unfold c3h196Velocity c3h196FinalState c3h196Principal
  exact positiveVelocity_apply_eq_algebraic space matter

theorem c3h196Velocity_origin_algebraicOperator :
    c3h196Velocity 0
        (c3h196AlgebraicOperator 0 c3h196Probe) =
      diracSpinZeroMatterCoordinate
        (c3h196AlgebraicOperator 0
          (c3h196Principal canonicalLorentzianTimeDirection
            (c3h196AlgebraicOperator 0 c3h196Probe))) := by
  rw [c3h196Velocity_apply_eq_cauchyAlgebraic]
  rw [← c3h196AlgebraicOperator_origin_eq_cauchy]

theorem c3h196VelocitySpatialDerivative_eq_algebraicSpatialDerivative
    (axis : Fin 3) (matter : DiracExteriorMatterCarrier) :
    c3h196VelocitySpatialDerivative axis matter =
      diracSpinZeroMatterCoordinate
        (c3h196CauchyAlgebraicSpatialDerivative axis
          (c3h196Principal canonicalLorentzianTimeDirection matter)) := by
  unfold c3h196VelocitySpatialDerivative
  rw [show
    (fun space => c3h196Velocity space matter) =
      fun space => diracSpinZeroMatterCoordinate
        (actionGeneratedMatterAlgebraicOperator c3h196FinalState space
          (c3h196Principal canonicalLorentzianTimeDirection matter)) by
    funext space
    exact c3h196Velocity_apply_eq_cauchyAlgebraic space matter]
  unfold c3h196CauchyAlgebraicSpatialDerivative
  apply fixedMatterDual_fderiv_eq_coordinateFderiv
  unfold c3h196FinalState
  exact positiveFinalState_algebraicResponse_coordinate_contDiff _

theorem c3h196_conjugateMatter_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun point => c3h196Actual.conjugateMatter point matter) := by
  rw [show
    (fun point => c3h196Actual.conjugateMatter point matter) = fun point =>
      diracSpinZeroMatterCoordinate matter +
        canonicalTimeProjection point •
          c3h196Velocity (canonicalSpatialProjection point) matter by
    funext point
    exact c3h196_conjugateMatter_apply_normalForm point matter]
  exact contDiff_const.add
    (canonicalTimeProjection.contDiff.smul
      ((c3h196Velocity_apply_contDiff matter).comp
        canonicalSpatialProjection.contDiff))

private theorem hasDerivAt_affineLine_of_differentiableAt
    {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : X → E)
    (point direction : X)
    (differentiable : DifferentiableAt ℝ field point) :
    HasDerivAt
      (fun parameter : ℝ =>
        field (point + parameter • direction))
      (fderiv ℝ field point direction) 0 := by
  have lineDerivative :
      HasDerivAt
        (fun parameter : ℝ =>
          point + parameter • direction)
        direction 0 := by
    simpa using
      ((hasDerivAt_id (0 : ℝ)).smul_const
        direction).const_add point
  have fieldDerivative : HasFDerivAt field (fderiv ℝ field point)
      (point + (0 : ℝ) • direction) := by
    simpa using differentiable.hasFDerivAt
  have composed := fieldDerivative.comp_hasDerivAt 0 lineDerivative
  simpa [Function.comp_def] using composed

theorem c3h196AlgebraicCoordinateDirectionalDerivative_eq_jet
    (derivativeDirection : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    fderiv ℝ
        (fun point => matterCoordinateEquiv
          (c3h196AlgebraicOperator point matter))
        0 (coordinateDirection derivativeDirection) =
      matterCoordinateEquiv
        (c3h196AlgebraicOperatorJet derivativeDirection matter) := by
  have differentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv
        (c3h196AlgebraicOperator point matter)) 0 :=
    ((by
      unfold c3h196AlgebraicOperator
      exact
        holonomicIdentityCoframeMatterAlgebraicOperator_coordinate_contDiff
          c3h196Actual c3h196Actual_smooth matter :
      ContDiff ℝ ∞ (fun point => matterCoordinateEquiv
        (c3h196AlgebraicOperator point matter))).differentiable
      (by simp)).differentiableAt
  have actual := hasDerivAt_affineLine_of_differentiableAt
    (fun point => matterCoordinateEquiv
      (c3h196AlgebraicOperator point matter))
    0 (coordinateDirection derivativeDirection) differentiable
  have expected : HasDerivAt
      (fun time : ℝ =>
        matterCoordinateEquiv (c3h196AlgebraicOperator 0 matter) +
          time • matterCoordinateEquiv
            (c3h196AlgebraicOperatorJet derivativeDirection matter))
      (matterCoordinateEquiv
        (c3h196AlgebraicOperatorJet derivativeDirection matter)) 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const
        (matterCoordinateEquiv
          (c3h196AlgebraicOperatorJet derivativeDirection matter))).const_add
          (matterCoordinateEquiv (c3h196AlgebraicOperator 0 matter))
  have functionEquality :
      (fun time : ℝ => matterCoordinateEquiv
        (c3h196AlgebraicOperator
          (0 + time • coordinateDirection derivativeDirection) matter)) =
      fun time : ℝ =>
        matterCoordinateEquiv (c3h196AlgebraicOperator 0 matter) +
          time • matterCoordinateEquiv
            (c3h196AlgebraicOperatorJet derivativeDirection matter) := by
    funext time
    rw [zero_add]
    calc
      matterCoordinateEquiv
          (c3h196AlgebraicOperator
            (time • coordinateDirection derivativeDirection) matter) =
          matterCoordinateEquiv
            (c3h196AlgebraicOperator 0 matter +
              (time : ℂ) •
                c3h196AlgebraicOperatorJet derivativeDirection matter) :=
        congrArg matterCoordinateEquiv
          (c3h196AlgebraicOperator_axis_apply time derivativeDirection matter)
      _ = matterCoordinateEquiv (c3h196AlgebraicOperator 0 matter) +
          (time : ℂ) • matterCoordinateEquiv
            (c3h196AlgebraicOperatorJet derivativeDirection matter) := by
        rw [map_add, map_smul]
      _ = matterCoordinateEquiv (c3h196AlgebraicOperator 0 matter) +
          time • matterCoordinateEquiv
            (c3h196AlgebraicOperatorJet derivativeDirection matter) := by
        exact congrArg
          (fun value =>
            matterCoordinateEquiv (c3h196AlgebraicOperator 0 matter) + value)
          (RCLike.real_smul_eq_coe_smul (K := ℂ) time
            (matterCoordinateEquiv
              (c3h196AlgebraicOperatorJet derivativeDirection matter))).symm
  rw [functionEquality] at actual
  exact actual.unique expected

theorem c3h196AlgebraicTimeDerivative_eq_jet
    (matter : DiracExteriorMatterCarrier) :
    c3h196AlgebraicTimeDerivative matter =
      c3h196AlgebraicOperatorJet canonicalLorentzianTimeDirection matter := by
  unfold c3h196AlgebraicTimeDerivative
  rw [c3h196AlgebraicCoordinateDirectionalDerivative_eq_jet]
  simp

theorem c3h196AlgebraicSpatialDerivative_eq_jet
    (axis : Fin 3) (matter : DiracExteriorMatterCarrier) :
    c3h196AlgebraicSpatialDerivative axis matter =
      c3h196AlgebraicOperatorJet axis.succ matter := by
  unfold c3h196AlgebraicSpatialDerivative
  rw [c3h196AlgebraicCoordinateDirectionalDerivative_eq_jet]
  simp

@[simp] theorem canonicalTimeProjection_c3h196TimeAxis (time : ℝ) :
    canonicalTimeProjection (c3h196TimeAxis time) = time := by
  simp [c3h196TimeAxis, canonicalTimeProjection, localBaseCoordinate_apply,
    coordinateDirection, canonicalLorentzianTimeDirection]

@[simp] theorem canonicalSpatialProjection_c3h196TimeAxis (time : ℝ) :
    canonicalSpatialProjection (c3h196TimeAxis time) = 0 := by
  apply PiLp.ext
  intro axis
  fin_cases axis <;>
    simp [c3h196TimeAxis, canonicalSpatialProjection,
      localBaseCoordinate_apply, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

@[simp] theorem canonicalTimeProjection_coordinateTime :
    canonicalTimeProjection
        (coordinateDirection canonicalLorentzianTimeDirection) = 1 := by
  simp [canonicalTimeProjection, localBaseCoordinate_apply,
    coordinateDirection, canonicalLorentzianTimeDirection]

@[simp] theorem canonicalSpatialProjection_coordinateTime :
    canonicalSpatialProjection
        (coordinateDirection canonicalLorentzianTimeDirection) = 0 := by
  apply PiLp.ext
  intro axis
  fin_cases axis <;>
    simp [canonicalSpatialProjection, localBaseCoordinate_apply,
      coordinateDirection, canonicalLorentzianTimeDirection]

@[simp] theorem canonicalTimeProjection_coordinateSpatial (axis : Fin 3) :
    canonicalTimeProjection (coordinateDirection axis.succ) = 0 := by
  fin_cases axis <;>
    simp [canonicalTimeProjection, localBaseCoordinate_apply,
      coordinateDirection, canonicalLorentzianTimeDirection]

@[simp] theorem canonicalSpatialProjection_coordinateSpatial (axis : Fin 3) :
    canonicalSpatialProjection (coordinateDirection axis.succ) =
      c3h196SpatialDirection axis := by
  apply PiLp.ext
  intro component
  fin_cases axis <;> fin_cases component <;>
    simp [canonicalSpatialProjection, c3h196SpatialDirection,
      localBaseCoordinate_apply, coordinateDirection]

theorem c3h196_conjugateMatter_apply_timeAxis
    (time : ℝ) (matter : DiracExteriorMatterCarrier) :
    c3h196Actual.conjugateMatter (c3h196TimeAxis time) matter =
      diracSpinZeroMatterCoordinate matter +
        time • c3h196Velocity 0 matter := by
  rw [c3h196_conjugateMatter_apply_normalForm]
  rw [canonicalTimeProjection_c3h196TimeAxis,
    canonicalSpatialProjection_c3h196TimeAxis]

theorem c3h196_conjugateMatterDerivativeDual_apply_bridge
    (point : BasePoint) (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    holonomicConjugateMatterDerivativeDual c3h196Actual point direction matter =
      fieldDirectionalDerivative
        (fun candidate => c3h196Actual.conjugateMatter candidate matter)
        point direction := by
  exact holonomicConjugateMatterDerivativeDual_apply c3h196Actual
    c3h196Actual_smooth point direction matter

set_option maxHeartbeats 10000000 in
theorem c3h196_conjugateMatter_fieldDerivative_timeAxis_time
    (time : ℝ) (matter : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (fun candidate => c3h196Actual.conjugateMatter candidate matter)
        (c3h196TimeAxis time) canonicalLorentzianTimeDirection =
      c3h196Velocity 0 matter := by
  rw [show
    (fun candidate => c3h196Actual.conjugateMatter candidate matter) =
      fun candidate =>
        diracSpinZeroMatterCoordinate matter +
          canonicalTimeProjection candidate •
            c3h196Velocity (canonicalSpatialProjection candidate) matter by
    funext candidate
    exact c3h196_conjugateMatter_apply_normalForm candidate matter]
  unfold fieldDirectionalDerivative
  have velocityDerivative : HasFDerivAt
      (fun space => c3h196Velocity space matter)
      (fderiv ℝ (fun space => c3h196Velocity space matter)
        (canonicalSpatialProjection (c3h196TimeAxis time)))
      (canonicalSpatialProjection (c3h196TimeAxis time)) :=
    ((c3h196Velocity_apply_contDiff matter).differentiable
      (by simp) |>.differentiableAt).hasFDerivAt
  have composedDerivative := velocityDerivative.comp
    (c3h196TimeAxis time) canonicalSpatialProjection.hasFDerivAt
  have productDerivative :=
    canonicalTimeProjection.hasFDerivAt.smul composedDerivative
  have totalDerivative :=
    (hasFDerivAt_const
      (x := c3h196TimeAxis time)
      (c := diracSpinZeroMatterCoordinate matter)).add productDerivative
  have functionEquality :
      (fun candidate =>
        diracSpinZeroMatterCoordinate matter +
          canonicalTimeProjection candidate •
            c3h196Velocity (canonicalSpatialProjection candidate) matter) =
      (fun _ : BasePoint => diracSpinZeroMatterCoordinate matter) +
        (fun candidate : BasePoint => canonicalTimeProjection candidate) •
          ((fun space => c3h196Velocity space matter) ∘
            canonicalSpatialProjection) := by
    funext candidate
    rfl
  rw [functionEquality, totalDerivative.fderiv]
  rw [canonicalTimeProjection_c3h196TimeAxis,
    canonicalSpatialProjection_c3h196TimeAxis]
  simp

theorem c3h196_conjugateMatterDerivative_timeAxis_time
    (time : ℝ) (matter : DiracExteriorMatterCarrier) :
    holonomicConjugateMatterDerivativeDual c3h196Actual
        (c3h196TimeAxis time) canonicalLorentzianTimeDirection matter =
      c3h196Velocity 0 matter := by
  calc
    _ = fieldDirectionalDerivative
        (fun candidate => c3h196Actual.conjugateMatter candidate matter)
        (c3h196TimeAxis time) canonicalLorentzianTimeDirection :=
      c3h196_conjugateMatterDerivativeDual_apply_bridge _ _ _
    _ = c3h196Velocity 0 matter :=
      c3h196_conjugateMatter_fieldDerivative_timeAxis_time time matter

set_option maxHeartbeats 10000000 in
theorem c3h196_conjugateMatter_fieldDerivative_timeAxis_spatial
    (time : ℝ) (axis : Fin 3) (matter : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (fun candidate => c3h196Actual.conjugateMatter candidate matter)
        (c3h196TimeAxis time) axis.succ =
      time • c3h196VelocitySpatialDerivative axis matter := by
  rw [show
    (fun candidate => c3h196Actual.conjugateMatter candidate matter) =
      fun candidate =>
        diracSpinZeroMatterCoordinate matter +
          canonicalTimeProjection candidate •
            c3h196Velocity (canonicalSpatialProjection candidate) matter by
    funext candidate
    exact c3h196_conjugateMatter_apply_normalForm candidate matter]
  unfold fieldDirectionalDerivative c3h196VelocitySpatialDerivative
  have velocityDerivative : HasFDerivAt
      (fun space => c3h196Velocity space matter)
      (fderiv ℝ (fun space => c3h196Velocity space matter)
        (canonicalSpatialProjection (c3h196TimeAxis time)))
      (canonicalSpatialProjection (c3h196TimeAxis time)) :=
    ((c3h196Velocity_apply_contDiff matter).differentiable
      (by simp) |>.differentiableAt).hasFDerivAt
  have composedDerivative := velocityDerivative.comp
    (c3h196TimeAxis time) canonicalSpatialProjection.hasFDerivAt
  have productDerivative :=
    canonicalTimeProjection.hasFDerivAt.smul composedDerivative
  have totalDerivative :=
    (hasFDerivAt_const
      (x := c3h196TimeAxis time)
      (c := diracSpinZeroMatterCoordinate matter)).add productDerivative
  have functionEquality :
      (fun candidate =>
        diracSpinZeroMatterCoordinate matter +
          canonicalTimeProjection candidate •
            c3h196Velocity (canonicalSpatialProjection candidate) matter) =
      (fun _ : BasePoint => diracSpinZeroMatterCoordinate matter) +
        (fun candidate : BasePoint => canonicalTimeProjection candidate) •
          ((fun space => c3h196Velocity space matter) ∘
            canonicalSpatialProjection) := by
    funext candidate
    rfl
  rw [functionEquality, totalDerivative.fderiv]
  rw [canonicalTimeProjection_c3h196TimeAxis,
    canonicalSpatialProjection_c3h196TimeAxis]
  simp

theorem c3h196_conjugateMatterDerivative_timeAxis_spatial
    (time : ℝ) (axis : Fin 3) (matter : DiracExteriorMatterCarrier) :
    holonomicConjugateMatterDerivativeDual c3h196Actual
        (c3h196TimeAxis time) axis.succ matter =
      time • c3h196VelocitySpatialDerivative axis matter := by
  calc
    _ = fieldDirectionalDerivative
        (fun candidate => c3h196Actual.conjugateMatter candidate matter)
        (c3h196TimeAxis time) axis.succ :=
      c3h196_conjugateMatterDerivativeDual_apply_bridge _ _ _
    _ = time • c3h196VelocitySpatialDerivative axis matter :=
      c3h196_conjugateMatter_fieldDerivative_timeAxis_spatial
        time axis matter

theorem c3h196_actionResidual_timeAxis (time : ℝ) :
    holonomicIdentityCoframeConjugateMatterActionResidual c3h196Actual
        (c3h196TimeAxis time) c3h196Probe =
      diracSpinZeroMatterCoordinate
          (c3h196AlgebraicOperator (c3h196TimeAxis time) c3h196Probe) +
        time • c3h196Velocity 0
          (c3h196AlgebraicOperator (c3h196TimeAxis time) c3h196Probe) -
        (∑ axis : Fin 3,
          time • c3h196VelocitySpatialDerivative axis
            (c3h196Principal axis.succ c3h196Probe)) -
        c3h196Velocity 0
          (c3h196Principal canonicalLorentzianTimeDirection c3h196Probe) := by
  simp_rw [c3h196AlgebraicOperator_apply, c3h196Principal_apply]
  unfold holonomicIdentityCoframeConjugateMatterActionResidual
    holonomicIdentityCoframeConjugateMatterKnownDual
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply]
  rw [c3h196_conjugateMatter_apply_timeAxis]
  rw [c3h196_conjugateMatterDerivative_timeAxis_time]
  simp_rw [c3h196_conjugateMatterDerivative_timeAxis_spatial]

theorem c3h196_actionResidual_origin :
    holonomicIdentityCoframeConjugateMatterActionResidual c3h196Actual 0
      c3h196Probe = 0 := by
  rw [show (0 : BasePoint) = c3h196TimeAxis 0 by
    simp [c3h196TimeAxis]]
  rw [c3h196_actionResidual_timeAxis]
  simp only [zero_smul, add_zero, Finset.sum_const_zero, sub_zero]
  rw [c3h196Velocity_apply_eq_cauchyAlgebraic]
  rw [identityCoframeMatterPrincipal_time_involutive]
  rw [← c3h196AlgebraicOperator_origin_eq_cauchy]
  simp [c3h196TimeAxis]

theorem c3h196TemporalAdjointELCoefficient_origin :
    c3h196TemporalAdjointELCoefficient 0 = 0 := by
  unfold c3h196TemporalAdjointELCoefficient
    c3h196TemporalAdjointELProbe
  rw [positiveAdjointDiagonalActual_matterEulerLagrange_eq_actionResidual_re]
  rw [matterCoordinateEquiv.symm_apply_apply]
  have originResidual := c3h196_actionResidual_origin
  unfold c3h196Actual c3h196Probe at originResidual
  rw [originResidual]
  rfl

theorem c3h196_fixedDual_algebraic_timeAxis_hasDerivAt
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : DiracExteriorMatterCarrier) :
    HasDerivAt
      (fun time => dual
        (c3h196AlgebraicOperator (c3h196TimeAxis time) matter))
      (dual (c3h196AlgebraicOperatorJet
        canonicalLorentzianTimeDirection matter))
      0 := by
  rw [show
      (fun time => dual
        (c3h196AlgebraicOperator (c3h196TimeAxis time) matter)) =
        fun time : ℝ =>
          dual (c3h196AlgebraicOperator 0 matter) +
            time • dual (c3h196AlgebraicOperatorJet
              canonicalLorentzianTimeDirection matter) by
    funext time
    calc
      dual (c3h196AlgebraicOperator (c3h196TimeAxis time) matter) =
          dual (c3h196AlgebraicOperator 0 matter +
            (time : ℂ) • c3h196AlgebraicOperatorJet
              canonicalLorentzianTimeDirection matter) :=
        congrArg dual
          (c3h196AlgebraicOperator_axis_apply time
            canonicalLorentzianTimeDirection matter)
      _ = dual (c3h196AlgebraicOperator 0 matter) +
          (time : ℂ) • dual (c3h196AlgebraicOperatorJet
            canonicalLorentzianTimeDirection matter) := by
        rw [map_add, map_smul]
      _ = dual (c3h196AlgebraicOperator 0 matter) +
          time • dual (c3h196AlgebraicOperatorJet
            canonicalLorentzianTimeDirection matter) := by
        exact congrArg
          (fun value => dual (c3h196AlgebraicOperator 0 matter) + value)
          (RCLike.real_smul_eq_coe_smul (K := ℂ) time
            (dual (c3h196AlgebraicOperatorJet
              canonicalLorentzianTimeDirection matter))).symm]
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const
      (dual (c3h196AlgebraicOperatorJet
        canonicalLorentzianTimeDirection matter))).const_add
          (dual (c3h196AlgebraicOperator 0 matter))

set_option maxHeartbeats 10000000 in
theorem c3h196_actionResidual_timeAxis_hasDerivAt :
    HasDerivAt
      (fun time =>
        holonomicIdentityCoframeConjugateMatterActionResidual c3h196Actual
          (c3h196TimeAxis time) c3h196Probe)
      (diracSpinZeroMatterCoordinate
          (c3h196AlgebraicOperatorJet
            canonicalLorentzianTimeDirection c3h196Probe) +
        c3h196Velocity 0
          (c3h196AlgebraicOperator 0 c3h196Probe) -
        ∑ axis : Fin 3,
          c3h196VelocitySpatialDerivative axis
            (c3h196Principal axis.succ c3h196Probe))
      0 := by
  have algebraicDerivative :=
    c3h196_fixedDual_algebraic_timeAxis_hasDerivAt
      diracSpinZeroMatterCoordinate c3h196Probe
  have velocityAlgebraicDerivative :=
    c3h196_fixedDual_algebraic_timeAxis_hasDerivAt
      (c3h196Velocity 0) c3h196Probe
  have productDerivative : HasDerivAt
      (fun time : ℝ => time • c3h196Velocity 0
        (c3h196AlgebraicOperator (c3h196TimeAxis time) c3h196Probe))
      (c3h196Velocity 0 (c3h196AlgebraicOperator 0 c3h196Probe)) 0 := by
    have productRule :=
      (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul
        velocityAlgebraicDerivative
    have productFunction :
        (fun time : ℝ => time • c3h196Velocity 0
          (c3h196AlgebraicOperator (c3h196TimeAxis time) c3h196Probe)) =
        (id : ℝ → ℝ) • (fun time : ℝ => c3h196Velocity 0
          (c3h196AlgebraicOperator (c3h196TimeAxis time) c3h196Probe)) := by
      funext time
      exact (RCLike.real_smul_eq_coe_mul time _).symm
    rw [productFunction]
    simpa [c3h196TimeAxis] using productRule
  have spatialDerivative : HasDerivAt
      (fun time : ℝ => ∑ axis : Fin 3,
        time • c3h196VelocitySpatialDerivative axis
          (c3h196Principal axis.succ c3h196Probe))
      (∑ axis : Fin 3,
        c3h196VelocitySpatialDerivative axis
          (c3h196Principal axis.succ c3h196Probe)) 0 := by
    exact HasDerivAt.sum (𝕜 := ℝ) (u := Finset.univ) fun axis _ => by
      simpa only [id_eq, one_smul] using
        (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const
          (c3h196VelocitySpatialDerivative axis
            (c3h196Principal axis.succ c3h196Probe))
  rw [show
    (fun time =>
      holonomicIdentityCoframeConjugateMatterActionResidual c3h196Actual
        (c3h196TimeAxis time) c3h196Probe) =
      fun time =>
        diracSpinZeroMatterCoordinate
            (c3h196AlgebraicOperator (c3h196TimeAxis time) c3h196Probe) +
          time • c3h196Velocity 0
            (c3h196AlgebraicOperator (c3h196TimeAxis time) c3h196Probe) -
          (∑ axis : Fin 3,
            time • c3h196VelocitySpatialDerivative axis
              (c3h196Principal axis.succ c3h196Probe)) -
          c3h196Velocity 0
            (c3h196Principal canonicalLorentzianTimeDirection c3h196Probe) by
    funext time
    exact c3h196_actionResidual_timeAxis time]
  have varyingDerivative :=
    (algebraicDerivative.add productDerivative).sub spatialDerivative
  have assembledDerivative := varyingDerivative.sub_const
    (c3h196Velocity 0
      (c3h196Principal canonicalLorentzianTimeDirection c3h196Probe))
  simpa only [Pi.add_apply, Pi.sub_apply] using assembledDerivative

def c3h196ActionResidualTemporalFirstGerm : ℂ :=
  deriv (fun time =>
    holonomicIdentityCoframeConjugateMatterActionResidual c3h196Actual
      (c3h196TimeAxis time) c3h196Probe) 0

theorem c3h196ActionResidualTemporalFirstGerm_eq_velocityNormalForm :
    c3h196ActionResidualTemporalFirstGerm =
      diracSpinZeroMatterCoordinate
          (c3h196AlgebraicOperatorJet
            canonicalLorentzianTimeDirection c3h196Probe) +
        c3h196Velocity 0
          (c3h196AlgebraicOperator 0 c3h196Probe) -
        ∑ axis : Fin 3,
          c3h196VelocitySpatialDerivative axis
            (c3h196Principal axis.succ c3h196Probe) := by
  unfold c3h196ActionResidualTemporalFirstGerm
  exact c3h196_actionResidual_timeAxis_hasDerivAt.deriv

theorem c3h196ActionResidualTemporalFirstGerm_eq_Kt_K0P0K0_KiP0Pi :
    c3h196ActionResidualTemporalFirstGerm =
      diracSpinZeroMatterCoordinate
          (c3h196AlgebraicTimeDerivative c3h196Probe) +
        diracSpinZeroMatterCoordinate
          (c3h196AlgebraicOperator 0
            (c3h196Principal canonicalLorentzianTimeDirection
              (c3h196AlgebraicOperator 0 c3h196Probe))) -
        ∑ axis : Fin 3,
          diracSpinZeroMatterCoordinate
            (c3h196CauchyAlgebraicSpatialDerivative axis
              (c3h196Principal canonicalLorentzianTimeDirection
                (c3h196Principal axis.succ c3h196Probe))) := by
  rw [c3h196ActionResidualTemporalFirstGerm_eq_velocityNormalForm]
  rw [← c3h196AlgebraicTimeDerivative_eq_jet]
  rw [c3h196Velocity_origin_algebraicOperator]
  apply congrArg (fun value =>
    diracSpinZeroMatterCoordinate
          (c3h196AlgebraicTimeDerivative c3h196Probe) +
        diracSpinZeroMatterCoordinate
          (c3h196AlgebraicOperator 0
            (c3h196Principal canonicalLorentzianTimeDirection
              (c3h196AlgebraicOperator 0 c3h196Probe))) - value)
  apply Finset.sum_congr rfl
  intro axis _
  exact
    c3h196VelocitySpatialDerivative_eq_algebraicSpatialDerivative axis _

theorem c3h196ActionResidualTemporalFirstGerm_eq_holonomic_Kt_K0P0K0_KiP0Pi :
    c3h196ActionResidualTemporalFirstGerm =
      diracSpinZeroMatterCoordinate
          (c3h196AlgebraicTimeDerivative c3h196Probe) +
        diracSpinZeroMatterCoordinate
          (c3h196AlgebraicOperator 0
            (c3h196Principal canonicalLorentzianTimeDirection
              (c3h196AlgebraicOperator 0 c3h196Probe))) -
        ∑ axis : Fin 3,
          diracSpinZeroMatterCoordinate
            (c3h196AlgebraicSpatialDerivative axis
              (c3h196Principal canonicalLorentzianTimeDirection
                (c3h196Principal axis.succ c3h196Probe))) := by
  rw [c3h196ActionResidualTemporalFirstGerm_eq_Kt_K0P0K0_KiP0Pi]
  apply congrArg (fun value =>
    diracSpinZeroMatterCoordinate
          (c3h196AlgebraicTimeDerivative c3h196Probe) +
        diracSpinZeroMatterCoordinate
          (c3h196AlgebraicOperator 0
            (c3h196Principal canonicalLorentzianTimeDirection
              (c3h196AlgebraicOperator 0 c3h196Probe))) - value)
  apply Finset.sum_congr rfl
  intro axis _
  rw [c3h196CauchyAlgebraicSpatialDerivative_eq_holonomic]

def c3h196TemporalAdjointELFirstGerm : ℝ :=
  deriv (fun time =>
    c3h196TemporalAdjointELCoefficient (c3h196TimeAxis time)) 0

theorem c3h196TemporalAdjointELFirstGerm_eq_actionResidual_re :
    c3h196TemporalAdjointELFirstGerm =
      c3h196ActionResidualTemporalFirstGerm.re := by
  have residualDerivative :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
      c3h196_actionResidual_timeAxis_hasDerivAt
  have coefficientEquality :
      (fun time =>
        c3h196TemporalAdjointELCoefficient (c3h196TimeAxis time)) =
      fun time =>
        (holonomicIdentityCoframeConjugateMatterActionResidual c3h196Actual
          (c3h196TimeAxis time) c3h196Probe).re := by
    funext time
    unfold c3h196TemporalAdjointELCoefficient
      c3h196TemporalAdjointELProbe c3h196Actual c3h196Probe
    simpa using
      positiveAdjointDiagonalActual_matterEulerLagrange_eq_actionResidual_re
        (matterCoordinateEquiv
          (Complex.I • diracSpinTwoMatterProbe))
        (c3h196TimeAxis time)
  unfold c3h196TemporalAdjointELFirstGerm
    c3h196ActionResidualTemporalFirstGerm
  rw [coefficientEquality]
  rw [c3h196_actionResidual_timeAxis_hasDerivAt.deriv]
  simpa [Function.comp_def] using residualDerivative.deriv

theorem c3h196TemporalAdjointELFirstGerm_eq_holonomic_Kt_K0P0K0_KiP0Pi :
    c3h196TemporalAdjointELFirstGerm =
      (diracSpinZeroMatterCoordinate
            (c3h196AlgebraicTimeDerivative c3h196Probe) +
          diracSpinZeroMatterCoordinate
            (c3h196AlgebraicOperator 0
              (c3h196Principal canonicalLorentzianTimeDirection
                (c3h196AlgebraicOperator 0 c3h196Probe))) -
          ∑ axis : Fin 3,
            diracSpinZeroMatterCoordinate
              (c3h196AlgebraicSpatialDerivative axis
                (c3h196Principal canonicalLorentzianTimeDirection
                  (c3h196Principal axis.succ c3h196Probe)))).re := by
  rw [c3h196TemporalAdjointELFirstGerm_eq_actionResidual_re]
  rw [c3h196ActionResidualTemporalFirstGerm_eq_holonomic_Kt_K0P0K0_KiP0Pi]

end

end
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermStructural
