import H0mework.Physics.Geometry.BiradialScalarOriginResponse
import H0mework.Physics.MatterCurrent.CanonicalLorentzTemporalGauss

/-!
# C3h192: same-actual canonical-contact scalar constraint

The C3h189 Lorentz first-jet installer changes only the gravity auxiliary.
This module nevertheless does not transport the old `U****` scalar theorem:
C3h187 opened a fresh contact-recomputation epoch, so the scalar germ is
reconstructed directly from the generated zero-response Cauchy state.

At the canonical spatial contact the forward chain is

```text
C3h187 generated zero-response state
-> constant vacuum scalar and zero scalar velocity
-> C3h188 action-generated affine scalar germ
-> zero P286 connection origin and diagonal jet
-> scalar differential divergence and algebraic terms vanish
-> scalar Euler--Lagrange constraint on the same C3h189 actual.
```

The final theorem is an independent, failure-capable constraint.  It is not
the re-substitution of a scalar response constructor, and no old whole-actual
replay, residual target, branch, event, or global source-time evolution is
used.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzScalarConstraint

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineBiradialCoframeResponse
open StageNineBiradialScalarOriginResponse
open StageNineCanonicalCauchyState
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalGravityPreservingLorentzDualResponse
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzActualFirstJetLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzOriginProvenance
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzTangentSimplicity
open StageNineSourceActionGeneratedP506MatterCurrentCompleteFirstGermCanonicalPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullSynchronizedActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterCompleteFirstGermResponse
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterTemporalFirstGermResponse
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open SU7MotherLieAlgebra
open SU7ExteriorBreakingYukawa

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance c3h192P286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance c3h192P286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance c3h192P286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private theorem c3h192_canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 0 = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-! ## Fresh C3h187 current scalar and connection data -/

theorem
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_scalar_vacuum :
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  funext space
  change
    positiveP506MatterCurrentCompleteFirstGermResponseActual.scalar
        (canonicalCauchySlicePoint 0 space) =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_scalar,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_scalar,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalar_vacuum]

theorem
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_scalarVelocity_zero :
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.scalarVelocity =
      0 := by
  funext space
  change
    fieldDirectionalDerivative
        positiveP506MatterCurrentCompleteFirstGermResponseActual.scalar
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      0
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_scalar,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_scalar,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalar_vacuum]
  simp [fieldDirectionalDerivative]

theorem
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_gaugeConnection_origin_zero
    (direction : LorentzianIndex) :
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.gaugeConnection
        0 direction =
      0 := by
  change
    positiveP506MatterCurrentCompleteFirstGermResponseActual.gaugeConnection
        (canonicalCauchySlicePoint 0 0) direction =
      0
  rw [c3h192_canonicalCauchySlicePoint_zero_zero,
    positiveP506MatterCurrentCompleteFirstGermResponseActual_gaugeConnection,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_gaugeConnection]
  apply p286CoordinateEquiv.injective
  simpa [holonomicP286GaugeConnectionCoordinate] using
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionCoordinate_origin_zero
      direction

/-! The contact update is definitionally faithful on the scalar Cauchy data. -/

@[simp] theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_scalar_vacuum :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  funext space
  change
    (currentCanonicalFullActionActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      space).scalar (canonicalCauchySlicePoint 0 0) =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  rw [c3h192_canonicalCauchySlicePoint_zero_zero]
  change
    (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      space).scalar 0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  change
    actionGeneratedScalarLocalField
        positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
        space 0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  rw [actionGeneratedScalarLocalField_origin,
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_scalar_vacuum]

@[simp] theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_scalarVelocity_zero :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.scalarVelocity =
      0 := by
  funext space
  change
    fieldDirectionalDerivative
        (currentCanonicalFullActionActual positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
          space).scalar
        (canonicalCauchySlicePoint 0 0)
        canonicalLorentzianTimeDirection =
      0
  rw [c3h192_canonicalCauchySlicePoint_zero_zero]
  change
    fieldDirectionalDerivative
        (actionGeneratedScalarLocalField
          positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
          space)
        0 canonicalLorentzianTimeDirection =
      0
  rw [actionGeneratedScalarLocalField_derivative]
  simp [actionGeneratedScalarLocalJetCoordinate,
    canonicalLorentzianTimeDirection,
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_scalarVelocity_zero]

theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeConnection_origin_zero
    (direction : LorentzianIndex) :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.gaugeConnection
        0 direction =
      0 := by
  change
    (currentCanonicalFullActionActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      0).gaugeConnection (canonicalCauchySlicePoint 0 0) direction =
      0
  rw [c3h192_canonicalCauchySlicePoint_zero_zero]
  change
    (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      0).gaugeConnection 0 direction =
      0
  change
    sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState 0
        0 direction =
      0
  rw [sourceGeneratedP286ActionLocalConnection_origin,
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState_gaugeConnection_origin_zero]

/-! ## Fresh C3h188/C3h189 scalar germ at the canonical contact -/

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalar_vacuum :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0).scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    actionGeneratedScalarLocalField
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        0 =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  funext point
  simp [actionGeneratedScalarLocalField,
    actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate,
    cauchyScalarSpatialDerivativeCoordinate,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_scalar_vacuum,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_scalarVelocity_zero,
    Fin.sum_univ_four]

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_connectionCoordinate_origin_zero
    (direction : LorentzianIndex) :
    holonomicP286GaugeConnectionCoordinate
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        0 direction =
      0 := by
  change
    p286CoordinateEquiv
        (sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
          positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
          0 0 direction) =
      0
  rw [sourceGeneratedP286ActionLocalConnection_origin,
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeConnection_origin_zero]
  simp

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gaugeConnection_eq_sourceGenerated :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
      0).gaugeConnection =
      (sourceGeneratedP286ActionLocalActualLift positiveSmoothUnifiedSource
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        0).gaugeConnection :=
  rfl

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_connectionDerivative_diagonal_zero
    (direction : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        0 direction direction =
      0 := by
  calc
    p286GaugeConnectionCoordinateDerivative
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          0 direction direction =
        p286GaugeConnectionCoordinateDerivative
          (sourceGeneratedP286ActionLocalActualLift positiveSmoothUnifiedSource
            positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
            0)
          0 direction direction := by
      unfold p286GaugeConnectionCoordinateDerivative
        holonomicP286GaugeConnectionCoordinate
      rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gaugeConnection_eq_sourceGenerated]
    _ = sourceGeneratedP286ActionLocalConnectionJet positiveSmoothUnifiedSource
          positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
          0 direction direction :=
      sourceGeneratedP286ActionLocalActualLift_connectionDerivative
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        0 direction direction
    _ = 0 := by
      fin_cases direction <;>
        simp [sourceGeneratedP286ActionLocalConnectionJet]

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_conjugateMatter_origin_zero :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
      0).conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  exact
    positiveP506MatterCurrentCanonicalGravityPreservingFinalActual_conjugateMatter_probe
      0

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarCovariantDerivative_eq_fixedVacuumAction
    (point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        point direction =
      scalarP286ActionBilinear
        (holonomicP286GaugeConnectionCoordinate
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          point direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  unfold holonomicScalarCovariantDerivative
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalar_vacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add]
  unfold holonomicP286GaugeConnectionCoordinate
  change
    scalarMotherLieAction
        (p286LieBlockEmbed
          ((positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
            0).gaugeConnection point direction))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (p286CoordinateEquiv
              ((positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
                0).gaugeConnection point direction))))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
  rw [p286CoordinateEquiv.symm_apply_apply]

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarCovariantDerivative_origin_zero
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        0 direction =
      0 := by
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarCovariantDerivative_eq_fixedVacuumAction,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_connectionCoordinate_origin_zero]
  simp

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarCovariantDerivative_diagonalDerivative_zero
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicScalarCovariantDerivative
            (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
            point direction)
        0 direction =
      0 := by
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  let connection := fun point =>
    holonomicP286GaugeConnectionCoordinate
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
      point direction
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 := by
    have smooth :=
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_smooth 0).2.2.2.2.1
        direction
    simpa [connection, holonomicP286GaugeConnectionCoordinate] using
      (smooth.differentiable (by simp)).differentiableAt
  have actionDerivative :
      fderiv ℝ
          (fun point =>
            action (connection point)
              (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
          0 =
        (action.flip
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).comp
            (fderiv ℝ connection 0) :=
    ((action.flip
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).hasFDerivAt.comp
      0 connectionDifferentiable.hasFDerivAt).fderiv
  rw [show
    (fun point =>
      holonomicScalarCovariantDerivative
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        point direction) =
      fun point =>
        action (connection point)
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) by
    funext point
    exact
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarCovariantDerivative_eq_fixedVacuumAction
        point direction]
  unfold fieldDirectionalDerivative
  rw [actionDerivative]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  change
    scalarP286ActionBilinear
        (p286GaugeConnectionCoordinateDerivative
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          0 direction direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      0
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_connectionDerivative_diagonal_zero]
  simp

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarDivergence_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction 0 =
      0 := by
  apply scalarDifferentialMomentumDivergence_origin_eq_zero_of_biradial
      positiveSmoothUnifiedSource
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
      (a := 1) (b := 1)
  · norm_num
  · norm_num
  · funext point
    rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one,
      biradialCoframe_one_one]
  · intro formDirection
    exact
      ((holonomicScalarCovariantDerivative_contDiff
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_smooth 0)
        formDirection).differentiable (by simp)).differentiableAt
  · exact
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarCovariantDerivative_diagonalDerivative_zero

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarKineticAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          0)
        (holonomicScalarVariationAlgebraicDirection
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction 0) =
      0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  have covariantDerivativeOrigin :
      (toContinuumPointField
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        0).scalarCovariantDerivative =
        0 := by
    funext formDirection
    exact
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarCovariantDerivative_origin_zero
        formDirection
  rw [covariantDerivativeOrigin]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarPotential_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          0)
        direction =
      0 := by
  unfold scalarPotentialFirstVariation
  rw [show
    (toContinuumPointField
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
      0).scalar =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource by
    exact congrFun
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalar_vacuum
      0]
  simp

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarYukawa_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarYukawaFirstVariationDensity
        (toContinuumPointField
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          0)
        direction =
      0 := by
  unfold scalarYukawaFirstVariationDensity scalarYukawaVariationVector
  rw [show
    (toContinuumPointField
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
      0).conjugateMatter =
        diracSpinZeroMatterCoordinate by
    exact
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_conjugateMatter_origin_zero,
    diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]
  norm_num

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction 0 =
      0 := by
  unfold scalarAlgebraicDirectionalCoefficient
  rw [
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarKineticAlgebraic_origin_zero,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarPotential_origin_zero,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarYukawa_origin_zero]
  ring

/-- Frontier theorem: the scalar Euler--Lagrange equation holds on the same
C3h189 actual as the Lorentz simplicity and temporal Gauss constraints.  The
scalar response was not solved by this actualizer, so this is an independent
constraint rather than producer re-substitution. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarEuler_origin
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction 0 =
      0 := by
  unfold scalarEulerLagrangeDirectionalCoefficient
  rw [
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarAlgebraic_origin_zero,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarDivergence_origin_zero]
  ring

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzScalarConstraint
