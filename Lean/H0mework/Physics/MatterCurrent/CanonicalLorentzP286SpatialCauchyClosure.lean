import H0mework.Physics.ConnectionJets.CurrentP286CompleteActionResponseFirstJet
import H0mework.Physics.MatterCurrent.CanonicalLorentzScalarSimultaneousLocalClosure
import H0mework.Physics.MatterCurrent.P286PrincipalFirstGermP286ConnectionSpatialCauchyClosure

/-!
# C3h194: fresh same-actual P286 spatial-Cauchy closure

This module directly evaluates the P286 connection Euler--Lagrange spatial
first germ on the fresh C3h189 actual.  It does not identify that actual with
the historical `U****`.  Instead it follows the current/action producer:

```text
C3h187 generated zero-response Cauchy state
-> its actual P286 Cauchy data at global contact 0
-> fresh source-generated affine connection germ
-> direct complete-P286 auxiliary response
-> temporal and complete matter response
-> C3h189 Lorentz auxiliary-only installer
-> P286 EL spatial first germ as downstream acceptance.
```

Historical C3h183b is used only to read the spatial derivative of the
source-owned Cauchy data from the actual that generated that Cauchy slice.
No whole-actual replay, equation receipt, branch, event, scheduler, or global
source-time evolution is used.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzP286SpatialCauchyClosure

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineCanonicalLocalFullActionResponseOperator
open StageNineConnectionSectorSourceBalance
open StageNineCoframeTwoFormPairing
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineFullSynchronizedCompleteP286ActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterActionTimeVelocity
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNinePositiveSourceNativeGravityCurvatureBridge
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineScalarActionSecondJetLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalGravityPreservingLorentzDualResponse
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzActualFirstJetLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzOriginProvenance
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzScalarConstraint
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzScalarSimultaneousLocalClosure
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzTangentSimplicity
open StageNineSourceActionGeneratedP506MatterCurrentCompleteFirstGermCanonicalPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullSynchronizedActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionLine
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterCompleteFirstGermResponse
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterCompleteFirstGermP286ConnectionSpatialCauchyClosure
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterTemporalFirstGermResponse
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance c3h194P286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance c3h194P286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance c3h194P286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance c3h194MatterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private theorem c3h194_canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 0 = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-! ## Generated C3h187 P286 Cauchy-data fidelity -/

@[simp] theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeConnection
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.gaugeConnection
        space direction =
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.gaugeConnection
        space direction := by
  change
    (currentCanonicalFullActionActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      space).gaugeConnection (canonicalCauchySlicePoint 0 0) direction =
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.gaugeConnection
        space direction
  rw [c3h194_canonicalCauchySlicePoint_zero_zero]
  change
    sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
        space 0 direction =
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.gaugeConnection
        space direction
  exact sourceGeneratedP286ActionLocalConnection_origin
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
    space direction

@[simp] theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeAuxiliary
    (space : StageNineSpatialPoint)
    (pair : Fin 6) :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.gaugeAuxiliary
        space pair =
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.gaugeAuxiliary
        space pair := by
  change
    (currentCanonicalFullActionActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
      space).gaugeAuxiliary (canonicalCauchySlicePoint 0 0) pair =
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.gaugeAuxiliary
        space pair
  rw [c3h194_canonicalCauchySlicePoint_zero_zero]
  change
    (fullSynchronizedCompleteP286ActionResponseOperator
      positiveSmoothUnifiedSource
      (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
        space)).gaugeAuxiliary 0 pair =
      positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.gaugeAuxiliary
        space pair
  unfold fullSynchronizedCompleteP286ActionResponseOperator
  rw [currentP286CompleteActionResponseOperator_gaugeAuxiliary_origin,
    fullSynchronizedActionResponseOperator_gaugeAuxiliary]
  rfl

theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_connectionSpatialCauchyDerivative_zero
    (axis : Fin 3)
    (formDirection : LorentzianIndex) :
    cauchyP286SpatialConnectionDerivativeCoordinate
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        0 axis formDirection =
      0 := by
  unfold cauchyP286SpatialConnectionDerivativeCoordinate
  rw [show
    (fun candidate =>
      p286CoordinateEquiv
        (positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.gaugeConnection
          candidate formDirection)) =
      (fun candidate =>
        p286CoordinateEquiv
          (positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState.gaugeConnection
            candidate formDirection)) by
    funext candidate
    rw [positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeConnection]]
  change
    cauchyP286SpatialConnectionDerivativeCoordinate
        positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
        0 axis formDirection =
      0
  unfold positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState
  rw [cauchyP286SpatialConnectionDerivativeCoordinate_restriction
    0 positiveP506MatterCurrentCompleteFirstGermResponseActual
    positiveP506MatterCurrentCompleteFirstGermResponseActual_smooth]
  rw [c3h194_canonicalCauchySlicePoint_zero_zero]
  exact
    positiveP506MatterCurrentCompleteFirstGermResponseActual_connectionSpatialOneJet_zero
      axis formDirection

private theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_actionCurvature_eq_old_origin
    (pair : Fin 6) :
    p286CoordinateEquiv
        (actionGeneratedP286Curvature positiveSmoothUnifiedSource
          positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
          0 pair) =
      holonomicP286GaugeCurvatureCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        0 pair := by
  unfold actionGeneratedP286Curvature
  rw [p286CoordinateEquiv_liftGaugeTwoFormOperator]
  rw [show
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.coframe
        0 =
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe
        0 by
    rw [positiveP506MatterCurrentCompleteFirstGermCanonicalGeneratedZeroResponseState_coframe_one,
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_coframe_one]]
  rw [show
    (fun input =>
      p286CoordinateEquiv
        (positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.gaugeAuxiliary
          0 input)) =
      holonomicP286GaugeAuxiliaryCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        0 by
    funext input
    unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeAuxiliary]
    change
      p286CoordinateEquiv
          (positiveP506MatterCurrentCompleteFirstGermResponseActual.gaugeAuxiliary
            (canonicalCauchySlicePoint 0 0) input) =
        _
    rw [c3h194_canonicalCauchySlicePoint_zero_zero,
      positiveP506MatterCurrentCompleteFirstGermResponseActual_gaugeAuxiliary,
      positiveP506MatterCurrentTemporalFirstGermResponseActual_gaugeAuxiliary]]
  exact (congrFun
    (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286AuxiliaryEquation_coordinate
      0) pair).symm

private theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_actionCurvature_pureSpatial_zero
    (pair : Fin 6)
    (pureSpatial : 3 ≤ pair) :
    p286CoordinateEquiv
        (actionGeneratedP286Curvature positiveSmoothUnifiedSource
          positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
          0 pair) =
      0 := by
  rw [positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_actionCurvature_eq_old_origin]
  rw [congrFun
    (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvatureCoordinate_normalForm
      0) pair]
  fin_cases pair <;>
    simp_all [c3h181FullCurvatureCoordinateNormalForm]

private theorem
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_exteriorDerivative_pureSpatial_zero
    (pair : Fin 6)
    (pureSpatial : 3 ≤ pair) :
    actionGeneratedP286ExteriorDerivativeCoordinate positiveSmoothUnifiedSource
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        0 pair =
      0 := by
  unfold actionGeneratedP286ExteriorDerivativeCoordinate
  rw [positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_actionCurvature_pureSpatial_zero
    pair pureSpatial]
  have firstZero :=
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeConnection_origin_zero
      (pairFirst pair)
  have secondZero :=
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeConnection_origin_zero
      (pairSecond pair)
  rw [firstZero, secondZero]
  simp

/-! ## Fresh local P286 connection on the canonical spatial slice -/

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_p286ConnectionSpatialOneJet_zero
    (axis : Fin 3)
    (formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        0 axis.succ formDirection =
      0 := by
  rw [show
    p286GaugeConnectionCoordinateDerivative
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        0 axis.succ formDirection =
      p286GaugeConnectionCoordinateDerivative
        (sourceGeneratedP286ActionLocalActualLift positiveSmoothUnifiedSource
          positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
          0)
        0 axis.succ formDirection by
    unfold p286GaugeConnectionCoordinateDerivative
      holonomicP286GaugeConnectionCoordinate
    rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gaugeConnection_eq_sourceGenerated]]
  rw [sourceGeneratedP286ActionLocalActualLift_connectionDerivative]
  fin_cases axis <;> fin_cases formDirection <;>
    simp [sourceGeneratedP286ActionLocalConnectionJet,
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_connectionSpatialCauchyDerivative_zero,
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_exteriorDerivative_pureSpatial_zero]

private theorem c3h194_connectionCoordinate_contDiff :
    ContDiff ℝ ∞
      (holonomicP286GaugeConnectionCoordinate
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)) := by
  rcases positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_smooth 0 with
    ⟨_, _, _, _, gaugeConnectionSmooth, _, _, _, _⟩
  apply contDiff_pi.mpr
  intro formDirection
  simpa [holonomicP286GaugeConnectionCoordinate] using
    gaugeConnectionSmooth formDirection

private theorem c3h194_connectionCoordinate_spatialDerivative_zero
    (axis : Fin 3) :
    fieldDirectionalDerivative
        (holonomicP286GaugeConnectionCoordinate
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0))
        0 axis.succ =
      0 := by
  funext formDirection
  have component :=
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_p286ConnectionSpatialOneJet_zero
      axis formDirection
  unfold p286GaugeConnectionCoordinateDerivative at component
  unfold fieldDirectionalDerivative at component ⊢
  rw [fderiv_apply
    (c3h194_connectionCoordinate_contDiff.differentiable (by simp) 0)
    formDirection] at component
  simpa using component

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gaugeConnection_canonicalZeroSlice_zero
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
      0).gaugeConnection (canonicalCauchySlicePoint 0 space) formDirection =
      0 := by
  rw [congrFun (congrFun
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gaugeConnection_eq_sourceGenerated
    (canonicalCauchySlicePoint 0 space)) formDirection]
  apply p286CoordinateEquiv.injective
  unfold sourceGeneratedP286ActionLocalActualLift
    sourceGeneratedP286ActionLocalConnection
  simp only [p286CoordinateEquiv.apply_symm_apply]
  unfold sourceGeneratedP286ActionLocalConnectionCoordinate
    sourceGeneratedP286ActionLocalIncrement
  rw [positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_gaugeConnection_origin_zero]
  fin_cases formDirection <;>
    simp [sourceGeneratedP286ActionLocalConnectionJet,
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_connectionSpatialCauchyDerivative_zero,
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_exteriorDerivative_pureSpatial_zero,
      canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      localBaseCoordinate_apply, Fin.sum_univ_four]

/-! ## Fresh matter data on the same canonical slice -/

private theorem c3h194_currentState_matter_constant :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  exact
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_matter_probe
      space

private theorem c3h194_currentState_conjugateMatter_constant :
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState.conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  funext space
  exact
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState_conjugateMatter_probe
      space

private theorem c3h194_baseActual_matter_canonicalZeroSlice
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
      0).matter (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        0 (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact actionGeneratedMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
    0 diracSpinTwoMatterProbe c3h194_currentState_matter_constant space

private theorem c3h194_baseActual_conjugateMatter_canonicalZeroSlice
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
      0).conjugateMatter (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        0 (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  exact actionGeneratedConjugateMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
    0 diracSpinZeroMatterCoordinate
    c3h194_currentState_conjugateMatter_constant space

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_matter_canonicalZeroSlice
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
      0).matter (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  change
    (actionGeneratedMatterCompleteFirstGermActual positiveSmoothUnifiedSource
      (actionGeneratedMatterTemporalFirstGermActual positiveSmoothUnifiedSource
        (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
          (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
            positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
            0)))).matter (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  rw [actionGeneratedMatterCompleteFirstGermActual_matter_of_time_zero
    positiveSmoothUnifiedSource _ _ (by
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection])]
  apply matterCoordinateEquiv.injective
  unfold actionGeneratedMatterTemporalFirstGermActual
  rw [installMatterTemporalFirstGermResponse_matter_coordinate]
  rw [currentP286CompleteActionResponseOperator_matter,
    c3h194_baseActual_matter_canonicalZeroSlice]
  simp [matterQuadraticTimeCoordinateCorrection,
    scalarQuadraticTimeCoefficient, localBaseCoordinate_apply,
    canonicalCauchySlicePoint, canonicalLorentzianTimeDirection]

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_conjugateMatter_canonicalZeroSlice
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
      0).conjugateMatter (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
      (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
        positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
        0)).conjugateMatter (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [currentP286CompleteActionResponseOperator_conjugateMatter]
  exact c3h194_baseActual_conjugateMatter_canonicalZeroSlice space

/-! ## Matter-current spatial germ on the fresh actual -/

private theorem c3h194_matterCurrent_cauchy_constant
    (direction : P286GaugeOneForm) (space : StageNineSpatialPoint) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction (canonicalCauchySlicePoint 0 space) =
      p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction 0 := by
  have matterOrigin :
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0).matter
          0 =
        diracSpinTwoMatterProbe := by
    rw [← c3h194_canonicalCauchySlicePoint_zero_zero]
    exact
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_matter_canonicalZeroSlice
        0
  have conjugateOrigin :
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
          0).conjugateMatter 0 =
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
    rw [← c3h194_canonicalCauchySlicePoint_zero_zero]
    exact
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_conjugateMatter_canonicalZeroSlice
        0
  unfold p286MatterCurrentCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
    holonomicMatterGaugeConnectionVariation p286GaugeConnectionMotherVariation
  simp only [toContinuumPointField]
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_matter_canonicalZeroSlice,
    matterOrigin,
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_conjugateMatter_canonicalZeroSlice,
    conjugateOrigin]
  simp

private theorem c3h194_matterCurrent_differentiableAt
    (direction : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction)
      0 := by
  apply p286MatterCurrent_differentiableAt_of_identityCoframe
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_smooth 0)
  funext point
  exact
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one
      0 point

private theorem c3h194_matterCurrent_spatialFirstGerm
    (axis : Fin 3) (direction : P286GaugeOneForm) :
    fieldDirectionalDerivative
        (p286MatterCurrentCoefficient positiveSmoothUnifiedSource
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction)
        0 axis.succ =
      0 := by
  exact fieldDirectionalDerivative_spatial_eq_zero_of_cauchy_constant
    _ (c3h194_matterCurrent_differentiableAt direction)
    (c3h194_matterCurrent_cauchy_constant direction) axis

/-! ## Direct complete-P286 BF differential momentum -/

private abbrev c3h194BaseActual : StageNineHolonomicConfiguration :=
  currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
    0

private abbrev c3h194DirectP286Actual : StageNineHolonomicConfiguration :=
  currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
    c3h194BaseActual

private theorem c3h194BaseActual_coframe_one (point : BasePoint) :
    c3h194BaseActual.coframe point = 1 := by
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
      0).coframe point =
      1
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe,
    positiveP506MatterCurrentCompleteFirstGermCanonicalGeneratedZeroResponseState_coframe_one]

private theorem c3h194_bfMomentum_eq_direct
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction =
      p286GaugeConnectionBFDifferentialMomentum c3h194DirectP286Actual
        direction := by
  rfl

private def c3h194_bfMomentumLinear
    (direction : P286GaugeTwoForm) : BasePoint →L[ℝ] ℝ :=
  (p286GaugeAuxiliaryHodgePairingPolynomial 1
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
          c3h194BaseActual))
      direction) •
      localBaseCoordinate canonicalLorentzianTimeDirection +
    ∑ axis : Fin 3,
      (canonicalP286EqualAxisCoefficient *
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (p286GaussAuxiliaryAxisEmbedding
              (currentP286GaussCharge positiveSmoothUnifiedSource
                c3h194BaseActual) axis)
            direction) •
        localBaseCoordinate axis.succ

private theorem c3h194_bfMomentum_affine
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction =
      fun point =>
        p286GaugeAuxiliaryHodgePairingPolynomial 1
            (currentP286OriginAuxiliaryCoordinate c3h194BaseActual) direction +
          c3h194_bfMomentumLinear direction point := by
  funext point
  rw [congrFun (c3h194_bfMomentum_eq_direct direction) point,
    currentP286CompleteActionResponseOperator_bfMomentum_affineNormalForm
      positiveSmoothUnifiedSource c3h194BaseActual
      c3h194BaseActual_coframe_one direction point]
  simp [c3h194_bfMomentumLinear, localBaseCoordinate_apply]
  have radialEq :
      (∑ axis : Fin 3,
          ((3 : ℝ)⁻¹ * point axis.succ) *
            p286GaugeAuxiliaryHodgePairingPolynomial 1
              (p286GaussAuxiliaryAxisEmbedding
                (currentP286GaussCharge positiveSmoothUnifiedSource
                  c3h194BaseActual) axis)
              direction) =
        ∑ axis : Fin 3,
          ((3 : ℝ)⁻¹ *
            p286GaugeAuxiliaryHodgePairingPolynomial 1
              (p286GaussAuxiliaryAxisEmbedding
                (currentP286GaussCharge positiveSmoothUnifiedSource
                  c3h194BaseActual) axis)
              direction) * point axis.succ := by
    apply Finset.sum_congr rfl
    intro axis _
    ring
  rw [radialEq]
  ring

private theorem c3h194_bfMomentum_derivative
    (direction : P286GaugeTwoForm) (point : BasePoint)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction)
        point derivativeDirection =
      c3h194_bfMomentumLinear direction
        (coordinateDirection derivativeDirection) := by
  rw [c3h194_bfMomentum_affine direction]
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add (differentiableAt_const _)
    (c3h194_bfMomentumLinear direction).differentiableAt,
    (c3h194_bfMomentumLinear direction).hasFDerivAt.fderiv]
  simp

private theorem c3h194_bfDivergence_constant
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction =
      fun _ =>
        ∑ derivativeDirection : LorentzianIndex,
          c3h194_bfMomentumLinear
              (p286GaugeExteriorDerivativeDirection derivativeDirection
                direction)
            (coordinateDirection derivativeDirection) := by
  funext point
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact c3h194_bfMomentum_derivative _ point derivativeDirection

private theorem c3h194_bfDivergence_differentiableAt
    (direction : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (p286GaugeConnectionBFDifferentialMomentumDivergence
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction)
      0 := by
  rw [c3h194_bfDivergence_constant direction]
  fun_prop

private theorem c3h194_bfDivergence_spatialFirstGerm
    (axis : Fin 3) (direction : P286GaugeOneForm) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentumDivergence
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction)
        0 axis.succ =
      0 := by
  rw [c3h194_bfDivergence_constant direction]
  simp [fieldDirectionalDerivative]

/-! ## Gauge-BF algebraic current on the fresh spatial slice -/

private theorem c3h194_connectionCoordinate_canonicalZeroSlice_zero
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeConnectionCoordinate
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        (canonicalCauchySlicePoint 0 space) =
      0 := by
  funext formDirection
  unfold holonomicP286GaugeConnectionCoordinate
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_gaugeConnection_canonicalZeroSlice_zero]
  simp

private theorem c3h194_bfAlgebraic_canonicalZeroSlice_zero
    (direction : P286GaugeOneForm) (space : StageNineSpatialPoint) :
    p286GaugeBFAlgebraicCoefficient
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction (canonicalCauchySlicePoint 0 space) =
      0 := by
  have algebraicZero :
      p286GaugeConnectionAlgebraicCurvatureDirection
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction (canonicalCauchySlicePoint 0 space) =
        0 := by
    unfold p286GaugeConnectionAlgebraicCurvatureDirection
      p286GaugeConnectionAlgebraicCurvatureVariation
    rw [c3h194_connectionCoordinate_canonicalZeroSlice_zero]
    funext pair
    simp
  unfold p286GaugeBFAlgebraicCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one,
    algebraicZero]
  simp

private theorem c3h194_bfAlgebraic_origin_zero
    (direction : P286GaugeOneForm) :
    p286GaugeBFAlgebraicCoefficient
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction 0 =
      0 := by
  rw [← c3h194_canonicalCauchySlicePoint_zero_zero]
  exact c3h194_bfAlgebraic_canonicalZeroSlice_zero direction 0

private theorem c3h194_bfAlgebraic_cauchy_constant
    (direction : P286GaugeOneForm) (space : StageNineSpatialPoint) :
    p286GaugeBFAlgebraicCoefficient
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction (canonicalCauchySlicePoint 0 space) =
      p286GaugeBFAlgebraicCoefficient
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction 0 := by
  rw [c3h194_bfAlgebraic_canonicalZeroSlice_zero,
    c3h194_bfAlgebraic_origin_zero]

private theorem c3h194_algebraicCurvatureDirection_contDiff
    (direction : P286GaugeOneForm) :
    ContDiff ℝ ∞ fun point =>
      p286GaugeConnectionAlgebraicCurvatureDirection
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction point := by
  apply contDiff_pi'
  intro pair
  have firstBracket : ContDiff ℝ ∞ fun point =>
      p286CoordinateLieBracket
        (direction (pairFirst pair))
        (holonomicP286GaugeConnectionCoordinate
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          point (pairSecond pair)) := by
    have actual :=
      (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.contDiff.comp
        (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
          direction (pairFirst pair))).clm_apply
        (contDiff_pi.mp c3h194_connectionCoordinate_contDiff
          (pairSecond pair))
    change ContDiff ℝ ∞ fun point =>
      p286CoordinateLieBracketBilinear.toContinuousBilinearMap
        (direction (pairFirst pair))
        (holonomicP286GaugeConnectionCoordinate
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          point (pairSecond pair))
    exact actual
  have secondBracket : ContDiff ℝ ∞ fun point =>
      p286CoordinateLieBracket
        (holonomicP286GaugeConnectionCoordinate
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          point (pairFirst pair))
        (direction (pairSecond pair)) := by
    have actual :=
      (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.contDiff.comp
        (contDiff_pi.mp c3h194_connectionCoordinate_contDiff
          (pairFirst pair))).clm_apply
        (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
          direction (pairSecond pair))
    change ContDiff ℝ ∞ fun point =>
      p286CoordinateLieBracketBilinear.toContinuousBilinearMap
        (holonomicP286GaugeConnectionCoordinate
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          point (pairFirst pair))
        (direction (pairSecond pair))
    exact actual
  unfold p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
  exact firstBracket.add secondBracket

private theorem c3h194_fixedBFIncrement_contDiff
    (auxiliary variation : BasePoint → P286GaugeTwoForm)
    (auxiliarySmooth : ContDiff ℝ ∞ auxiliary)
    (variationSmooth : ContDiff ℝ ∞ variation) :
    ContDiff ℝ ∞ fun point =>
      p286GaugeBFCurvatureIncrementDensity 1
        (coframeGaugeSpacetimeHodgeLinear 1)
        (auxiliary point) (variation point) := by
  have firstLiftSmooth := liftGaugeTwoFormOperator_apply_contDiff_p286
    (coframeTwoFormLinear 1) auxiliary auxiliarySmooth
  have hodgeLiftSmooth := liftGaugeTwoFormOperator_apply_contDiff_p286
    (coframeGaugeSpacetimeHodgeLinear 1) variation variationSmooth
  have secondLiftSmooth := liftGaugeTwoFormOperator_apply_contDiff_p286
    (coframeTwoFormLinear 1)
    (fun point => liftGaugeTwoFormOperator
      (coframeGaugeSpacetimeHodgeLinear 1) (variation point))
    hodgeLiftSmooth
  unfold p286GaugeBFCurvatureIncrementDensity
    generatedGaugeTwoFormMetricPairing
  apply ContDiff.sum
  intro pair _
  exact (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
      lorentzianTwoFormSign pair).mul
    (p286CoordinateLiePairing_apply_contDiff
      (fun point =>
        liftGaugeTwoFormOperator (coframeTwoFormLinear 1)
          (auxiliary point) pair)
      (fun point =>
        liftGaugeTwoFormOperator (coframeTwoFormLinear 1)
          (liftGaugeTwoFormOperator (coframeGaugeSpacetimeHodgeLinear 1)
            (variation point)) pair)
      (contDiff_pi.mp firstLiftSmooth pair)
      (contDiff_pi.mp secondLiftSmooth pair))

private theorem c3h194_bfAlgebraic_differentiableAt
    (direction : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (p286GaugeBFAlgebraicCoefficient
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction)
      0 := by
  have auxiliarySmooth := holonomicP286GaugeAuxiliaryCoordinate_contDiff
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_smooth 0)
  have incrementSmooth := c3h194_fixedBFIncrement_contDiff
    (holonomicP286GaugeAuxiliaryCoordinate
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0))
    (p286GaugeConnectionAlgebraicCurvatureDirection
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
      direction)
    auxiliarySmooth (c3h194_algebraicCurvatureDirection_contDiff direction)
  unfold p286GaugeBFAlgebraicCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [show
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0).coframe =
      fun _ => 1 by
    funext point
    exact
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one
        0 point]
  simp only [Matrix.det_one, abs_one, one_mul]
  exact incrementSmooth.differentiable (by simp) |>.differentiableAt

private theorem c3h194_bfAlgebraic_spatialFirstGerm
    (axis : Fin 3) (direction : P286GaugeOneForm) :
    fieldDirectionalDerivative
        (p286GaugeBFAlgebraicCoefficient
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction)
        0 axis.succ =
      0 := by
  exact fieldDirectionalDerivative_spatial_eq_zero_of_cauchy_constant
    _ (c3h194_bfAlgebraic_differentiableAt direction)
    (c3h194_bfAlgebraic_cauchy_constant direction) axis

/-! ## Scalar current as a linear readout of the fresh connection -/

private theorem c3h194_scalarGaugeVariation_normalForm
    (direction : P286GaugeOneForm) (point : BasePoint)
    (formDirection : LorentzianIndex) :
    holonomicScalarGaugeConnectionVariation
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        (fun _ => direction) point formDirection =
      scalarP286ActionBilinear (direction formDirection)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalar_vacuum]
  rfl

private def c3h194_minkowskiCoefficient
    (first second : LorentzianIndex) : ℝ :=
  minkowskiInternalMetric first second

private def c3h194_scalarCurrentAlgebraic
    (direction connection : P286GaugeOneForm) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ first : LorentzianIndex,
      ∑ second : LorentzianIndex,
        c3h194_minkowskiCoefficient first second *
          (scalarCoordinatePairingRe
              (scalarP286ActionBilinear (direction first)
                (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
              (scalarP286ActionBilinear (connection second)
                (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)) +
            scalarCoordinatePairingRe
              (scalarP286ActionBilinear (connection first)
                (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
              (scalarP286ActionBilinear (direction second)
                (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)))

private def c3h194_scalarConnectionActionAt
    (formDirection : LorentzianIndex) :
    P286GaugeOneForm →L[ℝ] ScalarCoordinateCarrier :=
  (scalarP286ActionBilinear.toContinuousBilinearMap.flip
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).comp
    (ContinuousLinearMap.proj formDirection :
      P286GaugeOneForm →L[ℝ] P286CoordinateCarrier)

private def c3h194_scalarCurrentLinear
    (direction : P286GaugeOneForm) : P286GaugeOneForm →L[ℝ] ℝ :=
  (1 / 2 : ℝ) •
    ∑ first : LorentzianIndex,
      ∑ second : LorentzianIndex,
        c3h194_minkowskiCoefficient first second •
          ((scalarCoordinatePairingReBilinear.toContinuousBilinearMap
              (scalarP286ActionBilinear (direction first)
                (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))).comp
              (c3h194_scalarConnectionActionAt second) +
            (scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip
              (scalarP286ActionBilinear (direction second)
                (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))).comp
              (c3h194_scalarConnectionActionAt first))

@[simp] private theorem c3h194_scalarCurrentLinear_apply
    (direction connection : P286GaugeOneForm) :
    c3h194_scalarCurrentLinear direction connection =
      c3h194_scalarCurrentAlgebraic direction connection := by
  simp [c3h194_scalarCurrentLinear, c3h194_scalarConnectionActionAt,
    c3h194_scalarCurrentAlgebraic, scalarCoordinatePairingReBilinear,
    mul_add]

private theorem c3h194_scalarCurrent_normalForm
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction point =
      c3h194_scalarCurrentAlgebraic direction
        (holonomicP286GaugeConnectionCoordinate
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          point) := by
  unfold p286ScalarCurrentCoefficient generatedVolumeDensity
    scalarGaugeConnectionKineticFirstVariationDensity
    c3h194_scalarCurrentAlgebraic
  simp only [toContinuumPointField]
  have frameVariation :
      scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0
          point
          (holonomicScalarGaugeConnectionVariation
            (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
            (fun _ => direction) point) =
        holonomicScalarGaugeConnectionVariation
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          (fun _ => direction) point := by
    funext formDirection
    exact scalarFrameRelativeCoordinates_zeroChart _ _ _
  have frameCovariant :
      scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0
          point
          (holonomicScalarCovariantDerivative
            (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
            point) =
        holonomicScalarCovariantDerivative
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          point := by
    funext formDirection
    exact scalarFrameRelativeCoordinates_zeroChart _ _ _
  have variationNormal :
      holonomicScalarGaugeConnectionVariation
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          (fun _ => direction) point =
        fun formDirection =>
          scalarP286ActionBilinear (direction formDirection)
            (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
    funext formDirection
    exact c3h194_scalarGaugeVariation_normalForm direction point formDirection
  have covariantNormal :
      holonomicScalarCovariantDerivative
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          point =
        fun formDirection =>
          scalarP286ActionBilinear
            (holonomicP286GaugeConnectionCoordinate
              (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
              point formDirection)
            (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
    funext formDirection
    exact
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_scalarCovariantDerivative_eq_fixedVacuumAction
        point formDirection
  rw [frameVariation, frameCovariant, variationNormal, covariantNormal]
  rw [positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one,
    Matrix.det_one, abs_one, one_mul]
  rw [lorentzianMetricOfCoframe_one_inv]
  rfl

private theorem c3h194_scalarCurrent_differentiableAt
    (direction : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction)
      0 := by
  let currentLinear := c3h194_scalarCurrentLinear direction
  let connection :=
    holonomicP286GaugeConnectionCoordinate
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 :=
    c3h194_connectionCoordinate_contDiff.differentiable (by simp) 0
  have functionEquality :
      p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction =
        currentLinear ∘ connection := by
    funext point
    rw [c3h194_scalarCurrent_normalForm direction point]
    exact (c3h194_scalarCurrentLinear_apply
      direction (connection point)).symm
  rw [functionEquality]
  exact (currentLinear.hasFDerivAt.comp 0
    connectionDifferentiable.hasFDerivAt).differentiableAt

private theorem c3h194_scalarCurrent_spatialFirstGerm
    (axis : Fin 3) (direction : P286GaugeOneForm) :
    fieldDirectionalDerivative
        (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction)
        0 axis.succ =
      0 := by
  let currentLinear := c3h194_scalarCurrentLinear direction
  let connection :=
    holonomicP286GaugeConnectionCoordinate
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 :=
    c3h194_connectionCoordinate_contDiff.differentiable (by simp) 0
  have functionEquality :
      p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction =
        currentLinear ∘ connection := by
    funext point
    rw [c3h194_scalarCurrent_normalForm direction point]
    exact (c3h194_scalarCurrentLinear_apply
      direction (connection point)).symm
  have derivative := currentLinear.hasFDerivAt.comp 0
    connectionDifferentiable.hasFDerivAt
  rw [functionEquality]
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  change currentLinear
      (fieldDirectionalDerivative connection 0 axis.succ) = 0
  rw [show fieldDirectionalDerivative connection 0 axis.succ = 0 by
    exact c3h194_connectionCoordinate_spatialDerivative_zero axis]
  exact map_zero currentLinear

/-! ## Complete P286 connection dual on the same fresh actual -/

private theorem c3h194_p286ConnectionEulerLagrange_sectorFunction
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction =
      (p286GaugeBFAlgebraicCoefficient
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction -
        p286GaugeConnectionBFDifferentialMomentumDivergence
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction) +
      p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction +
      p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction := by
  funext point
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance]
  unfold p286GaugeBFBalanceCoefficient
  rfl

theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_p286ConnectionEulerLagrange_differentiableAt_origin
    (direction : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction)
      0 := by
  rw [c3h194_p286ConnectionEulerLagrange_sectorFunction direction]
  exact (((c3h194_bfAlgebraic_differentiableAt direction).sub
      (c3h194_bfDivergence_differentiableAt direction)).add
    (c3h194_scalarCurrent_differentiableAt direction)).add
      (c3h194_matterCurrent_differentiableAt direction)

/-- C3h194 independent closure: after the branch-free action path has
generated the fresh C3h189 actual, its complete P286 connection dual has zero
first germ along every canonical spatial Cauchy axis.  This is evaluated on
that actual; it does not replay the historical `U****`, select a current
support branch, or claim global source-time evolution. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_p286ConnectionEulerLagrange_spatialCauchyFirstGerm
    (axis : Fin 3) (direction : P286GaugeOneForm) :
    fieldDirectionalDerivative
        (p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction)
        0 axis.succ =
      0 := by
  let bfAlgebraic :=
    p286GaugeBFAlgebraicCoefficient
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
      direction
  let bfDivergence :=
    p286GaugeConnectionBFDifferentialMomentumDivergence
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
      direction
  let scalarCurrent :=
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
      direction
  let matterCurrent :=
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
      direction
  have bfAlgebraicDifferentiable : DifferentiableAt ℝ bfAlgebraic 0 :=
    c3h194_bfAlgebraic_differentiableAt direction
  have bfDivergenceDifferentiable : DifferentiableAt ℝ bfDivergence 0 :=
    c3h194_bfDivergence_differentiableAt direction
  have scalarCurrentDifferentiable : DifferentiableAt ℝ scalarCurrent 0 :=
    c3h194_scalarCurrent_differentiableAt direction
  have matterCurrentDifferentiable : DifferentiableAt ℝ matterCurrent 0 :=
    c3h194_matterCurrent_differentiableAt direction
  rw [c3h194_p286ConnectionEulerLagrange_sectorFunction direction]
  rw [fieldDirectionalDerivative_add_real_at_origin
      ((bfAlgebraic - bfDivergence) + scalarCurrent) matterCurrent
      ((bfAlgebraicDifferentiable.sub bfDivergenceDifferentiable).add
        scalarCurrentDifferentiable)
      matterCurrentDifferentiable,
    fieldDirectionalDerivative_add_real_at_origin
      (bfAlgebraic - bfDivergence) scalarCurrent
      (bfAlgebraicDifferentiable.sub bfDivergenceDifferentiable)
      scalarCurrentDifferentiable,
    fieldDirectionalDerivative_sub_real_at_origin
      bfAlgebraic bfDivergence bfAlgebraicDifferentiable
      bfDivergenceDifferentiable,
    c3h194_bfAlgebraic_spatialFirstGerm axis direction,
    c3h194_bfDivergence_spatialFirstGerm axis direction,
    c3h194_scalarCurrent_spatialFirstGerm axis direction,
    c3h194_matterCurrent_spatialFirstGerm axis direction]
  ring

/-! ## Producer consistency at the common contact -/

private theorem c3h194_coframe_eq_direct :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0).coframe =
      c3h194DirectP286Actual.coframe := by
  rfl

private theorem c3h194_gaugeConnection_eq_direct :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
      0).gaugeConnection =
      c3h194DirectP286Actual.gaugeConnection := by
  rfl

private theorem c3h194_gaugeAuxiliary_eq_direct :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
      0).gaugeAuxiliary =
      c3h194DirectP286Actual.gaugeAuxiliary := by
  rfl

private theorem c3h194_scalar_eq_direct :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0).scalar =
      c3h194DirectP286Actual.scalar := by
  rfl

private theorem c3h194_conjugateMatter_eq_direct :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift
      0).conjugateMatter =
      c3h194DirectP286Actual.conjugateMatter := by
  rfl

private theorem c3h194_matter_origin_eq_direct :
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0).matter 0 =
      c3h194DirectP286Actual.matter 0 := by
  change
    (actionGeneratedMatterCompleteFirstGermActual positiveSmoothUnifiedSource
      (actionGeneratedMatterTemporalFirstGermActual positiveSmoothUnifiedSource
        c3h194DirectP286Actual)).matter 0 =
      c3h194DirectP286Actual.matter 0
  rw [actionGeneratedMatterCompleteFirstGermActual_matter_origin,
    actionGeneratedMatterTemporalFirstGermActual_matter_origin]

private theorem c3h194_scalarCovariantDerivative_origin_eq_direct :
    holonomicScalarCovariantDerivative
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0) 0 =
      holonomicScalarCovariantDerivative c3h194DirectP286Actual 0 := by
  unfold holonomicScalarCovariantDerivative
  rw [c3h194_scalar_eq_direct, c3h194_gaugeConnection_eq_direct]

private theorem c3h194_algebraicCurrent_origin_eq_direct
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient positiveSmoothUnifiedSource
        c3h194DirectP286Actual direction 0 := by
  exact p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contact
    positiveSmoothUnifiedSource
    (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
    c3h194DirectP286Actual 0
    (congrFun c3h194_coframe_eq_direct 0)
    (congrFun c3h194_gaugeConnection_eq_direct 0)
    (congrFun c3h194_gaugeAuxiliary_eq_direct 0)
    (congrFun c3h194_scalar_eq_direct 0)
    c3h194_scalarCovariantDerivative_origin_eq_direct
    c3h194_matter_origin_eq_direct
    (congrFun c3h194_conjugateMatter_eq_direct 0)
    direction

private theorem c3h194_bfDivergence_origin_eq_direct
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction 0 =
      p286GaugeConnectionBFDifferentialMomentumDivergence
        c3h194DirectP286Actual direction 0 := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [c3h194_bfMomentum_eq_direct]

/-- Re-substitution of the direct complete-P286 action response remains true
after the later matter and Lorentz-auxiliary installers, because they preserve
exactly the P286 fields consumed at the common contact.  This is producer
consistency, not the independent Cauchy first-germ closure above. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_p286ConnectionEquation_origin_producerConsistency
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
        direction 0 =
      0 := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [c3h194_algebraicCurrent_origin_eq_direct,
    c3h194_bfDivergence_origin_eq_direct]
  exact currentP286CompleteActionResponseOperator_connectionEquation_origin
    positiveSmoothUnifiedSource c3h194BaseActual
    c3h194BaseActual_coframe_one direction

/-! ## C3h194 role-separated authority -/

/-- Failure-capable local P286 spatial-Cauchy acceptance predicate.  It is a
readout of an already generated actual and carries no producer data. -/
structure StageNineP286ConnectionSpatialCauchyConstraintAt
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (point : BasePoint) : Prop where
  spatialFirstGerm :
    ∀ (axis : Fin 3) (direction : P286GaugeOneForm),
      fieldDirectionalDerivative
          (p286GaugeConnectionEulerLagrangeCoefficient source actual direction)
          point axis.succ =
        0

/-- C3h194 extends the exact same-actual C3h193 authority by one P286
spatial-Cauchy constraint.  The contact equation is retained in a separate
producer-consistency field so it is not counted again as independent
closure. -/
structure
    PositiveP506MatterCurrentCanonicalLorentzP286SpatialCauchyClosureLaw :
    Prop where
  priorC3h193 :
    PositiveP506MatterCurrentCanonicalLorentzScalarSimultaneousLocalLaw
  producerP286ConnectionConsistency :
    ∀ direction : P286GaugeOneForm,
      p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
          (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0)
          direction 0 =
        0
  independentP286ConnectionSpatialCauchyFirstGerm :
    StageNineP286ConnectionSpatialCauchyConstraintAt
      positiveSmoothUnifiedSource
      (positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0) 0

/-- Frontier theorem: the branch-free C3h189 actual now carries the direct
complete-P286 spatial Cauchy first-germ constraint in addition to the C3h193
gravity/Lorentz/scalar closure. -/
theorem
    positiveP506MatterCurrentCanonicalLorentzP286SpatialCauchyClosure_realizes_C3h194 :
    PositiveP506MatterCurrentCanonicalLorentzP286SpatialCauchyClosureLaw where
  priorC3h193 :=
    positiveP506MatterCurrentCanonicalLorentzScalarSimultaneousLocal_realizes_C3h193
  producerP286ConnectionConsistency :=
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_p286ConnectionEquation_origin_producerConsistency
  independentP286ConnectionSpatialCauchyFirstGerm := {
    spatialFirstGerm :=
      positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_p286ConnectionEulerLagrange_spatialCauchyFirstGerm }

end


end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzP286SpatialCauchyClosure
