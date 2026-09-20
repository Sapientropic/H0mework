import H0mework.Physics.MatterCurrent.P286PrincipalFirstGermResponse

/-!
# C3h183b: P286 connection spatial-Cauchy first-germ closure

The already generated exact P506/L0 actual `U****` is tested here against
the complete P286 gauge-connection Euler--Lagrange dual.  The matter Hessian
constructor did not solve this equation: it preserves the initial Cauchy
slice and every non-matter field.  Direct evaluation shows that all three
canonical spatial first germs vanish for every P286 one-form variation.

This is a local spatial-Cauchy statement.  It neither selects an event branch
from the P286 current support nor claims a temporal or global source-time
evolution.

The four sector calculations remain in one module because differentiability
and first-germ normalization must be assembled against the same complete P286
dual; splitting them would duplicate that integration seam and its local
instances without creating an independent mechanism.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterCompleteFirstGermP286ConnectionSpatialCauchyClosure

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineConnectionSectorSourceBalance
open StageNineCoframeTwoFormPairing
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterActionTimeVelocity
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286GaussRadialSecondJetLift
open StageNineP286SourceAffineCurvatureJetNormalForm
open StageNineP286TemporalVelocitySecondJetLift
open StageNinePositiveSourceNativeGravityCurvatureBridge
open StageNineResidualLimitCoframeBalanceDecision
open StageNineScalarActionSecondJetLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionLine
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullSynchronizedActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterCompleteFirstGermResponse
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterTemporalFirstGermResponse
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private theorem c3h183b_canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 0 = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-! ## The actual initial matter data -/

private theorem c3h183b_currentP286GaussCauchyState_matter_constant :
    positiveP506MatterCurrentP286GaussCauchyState.matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  unfold positiveP506MatterCurrentP286GaussCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  rw [
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_matter,
    positiveP506MatterCurrentGravityCoupledLocalActualLift_matter,
    positiveP506MatterCurrentGravityCoupledBaseActual_eq_synchronized]
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentLinearPlebanskiCauchyState 0
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact actionGeneratedMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentLinearPlebanskiCauchyState 0
    diracSpinTwoMatterProbe currentLinearPlebanskiCauchyState_matter_allSpace
    space

private theorem c3h183b_currentP286GaussCauchyState_conjugateMatter_constant :
    positiveP506MatterCurrentP286GaussCauchyState.conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  funext space
  unfold positiveP506MatterCurrentP286GaussCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_conjugateMatter,
    positiveP506MatterCurrentGravityCoupledLocalActualLift_conjugateMatter,
    positiveP506MatterCurrentGravityCoupledBaseActual_eq_synchronized]
  change
    actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentLinearPlebanskiCauchyState 0
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  exact actionGeneratedConjugateMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentLinearPlebanskiCauchyState 0
    diracSpinZeroMatterCoordinate
    currentLinearPlebanskiCauchyState_conjugate_allSpace space

private theorem c3h183b_lorentzResponseCauchyState_matter_constant :
    positiveP506MatterCurrentLorentzResponseCauchyState.matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  unfold positiveP506MatterCurrentLorentzResponseCauchyState
    canonicalCauchyRestriction
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact actionGeneratedMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentP286GaussCauchyState
    positiveP506MatterCurrentP286AxisContact diracSpinTwoMatterProbe
    c3h183b_currentP286GaussCauchyState_matter_constant space

private theorem c3h183b_lorentzResponseCauchyState_conjugateMatter_constant :
    positiveP506MatterCurrentLorentzResponseCauchyState.conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  funext space
  unfold positiveP506MatterCurrentLorentzResponseCauchyState
    canonicalCauchyRestriction
  change
    actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  exact actionGeneratedConjugateMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentP286GaussCauchyState
    positiveP506MatterCurrentP286AxisContact diracSpinZeroMatterCoordinate
    c3h183b_currentP286GaussCauchyState_conjugateMatter_constant space

private theorem c3h183b_UStar_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  rw [positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_matter]
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentLorentzResponseCauchyState 0
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact actionGeneratedMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentLorentzResponseCauchyState 0
    diracSpinTwoMatterProbe c3h183b_lorentzResponseCauchyState_matter_constant
    space

private theorem c3h183b_UStar_conjugateMatter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  rw [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_conjugateMatter]
  change
    actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentLorentzResponseCauchyState 0
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  exact actionGeneratedConjugateMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentLorentzResponseCauchyState 0
    diracSpinZeroMatterCoordinate
    c3h183b_lorentzResponseCauchyState_conjugateMatter_constant space

private theorem c3h183b_UStarSecondJetCauchyState_matter_constant :
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual).matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  unfold fullSynchronizedActionMatterCauchyState
    fullSynchronizedActionLorentzActual canonicalCauchyRestriction
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
    installP286HolonomicConnectionSecondJet varyP286GaugeConnectionCoordinate
  exact c3h183b_UStar_matter_zeroSlice space

private theorem c3h183b_UStarSecondJetCauchyState_conjugateMatter_constant :
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual).conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  funext space
  unfold fullSynchronizedActionMatterCauchyState
    fullSynchronizedActionLorentzActual canonicalCauchyRestriction
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
    installP286HolonomicConnectionSecondJet varyP286GaugeConnectionCoordinate
  exact c3h183b_UStar_conjugateMatter_zeroSlice space

private theorem c3h183b_UStarStar_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  unfold positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
    fullSynchronizedActionResponseOperator fullSynchronizedActionMatterActual
  exact actionGeneratedMatterLocalField_zeroSlice_of_constant
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual)
    0 diracSpinTwoMatterProbe
    c3h183b_UStarSecondJetCauchyState_matter_constant space

private theorem c3h183b_UStarStar_conjugateMatter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  unfold positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
    fullSynchronizedActionResponseOperator fullSynchronizedActionMatterActual
  exact actionGeneratedConjugateMatterLocalField_zeroSlice_of_constant
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual)
    0 diracSpinZeroMatterCoordinate
    c3h183b_UStarSecondJetCauchyState_conjugateMatter_constant space

private theorem c3h183b_UStarStarStar_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentTemporalFirstGermResponseActual.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  apply matterCoordinateEquiv.injective
  unfold positiveP506MatterCurrentTemporalFirstGermResponseActual
    actionGeneratedMatterTemporalFirstGermActual
  rw [installMatterTemporalFirstGermResponse_matter_coordinate]
  rw [c3h183b_UStarStar_matter_zeroSlice]
  simp [matterQuadraticTimeCoordinateCorrection,
    scalarQuadraticTimeCoefficient, localBaseCoordinate_apply,
    canonicalCauchySlicePoint, canonicalLorentzianTimeDirection]

private theorem c3h183b_UStarStarStar_conjugateMatter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentTemporalFirstGermResponseActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  rw [positiveP506MatterCurrentTemporalFirstGermResponseActual_conjugateMatter]
  exact c3h183b_UStarStar_conjugateMatter_zeroSlice space

private theorem c3h183b_UStarStarStarStar_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCompleteFirstGermResponseActual.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_matter_initialSlice
    (canonicalCauchySlicePoint 0 space) (by
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection])]
  exact c3h183b_UStarStarStar_matter_zeroSlice space

private theorem c3h183b_UStarStarStarStar_conjugateMatter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCompleteFirstGermResponseActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_conjugateMatter]
  exact c3h183b_UStarStarStar_conjugateMatter_zeroSlice space

/-! Public zero-slice interfaces used by later same-contact action replay.
These are field readouts of the already generated actuals; they do not add a
Cauchy datum or a branch selector to either producer. -/

theorem
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_matter_canonicalZeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe :=
  c3h183b_UStarStar_matter_zeroSlice space

theorem
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_actionMatterCauchyState_matter_constant :
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual).matter =
      fun _ => diracSpinTwoMatterProbe :=
  c3h183b_UStarSecondJetCauchyState_matter_constant

theorem
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_conjugateMatter_canonicalZeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) :=
  c3h183b_UStarStar_conjugateMatter_zeroSlice space

theorem
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_actionMatterCauchyState_conjugateMatter_constant :
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual).conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) :=
  c3h183b_UStarSecondJetCauchyState_conjugateMatter_constant

theorem
    positiveP506MatterCurrentCompleteFirstGermResponseActual_matter_canonicalZeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCompleteFirstGermResponseActual.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe :=
  c3h183b_UStarStarStarStar_matter_zeroSlice space

theorem
    positiveP506MatterCurrentCompleteFirstGermResponseActual_conjugateMatter_canonicalZeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentCompleteFirstGermResponseActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) :=
  c3h183b_UStarStarStarStar_conjugateMatter_zeroSlice space

/-! ## Shared actual normal forms -/

private theorem c3h183b_coframe_one (point : BasePoint) :
    positiveP506MatterCurrentCompleteFirstGermResponseActual.coframe point =
      1 := by
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_coframe,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_coframe]
  exact
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_coframe_one
      point

private theorem c3h183b_scalar_vacuum :
    positiveP506MatterCurrentCompleteFirstGermResponseActual.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_scalar,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_scalar]
  exact
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalar_vacuum

private theorem c3h183b_connectionCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteFirstGermResponseActual point =
      c3h181FullConnectionNormalForm point := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_gaugeConnection,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_gaugeConnection]
  exact
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm
      point

private theorem c3h183b_connectionCoordinate_line
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteFirstGermResponseActual point
        direction =
      c3h181FullConnectionCoefficient point direction •
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_gaugeConnection,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_gaugeConnection]
  exact
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line
      point direction

private theorem c3h183b_auxiliaryCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        positiveP506MatterCurrentCompleteFirstGermResponseActual point =
      c3h181FullAuxiliaryCoordinateNormalForm point := by
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_gaugeAuxiliary,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_gaugeAuxiliary]
  exact
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_auxiliaryCoordinate_normalForm
      point

/-! The matter-only responses preserve the already generated P286 connection.
Its spatial one-jet at the common contact is therefore still the zero jet of
the C3h181 action-principal actual. -/

private theorem c3h183b_connectionDerivative_eq_principalActual
    (point : BasePoint) (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        positiveP506MatterCurrentCompleteFirstGermResponseActual point
        derivativeDirection formDirection =
      p286GaugeConnectionCoordinateDerivative
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        point derivativeDirection formDirection := by
  unfold p286GaugeConnectionCoordinateDerivative
  rw [show
    (fun candidate =>
      holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteFirstGermResponseActual candidate
        formDirection) =
      fun candidate =>
        holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          candidate formDirection by
    funext candidate
    rw [congrFun (c3h183b_connectionCoordinate_normalForm candidate)
      formDirection]
    exact
      (congrFun
        (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm
          candidate) formDirection).symm]

theorem positiveP506MatterCurrentCompleteFirstGermResponseActual_connectionSpatialOneJet_zero
    (axis : Fin 3) (formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        positiveP506MatterCurrentCompleteFirstGermResponseActual 0 axis.succ
        formDirection =
      0 := by
  rw [c3h183b_connectionDerivative_eq_principalActual,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionDerivative_normalForm]
  fin_cases axis <;> fin_cases formDirection <;>
    simp [c3h181U7ConnectionLinear,
      positiveP506MatterCurrentCompleteActionPrincipalSecondJet,
      positiveActionGeneratedTemporalVelocityP286SecondJet,
      positiveActionGeneratedGaussRadialP286SecondJet,
      p286TemporalVelocityActionSecondJet,
      p286TemporalVelocityActionSecondJetAmbient,
      p286GaussRadialActionSecondJet,
      p286GaussRadialActionSecondJetAmbient,
      ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply,
      coordinateDirection, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem c3h183b_connectionCoordinate_contDiff :
    ContDiff ℝ ∞
      (holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteFirstGermResponseActual) := by
  rcases positiveP506MatterCurrentCompleteFirstGermResponseActual_smooth with
    ⟨_, _, _, _, gaugeConnectionSmooth, _, _, _, _⟩
  apply contDiff_pi.mpr
  intro formDirection
  simpa [holonomicP286GaugeConnectionCoordinate] using
    gaugeConnectionSmooth formDirection

private theorem c3h183b_connectionCoordinate_spatialDerivative_zero
    (axis : Fin 3) :
    fieldDirectionalDerivative
        (holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentCompleteFirstGermResponseActual)
        0 axis.succ =
      0 := by
  funext formDirection
  have component :=
    positiveP506MatterCurrentCompleteFirstGermResponseActual_connectionSpatialOneJet_zero
      axis formDirection
  unfold p286GaugeConnectionCoordinateDerivative at component
  unfold fieldDirectionalDerivative at component ⊢
  rw [fderiv_apply
    (c3h183b_connectionCoordinate_contDiff.differentiable (by simp) 0)
    formDirection] at component
  simpa using component

/-! ## Spatial slice calculus -/

theorem fieldDirectionalDerivative_spatial_eq_zero_of_cauchy_constant
    (field : BasePoint → ℝ)
    (fieldDifferentiable : DifferentiableAt ℝ field 0)
    (constant : ∀ space : StageNineSpatialPoint,
      field (canonicalCauchySlicePoint 0 space) = field 0)
    (axis : Fin 3) :
    fieldDirectionalDerivative field 0 axis.succ = 0 := by
  have sliceDerivative :=
    (show DifferentiableAt ℝ field (canonicalCauchySlicePoint 0 0) by
      rw [c3h183b_canonicalCauchySlicePoint_zero_zero]
      exact fieldDifferentiable).hasFDerivAt.comp
      (0 : StageNineSpatialPoint)
      (canonicalCauchySlicePoint_hasFDerivAt 0 0)
  rw [c3h183b_canonicalCauchySlicePoint_zero_zero] at sliceDerivative
  have sliceFDerivZero :
      fderiv ℝ (field ∘ canonicalCauchySlicePoint 0)
          (0 : StageNineSpatialPoint) =
        0 := by
    rw [show field ∘ canonicalCauchySlicePoint 0 =
        fun _ : StageNineSpatialPoint => field 0 by
      funext space
      exact constant space]
    simp
  rw [sliceDerivative.fderiv] at sliceFDerivZero
  have applied := congrArg
    (fun derivative : StageNineSpatialPoint →L[ℝ] ℝ =>
      derivative (canonicalSpatialCoordinateDirection axis))
    sliceFDerivZero
  unfold fieldDirectionalDerivative
  simpa [ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection] using applied

/-! ## Matter-current spatial germ -/

private theorem c3h183b_matterCurrent_cauchy_constant
    (direction : P286GaugeOneForm) (space : StageNineSpatialPoint) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction
        (canonicalCauchySlicePoint 0 space) =
      p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction 0 := by
  have matterOrigin :
      positiveP506MatterCurrentCompleteFirstGermResponseActual.matter 0 =
        diracSpinTwoMatterProbe := by
    rw [← c3h183b_canonicalCauchySlicePoint_zero_zero]
    exact c3h183b_UStarStarStarStar_matter_zeroSlice 0
  have conjugateOrigin :
      positiveP506MatterCurrentCompleteFirstGermResponseActual.conjugateMatter
          0 =
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
    rw [← c3h183b_canonicalCauchySlicePoint_zero_zero]
    exact c3h183b_UStarStarStarStar_conjugateMatter_zeroSlice 0
  unfold p286MatterCurrentCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
    holonomicMatterGaugeConnectionVariation p286GaugeConnectionMotherVariation
  simp only [toContinuumPointField]
  rw [c3h183b_coframe_one, c3h183b_coframe_one,
    c3h183b_UStarStarStarStar_matter_zeroSlice, matterOrigin,
    c3h183b_UStarStarStarStar_conjugateMatter_zeroSlice, conjugateOrigin]
  simp

theorem p286MatterCurrent_differentiableAt_of_identityCoframe
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (coframeOne : configuration.coframe = fun _ => 1)
    (direction : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        configuration direction)
      0 := by
  let vector : BasePoint → DiracExteriorMatterCarrier := fun point =>
    matterGaugeConnectionVariationVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField configuration point)
      (holonomicMatterGaugeConnectionVariation configuration
        (fun _ => direction) point)
  rcases smooth with
    ⟨_, _, _, _, _, _, _, matterSmooth, conjugateSmooth⟩
  have variationCoordinateSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (holonomicMatterGaugeConnectionVariation configuration
            (fun _ => direction) point formDirection) := by
    have actual :=
      (StageNineCoframeScalarMatterRegularity.matterP286ActionCoordinateBilinear
          |>.toContinuousBilinearMap |>.contDiff |>.comp
            (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
              direction formDirection)).clm_apply matterSmooth
    unfold holonomicMatterGaugeConnectionVariation
      p286GaugeConnectionMotherVariation
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm
            (direction formDirection)))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (configuration.matter point)))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have gammaVariationCoordinateSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := 1, derivative := 0 } formDirection)
            (holonomicMatterGaugeConnectionVariation configuration
              (fun _ => direction) point formDirection)) := by
    have actual :=
      (StageNineCoframeScalarMatterRegularity.diracMatrixMatterCoordinateRealBilinear
          |>.toContinuousBilinearMap |>.contDiff |>.comp
            (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
              inverseCoframeDiracGamma
                { coframe := 1, derivative := 0 } formDirection)).clm_apply
        (variationCoordinateSmooth formDirection)
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := 1, derivative := 0 } formDirection)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (holonomicMatterGaugeConnectionVariation configuration
                (fun _ => direction) point formDirection)))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have sumSmooth : ContDiff ℝ ∞ fun point =>
      ∑ formDirection : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := 1, derivative := 0 } formDirection)
            (holonomicMatterGaugeConnectionVariation configuration
              (fun _ => direction) point formDirection)) := by
    apply ContDiff.sum
    intro formDirection _
    exact gammaVariationCoordinateSmooth formDirection
  have vectorCoordinateSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (vector point) := by
    have withISmooth : ContDiff ℝ ∞ fun point =>
        Complex.I •
          ∑ formDirection : LorentzianIndex,
            matterCoordinateEquiv
              (diracMatrixMatterAction
                (inverseCoframeDiracGamma
                  { coframe := 1, derivative := 0 } formDirection)
                (holonomicMatterGaugeConnectionVariation configuration
                  (fun _ => direction) point formDirection)) :=
      (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint => Complex.I).smul
        sumSmooth
    dsimp [vector]
    unfold matterGaugeConnectionVariationVector matterGaugeKineticSum
      matterDerivativeFrameRelative
    simp only [toContinuumPointField]
    rw [coframeOne]
    simpa only [matterFrameRelative_zeroChart, map_sum, map_smul] using
      withISmooth
  have pairingSumSmooth : ContDiff ℝ ∞ fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
    apply ContDiff.sum
    intro index _
    let coordinateLinear : MatterCoordinateCarrier →L[ℝ] ℂ :=
      (PiLp.projₗ (𝕜 := ℂ) 2
        (fun _ : MatterCoordinateIndex => ℂ) index)
        |>.toContinuousLinearMap |>.restrictScalars ℝ
    have vectorEntrySmooth : ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv (vector point) index :=
      coordinateLinear.contDiff.comp vectorCoordinateSmooth
    exact vectorEntrySmooth.mul (conjugateSmooth index)
  have dualPairingSmooth : ContDiff ℝ ∞ fun point =>
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
    exact pairingSumSmooth
  have realPairingSmooth : ContDiff ℝ ∞ fun point =>
      (configuration.conjugateMatter point (vector point)).re :=
    Complex.reCLM.contDiff.comp dualPairingSmooth
  unfold p286MatterCurrentCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart]
  change DifferentiableAt ℝ
    (fun point =>
      |Matrix.det (configuration.coframe point)| *
        (configuration.conjugateMatter point (vector point)).re) 0
  rw [coframeOne]
  simp only [Matrix.det_one, abs_one, one_mul]
  exact realPairingSmooth.differentiable (by simp) |>.differentiableAt

private theorem c3h183b_matterCurrent_differentiableAt
    (direction : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
      0 := by
  apply p286MatterCurrent_differentiableAt_of_identityCoframe
    positiveP506MatterCurrentCompleteFirstGermResponseActual
    positiveP506MatterCurrentCompleteFirstGermResponseActual_smooth
  funext point
  exact c3h183b_coframe_one point

private theorem c3h183b_matterCurrent_spatialFirstGerm
    (axis : Fin 3) (direction : P286GaugeOneForm) :
    fieldDirectionalDerivative
        (p286MatterCurrentCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
        0 axis.succ =
      0 := by
  exact fieldDirectionalDerivative_spatial_eq_zero_of_cauchy_constant
    _ (c3h183b_matterCurrent_differentiableAt direction)
    (c3h183b_matterCurrent_cauchy_constant direction) axis

/-! ## Gauge-BF differential momentum -/

private theorem c3h183b_bfMomentum_eq_completeResponse
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction =
      p286GaugeConnectionBFDifferentialMomentum
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift direction := by
  funext point
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [c3h183b_coframe_one,
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_coframe_one,
    c3h183b_auxiliaryCoordinate_normalForm,
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_auxiliaryCoordinate,
    positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate_normalForm]

private def c3h183b_bfMomentumLinear
    (direction : P286GaugeTwoForm) : BasePoint →L[ℝ] ℝ :=
  (p286GaugeAuxiliaryHodgePairingPolynomial 1
      (p286SpatialAuxiliaryVelocityEmbedding
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity)
      direction) •
      localBaseCoordinate canonicalLorentzianTimeDirection +
    ∑ axis : Fin 3,
      ((1 / 3 : ℝ) *
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (p286GaussAuxiliaryAxisEmbedding
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge axis)
            direction) •
        localBaseCoordinate axis.succ

private theorem c3h183b_bfMomentum_affine
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction =
      fun point =>
        p286GaugeAuxiliaryHodgePairingPolynomial 1
            positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate
            direction +
          c3h183b_bfMomentumLinear direction point := by
  funext point
  rw [c3h183b_bfMomentum_eq_completeResponse direction,
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_bfMomentum_affineNormalForm]
  simp [c3h183b_bfMomentumLinear, localBaseCoordinate_apply]
  have radialEq :
      (∑ axis : Fin 3,
          (3 : ℝ)⁻¹ * point axis.succ *
            p286GaugeAuxiliaryHodgePairingPolynomial 1
              (p286GaussAuxiliaryAxisEmbedding
                positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge axis)
              direction) =
        ∑ axis : Fin 3,
          (3 : ℝ)⁻¹ *
            p286GaugeAuxiliaryHodgePairingPolynomial 1
              (p286GaussAuxiliaryAxisEmbedding
                positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge axis)
              direction * point axis.succ := by
    apply Finset.sum_congr rfl
    intro axis _
    ring
  rw [radialEq]
  ring

private theorem c3h183b_bfMomentum_derivative
    (direction : P286GaugeTwoForm) (point : BasePoint)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
        point derivativeDirection =
      c3h183b_bfMomentumLinear direction
        (coordinateDirection derivativeDirection) := by
  rw [c3h183b_bfMomentum_affine direction]
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add (differentiableAt_const _)
    (c3h183b_bfMomentumLinear direction).differentiableAt,
    (c3h183b_bfMomentumLinear direction).hasFDerivAt.fderiv]
  simp

private theorem c3h183b_bfDivergence_constant
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction =
      fun _ =>
        ∑ derivativeDirection : LorentzianIndex,
          c3h183b_bfMomentumLinear
              (p286GaugeExteriorDerivativeDirection derivativeDirection
                direction)
            (coordinateDirection derivativeDirection) := by
  funext point
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact c3h183b_bfMomentum_derivative _ point derivativeDirection

private theorem c3h183b_bfDivergence_spatialFirstGerm
    (axis : Fin 3) (direction : P286GaugeOneForm) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentumDivergence
          positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
        0 axis.succ =
      0 := by
  rw [c3h183b_bfDivergence_constant direction]
  simp [fieldDirectionalDerivative]

/-! ## Scalar current -/

private theorem c3h183b_scalarGaugeVariation_normalForm
    (direction : P286GaugeOneForm) (point : BasePoint)
    (formDirection : LorentzianIndex) :
    holonomicScalarGaugeConnectionVariation
        positiveP506MatterCurrentCompleteFirstGermResponseActual
        (fun _ => direction) point formDirection =
      scalarP286ActionBilinear (direction formDirection)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  rw [c3h183b_scalar_vacuum]
  change
    scalarMotherLieAction
        (p286LieBlockEmbed (p286CoordinateEquiv.symm (direction formDirection)))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      scalarMotherLieAction
        (p286LieBlockEmbed (p286CoordinateEquiv.symm (direction formDirection)))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
  rfl

private theorem c3h183b_scalarCovariantDerivative_normalForm
    (point : BasePoint) (formDirection : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        positiveP506MatterCurrentCompleteFirstGermResponseActual point
        formDirection =
      scalarP286ActionBilinear
        (holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentCompleteFirstGermResponseActual point
          formDirection)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  unfold holonomicScalarCovariantDerivative
  rw [c3h183b_scalar_vacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add]
  unfold holonomicP286GaugeConnectionCoordinate
  change
    scalarMotherLieAction
        (p286LieBlockEmbed
          (positiveP506MatterCurrentCompleteFirstGermResponseActual.gaugeConnection
            point formDirection))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (p286CoordinateEquiv
              (positiveP506MatterCurrentCompleteFirstGermResponseActual.gaugeConnection
                point formDirection))))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
  rw [p286CoordinateEquiv.symm_apply_apply]

private def c3h183b_minkowskiCoefficient
    (first second : LorentzianIndex) : ℝ :=
  minkowskiInternalMetric first second

private def c3h183b_scalarCurrentAlgebraic
    (direction connection : P286GaugeOneForm) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ first : LorentzianIndex,
      ∑ second : LorentzianIndex,
        c3h183b_minkowskiCoefficient first second *
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

private def c3h183b_scalarConnectionActionAt
    (formDirection : LorentzianIndex) :
    P286GaugeOneForm →L[ℝ] ScalarCoordinateCarrier :=
  (scalarP286ActionBilinear.toContinuousBilinearMap.flip
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).comp
    (ContinuousLinearMap.proj formDirection :
      P286GaugeOneForm →L[ℝ] P286CoordinateCarrier)

private def c3h183b_scalarCurrentLinear
    (direction : P286GaugeOneForm) : P286GaugeOneForm →L[ℝ] ℝ :=
  (1 / 2 : ℝ) •
    ∑ first : LorentzianIndex,
      ∑ second : LorentzianIndex,
        c3h183b_minkowskiCoefficient first second •
          ((scalarCoordinatePairingReBilinear.toContinuousBilinearMap
              (scalarP286ActionBilinear (direction first)
                (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))).comp
              (c3h183b_scalarConnectionActionAt second) +
            (scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip
              (scalarP286ActionBilinear (direction second)
                (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))).comp
              (c3h183b_scalarConnectionActionAt first))

@[simp] private theorem c3h183b_scalarCurrentLinear_apply
    (direction connection : P286GaugeOneForm) :
    c3h183b_scalarCurrentLinear direction connection =
      c3h183b_scalarCurrentAlgebraic direction connection := by
  simp [c3h183b_scalarCurrentLinear, c3h183b_scalarConnectionActionAt,
    c3h183b_scalarCurrentAlgebraic, scalarCoordinatePairingReBilinear,
    mul_add]

private theorem c3h183b_scalarCurrent_normalForm
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction
        point =
      c3h183b_scalarCurrentAlgebraic direction
        (holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentCompleteFirstGermResponseActual point) := by
  unfold p286ScalarCurrentCoefficient generatedVolumeDensity
    scalarGaugeConnectionKineticFirstVariationDensity
    c3h183b_scalarCurrentAlgebraic
  simp only [toContinuumPointField]
  have frameVariation :
      scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0
          point
          (holonomicScalarGaugeConnectionVariation
            positiveP506MatterCurrentCompleteFirstGermResponseActual
            (fun _ => direction) point) =
        holonomicScalarGaugeConnectionVariation
          positiveP506MatterCurrentCompleteFirstGermResponseActual
          (fun _ => direction) point := by
    funext formDirection
    exact scalarFrameRelativeCoordinates_zeroChart _ _ _
  have frameCovariant :
      scalarFrameRelativeCovariantDerivative positiveSmoothUnifiedSource 0
          point
          (holonomicScalarCovariantDerivative
            positiveP506MatterCurrentCompleteFirstGermResponseActual point) =
        holonomicScalarCovariantDerivative
          positiveP506MatterCurrentCompleteFirstGermResponseActual point := by
    funext formDirection
    exact scalarFrameRelativeCoordinates_zeroChart _ _ _
  have variationNormal :
      holonomicScalarGaugeConnectionVariation
          positiveP506MatterCurrentCompleteFirstGermResponseActual
          (fun _ => direction) point =
        fun formDirection =>
          scalarP286ActionBilinear (direction formDirection)
            (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
    funext formDirection
    exact c3h183b_scalarGaugeVariation_normalForm direction point formDirection
  have covariantNormal :
      holonomicScalarCovariantDerivative
          positiveP506MatterCurrentCompleteFirstGermResponseActual point =
        fun formDirection =>
          scalarP286ActionBilinear
            (holonomicP286GaugeConnectionCoordinate
              positiveP506MatterCurrentCompleteFirstGermResponseActual point
              formDirection)
            (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
    funext formDirection
    exact c3h183b_scalarCovariantDerivative_normalForm point formDirection
  rw [frameVariation, frameCovariant, variationNormal, covariantNormal]
  rw [c3h183b_coframe_one, Matrix.det_one, abs_one, one_mul]
  rw [lorentzianMetricOfCoframe_one_inv]
  rfl

private theorem c3h183b_scalarCurrent_spatialFirstGerm
    (axis : Fin 3) (direction : P286GaugeOneForm) :
    fieldDirectionalDerivative
        (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
        0 axis.succ =
      0 := by
  let currentLinear := c3h183b_scalarCurrentLinear direction
  let connection :=
    holonomicP286GaugeConnectionCoordinate
      positiveP506MatterCurrentCompleteFirstGermResponseActual
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 :=
    c3h183b_connectionCoordinate_contDiff.differentiable (by simp) 0
  have functionEquality :
      p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteFirstGermResponseActual direction =
        currentLinear ∘ connection := by
    funext point
    rw [c3h183b_scalarCurrent_normalForm direction point]
    exact (c3h183b_scalarCurrentLinear_apply direction (connection point)).symm
  have derivative := currentLinear.hasFDerivAt.comp 0
    connectionDifferentiable.hasFDerivAt
  rw [functionEquality]
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  change currentLinear
      (fieldDirectionalDerivative connection 0 axis.succ) = 0
  rw [show fieldDirectionalDerivative connection 0 axis.succ = 0 by
    exact c3h183b_connectionCoordinate_spatialDerivative_zero axis]
  exact map_zero currentLinear

/-! ## Gauge-BF algebraic current

Every spacetime component of the generated connection and auxiliary lies on
the same generated Gauss-charge line.  Invariance of the P286 pairing then
kills its pairing with every algebraic commutator.  This is not an Abelian
assumption and does not project the arbitrary test direction. -/

private def c3h183b_auxiliaryCoefficient
    (point : BasePoint) : Fin 6 → ℝ :=
  ![
    0, 0, 0,
    (1 / 3 : ℝ) * (1 + point 1),
    (1 / 3 : ℝ) * point 2,
    (1 / 3 : ℝ) * point 3 -
      point canonicalLorentzianTimeDirection
  ]

private theorem c3h183b_auxiliaryCoordinate_line
    (point : BasePoint) (pair : Fin 6) :
    c3h181FullAuxiliaryCoordinateNormalForm point pair =
      c3h183b_auxiliaryCoefficient point pair •
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  fin_cases pair <;>
    simp [c3h181FullAuxiliaryCoordinateNormalForm,
      c3h183b_auxiliaryCoefficient]

private theorem c3h183b_charge_pairing_direction_chargeBracket_zero
    (direction : P286CoordinateCarrier) :
    p286CoordinateLiePairing
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
        (p286CoordinateLieBracket direction
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge) =
      0 := by
  calc
    p286CoordinateLiePairing
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
          (p286CoordinateLieBracket direction
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge) =
        p286CoordinateLiePairing
          (p286CoordinateLieBracket direction
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge :=
      p286CoordinateLiePairing_symmetric _ _
    _ = p286CoordinateLiePairing direction
          (p286CoordinateLieBracket
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge) := by
      rw [p286CoordinateLiePairing_bracket_left_local]
    _ = 0 := by
      rw [p286CoordinateLieBracket_self]
      simp

private theorem c3h183b_charge_pairing_chargeBracket_direction_zero
    (direction : P286CoordinateCarrier) :
    p286CoordinateLiePairing
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
        (p286CoordinateLieBracket
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge direction) =
      0 := by
  calc
    p286CoordinateLiePairing
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
          (p286CoordinateLieBracket
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge direction) =
        p286CoordinateLiePairing
          (p286CoordinateLieBracket
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge direction)
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge :=
      p286CoordinateLiePairing_symmetric _ _
    _ = p286CoordinateLiePairing
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
          (p286CoordinateLieBracket direction
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge) := by
      rw [p286CoordinateLiePairing_bracket_left_local]
    _ = 0 :=
      c3h183b_charge_pairing_direction_chargeBracket_zero direction

private theorem c3h183b_scaledCharge_pairing_direction_scaledChargeBracket_zero
    (left right : ℝ) (direction : P286CoordinateCarrier) :
    p286CoordinateLiePairing
        (left • positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)
        (p286CoordinateLieBracket direction
          (right •
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)) =
      0 := by
  rw [p286CoordinateLieBracket_smul_right,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_right,
    c3h183b_charge_pairing_direction_chargeBracket_zero]
  ring

private theorem c3h183b_scaledCharge_pairing_scaledChargeBracket_direction_zero
    (left right : ℝ) (direction : P286CoordinateCarrier) :
    p286CoordinateLiePairing
        (left • positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)
        (p286CoordinateLieBracket
          (right • positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)
          direction) =
      0 := by
  rw [p286CoordinateLieBracket_smul_left,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_right,
    c3h183b_charge_pairing_chargeBracket_direction_zero]
  ring

private theorem c3h183b_chargeLine_bfIncrement_zero
    (auxiliaryCoefficient : Fin 6 → ℝ)
    (connectionCoefficient : LorentzianIndex → ℝ)
    (direction : P286GaugeOneForm) :
    p286GaugeBFCurvatureIncrementDensity 1 lorentzianCoframeHodge
        (fun pair => auxiliaryCoefficient pair •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)
        (fun pair =>
          p286CoordinateLieBracket
              (direction (pairFirst pair))
              (connectionCoefficient (pairSecond pair) •
                positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge) +
            p286CoordinateLieBracket
              (connectionCoefficient (pairFirst pair) •
                positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)
              (direction (pairSecond pair))) =
      0 := by
  unfold p286GaugeBFCurvatureIncrementDensity
    generatedGaugeTwoFormMetricPairing
  rw [coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_id_p286,
    liftGaugeTwoFormOperator_fixedHodge_apply_local]
  rw [Fin.sum_univ_six]
  simp [lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, p286CoordinateLiePairing_add_right,
    c3h183b_scaledCharge_pairing_direction_scaledChargeBracket_zero,
    c3h183b_scaledCharge_pairing_scaledChargeBracket_direction_zero]

/-- On the generated actual, the complete gauge-BF algebraic current vanishes
on the whole local domain for every P286 test direction.  The reason is the
common generated `Q`-line and invariant pairing, not commutativity of the
test direction. -/
theorem positiveP506MatterCurrentCompleteFirstGermResponseActual_p286BFAlgebraic_zero
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeBFAlgebraicCoefficient
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction
        point =
      0 := by
  unfold p286GaugeBFAlgebraicCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [c3h183b_coframe_one, Matrix.det_one, abs_one, one_mul,
    coframeGaugeSpacetimeHodgeLinear_one,
    c3h183b_auxiliaryCoordinate_normalForm]
  have auxiliaryLine :
      c3h181FullAuxiliaryCoordinateNormalForm point =
        fun pair => c3h183b_auxiliaryCoefficient point pair •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
    funext pair
    exact c3h183b_auxiliaryCoordinate_line point pair
  have connectionLine :
      holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentCompleteFirstGermResponseActual point =
        fun formDirection =>
          c3h181FullConnectionCoefficient point formDirection •
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
    funext formDirection
    exact c3h183b_connectionCoordinate_line point formDirection
  rw [auxiliaryLine]
  unfold p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
  rw [connectionLine]
  exact c3h183b_chargeLine_bfIncrement_zero
    (c3h183b_auxiliaryCoefficient point)
    (c3h181FullConnectionCoefficient point) direction

private theorem c3h183b_bfAlgebraic_differentiableAt
    (direction : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (p286GaugeBFAlgebraicCoefficient
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
      0 := by
  rw [show
    p286GaugeBFAlgebraicCoefficient
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction =
      fun _ => 0 by
    funext point
    exact
      positiveP506MatterCurrentCompleteFirstGermResponseActual_p286BFAlgebraic_zero
        direction point]
  fun_prop

private theorem c3h183b_bfAlgebraic_spatialFirstGerm
    (axis : Fin 3) (direction : P286GaugeOneForm) :
    fieldDirectionalDerivative
        (p286GaugeBFAlgebraicCoefficient
          positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
        0 axis.succ =
      0 := by
  rw [show
    p286GaugeBFAlgebraicCoefficient
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction =
      fun _ => 0 by
    funext point
    exact
      positiveP506MatterCurrentCompleteFirstGermResponseActual_p286BFAlgebraic_zero
        direction point]
  simp [fieldDirectionalDerivative]

/-! ## Complete P286 connection dual -/

private theorem c3h183b_bfDivergence_differentiableAt
    (direction : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (p286GaugeConnectionBFDifferentialMomentumDivergence
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
      0 := by
  rw [c3h183b_bfDivergence_constant direction]
  fun_prop

private theorem c3h183b_scalarCurrent_differentiableAt
    (direction : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
      0 := by
  let currentLinear := c3h183b_scalarCurrentLinear direction
  let connection :=
    holonomicP286GaugeConnectionCoordinate
      positiveP506MatterCurrentCompleteFirstGermResponseActual
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 :=
    c3h183b_connectionCoordinate_contDiff.differentiable (by simp) 0
  have functionEquality :
      p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteFirstGermResponseActual direction =
        currentLinear ∘ connection := by
    funext point
    rw [c3h183b_scalarCurrent_normalForm direction point]
    exact (c3h183b_scalarCurrentLinear_apply direction (connection point)).symm
  rw [functionEquality]
  exact (currentLinear.hasFDerivAt.comp 0
    connectionDifferentiable.hasFDerivAt).differentiableAt

private theorem c3h183b_p286ConnectionEulerLagrange_sectorFunction
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction =
      (p286GaugeBFAlgebraicCoefficient
          positiveP506MatterCurrentCompleteFirstGermResponseActual direction -
        p286GaugeConnectionBFDifferentialMomentumDivergence
          positiveP506MatterCurrentCompleteFirstGermResponseActual direction) +
      p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteFirstGermResponseActual direction +
      p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction := by
  funext point
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance]
  unfold p286GaugeBFBalanceCoefficient
  rfl

/-- The complete P286 connection Euler--Lagrange coefficient of the same
generated actual is differentiable at the common contact.  This exposes the
analytic premise needed by failure-capable first-germ regressions. -/
theorem
    positiveP506MatterCurrentCompleteFirstGermResponseActual_p286ConnectionEulerLagrange_differentiableAt_origin
    (direction : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
      0 := by
  rw [c3h183b_p286ConnectionEulerLagrange_sectorFunction direction]
  exact (((c3h183b_bfAlgebraic_differentiableAt direction).sub
      (c3h183b_bfDivergence_differentiableAt direction)).add
    (c3h183b_scalarCurrent_differentiableAt direction)).add
      (c3h183b_matterCurrent_differentiableAt direction)

theorem fieldDirectionalDerivative_add_real_at_origin
    (first second : BasePoint → ℝ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (first + second) 0 direction =
      fieldDirectionalDerivative first 0 direction +
        fieldDirectionalDerivative second 0 direction := by
  change fieldDirectionalDerivative
      (fun point => first point + second point) 0 direction = _
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add firstDifferentiable secondDifferentiable]
  rfl

theorem fieldDirectionalDerivative_sub_real_at_origin
    (first second : BasePoint → ℝ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (first - second) 0 direction =
      fieldDirectionalDerivative first 0 direction -
        fieldDirectionalDerivative second 0 direction := by
  change fieldDirectionalDerivative
      (fun point => first point - second point) 0 direction = _
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_sub firstDifferentiable secondDifferentiable]
  rfl

/-- C3h183b: on the same exact-lineage actual `U****`, the complete P286
connection Euler--Lagrange dual has zero first germ along every canonical
spatial Cauchy axis and against every P286 one-form direction.  This is local
spatial-Cauchy closure only; it selects no current-support branch and claims
no global source-time evolution. -/
theorem
    positiveP506MatterCurrentCompleteFirstGermResponseActual_p286ConnectionEulerLagrange_spatialCauchyFirstGerm
    (axis : Fin 3) (direction : P286GaugeOneForm) :
    fieldDirectionalDerivative
        (p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
        0 axis.succ =
      0 := by
  let bfAlgebraic :=
    p286GaugeBFAlgebraicCoefficient
      positiveP506MatterCurrentCompleteFirstGermResponseActual direction
  let bfDivergence :=
    p286GaugeConnectionBFDifferentialMomentumDivergence
      positiveP506MatterCurrentCompleteFirstGermResponseActual direction
  let scalarCurrent :=
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermResponseActual direction
  let matterCurrent :=
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermResponseActual direction
  have bfAlgebraicDifferentiable : DifferentiableAt ℝ bfAlgebraic 0 :=
    c3h183b_bfAlgebraic_differentiableAt direction
  have bfDivergenceDifferentiable : DifferentiableAt ℝ bfDivergence 0 :=
    c3h183b_bfDivergence_differentiableAt direction
  have scalarCurrentDifferentiable : DifferentiableAt ℝ scalarCurrent 0 :=
    c3h183b_scalarCurrent_differentiableAt direction
  have matterCurrentDifferentiable : DifferentiableAt ℝ matterCurrent 0 :=
    c3h183b_matterCurrent_differentiableAt direction
  rw [c3h183b_p286ConnectionEulerLagrange_sectorFunction direction]
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
    c3h183b_bfAlgebraic_spatialFirstGerm axis direction,
    c3h183b_bfDivergence_spatialFirstGerm axis direction,
    c3h183b_scalarCurrent_spatialFirstGerm axis direction,
    c3h183b_matterCurrent_spatialFirstGerm axis direction]
  ring

/-- Audit authority for C3h183b.  It retains the complete C3h183a producer
ledger and adds exactly one new independent local spatial-Cauchy constraint.
It is not a new producer and does not assert temporal or full-spacetime
closure. -/
structure
    PositiveP506MatterCurrentCompleteFirstGermP286ConnectionSpatialCauchyClosureLaw :
    Prop where
  c3h183a : PositiveP506MatterCurrentCompleteFirstGermResponseLaw
  independentP286ConnectionSpatialCauchyFirstGerm :
    ∀ (axis : Fin 3) (direction : P286GaugeOneForm),
      fieldDirectionalDerivative
          (p286GaugeConnectionEulerLagrangeCoefficient
            positiveSmoothUnifiedSource
            positiveP506MatterCurrentCompleteFirstGermResponseActual direction)
          0 axis.succ =
        0

theorem
    positiveP506MatterCurrentCompleteFirstGermResponseActual_realizes_C3h183b :
    PositiveP506MatterCurrentCompleteFirstGermP286ConnectionSpatialCauchyClosureLaw := by
  exact
    { c3h183a :=
        positiveP506MatterCurrentCompleteFirstGermResponseActual_realizes_C3h183a
      independentP286ConnectionSpatialCauchyFirstGerm :=
        positiveP506MatterCurrentCompleteFirstGermResponseActual_p286ConnectionEulerLagrange_spatialCauchyFirstGerm }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterCompleteFirstGermP286ConnectionSpatialCauchyClosure
