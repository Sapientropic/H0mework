import H0mework.Physics.CartanAction.CartanAlgebraicSmoothness
import H0mework.Physics.JointVariation.TemporalDevelopmentOperator
import H0mework.Physics.Geometry.DynamicBreakingVacuum
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterNaturality

/-!
# Local regularity of the complete-joint matter temporal profile

The complete-joint writer recomputes its matter velocity after a Cartan
restart at every spacetime occurrence.  This module proves the corresponding
correction profile smooth at an arbitrary nondegenerate, noncharacteristic
contact of a smooth current.

The hypotheses describe only the supplied current at the contact.  No target
velocity, residual coordinate, derivative receipt, or branch choice enters
the producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanAffineConnectionActualization
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTorsionThreeFormEquiv
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeTwoFormPairing
open StageNineCoframeVariation
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeCartanAlgebraicSmoothness
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance completeJointMatterLocalP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance completeJointMatterLocalP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance completeJointMatterLocalP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private theorem coframe_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    ContDiff ℝ ∞ current.coframe := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  exact smooth.1 internal coordinate

private def coframeJetCarrier
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : IdentityECCoframeJetCarrier :=
  (current.coframe point,
    (holonomicCoframeFirstJetAt current.coframe point).derivative)

private theorem coframeJetCarrier_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    ContDiff ℝ ∞ (coframeJetCarrier current) := by
  refine (coframe_contDiff current smooth).prodMk ?_
  apply contDiff_pi'
  intro derivativeDirection
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  let component : BasePoint → ℝ := fun point =>
    current.coframe point internal coordinate
  have componentSmooth : ContDiff ℝ ∞ component :=
    contDiff_pi.mp (contDiff_pi.mp (coframe_contDiff current smooth) internal)
      coordinate
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry (fun _ : BasePoint => component)) :=
    componentSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ component point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  change ContDiff ℝ ∞
    (fun point =>
      fderiv ℝ component point
        (coordinateDirection derivativeDirection))
  exact derivativeSmooth.clm_apply contDiff_const

private theorem coframeJetCarrier_contDiffAt_of_local
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point) :
    ContDiffAt ℝ 0 (coframeJetCarrier current) point := by
  refine (coframeRegular.of_le (by norm_num)).prodMk ?_
  apply contDiffAt_pi'
  intro derivativeDirection
  apply contDiffAt_pi'
  intro internal
  apply contDiffAt_pi'
  intro coordinate
  let component : BasePoint → ℝ := fun candidate =>
    current.coframe candidate internal coordinate
  have componentRegular : ContDiffAt ℝ 1 component point :=
    contDiffAt_pi.mp (contDiffAt_pi.mp coframeRegular internal) coordinate
  have derivativeRegular : ContDiffAt ℝ 0
      (fun candidate => fderiv ℝ component candidate) point :=
    componentRegular.fderiv_right (m := 0) (by norm_num)
  change ContDiffAt ℝ 0
    (fun candidate =>
      fderiv ℝ component candidate
        (coordinateDirection derivativeDirection)) point
  exact derivativeRegular.clm_apply contDiffAt_const

private theorem coframeJetCarrier_contDiffAt_one_of_local
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point) :
    ContDiffAt ℝ 1 (coframeJetCarrier current) point := by
  refine (coframeRegular.of_le (by norm_num)).prodMk ?_
  apply contDiffAt_pi'
  intro derivativeDirection
  apply contDiffAt_pi'
  intro internal
  apply contDiffAt_pi'
  intro coordinate
  let component : BasePoint → ℝ := fun candidate =>
    current.coframe candidate internal coordinate
  have componentRegular : ContDiffAt ℝ 2 component point :=
    contDiffAt_pi.mp (contDiffAt_pi.mp coframeRegular internal) coordinate
  have derivativeRegular : ContDiffAt ℝ 1
      (fun candidate => fderiv ℝ component candidate) point :=
    componentRegular.fderiv_right (m := 1) (by norm_num)
  change ContDiffAt ℝ 1
    (fun candidate =>
      fderiv ℝ component candidate
        (coordinateDirection derivativeDirection)) point
  exact derivativeRegular.clm_apply contDiffAt_const

private theorem spinResponse_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponseAt source current) point := by
  have outer : ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponsePointCoframe source current)
      (point, current.coframe point) :=
    diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
      source current smooth point (current.coframe point) nondegenerate
  have inner : ContDiffAt ℝ ∞
      (fun candidate : BasePoint =>
        (candidate, current.coframe candidate)) point :=
    contDiffAt_id.prodMk (coframe_contDiff current smooth).contDiffAt
  have composed := outer.comp point inner
  rw [show
    diracDualFormNativeActionSpinResponseAt source current =
      fun candidate =>
        diracDualFormNativeActionSpinResponsePointCoframe source current
          (candidate, current.coframe candidate) by
    funext candidate
    exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
      source current candidate]
  exact composed

private theorem conjugateMatterBasis_contDiffAt_of_coordinates
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coordinatesRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (index : MatterCoordinateIndex) :
    ContDiffAt ℝ 0
      (fun target =>
        current.conjugateMatter target
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) point := by
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have projectionRegular : ContDiffAt ℝ 0
      (projection.restrictScalars ℝ)
      (holonomicConjugateMatterCoordinates current point) :=
    (projection.restrictScalars ℝ).contDiff.contDiffAt
  have coordinateRegular : ContDiffAt ℝ 0
      (fun target =>
        holonomicConjugateMatterCoordinates current target index) point :=
    projectionRegular.comp point coordinatesRegular
  change ContDiffAt ℝ 0 (fun target =>
    matterDualCoordinates (current.conjugateMatter target) index) point
  exact coordinateRegular

private theorem conjugateMatterBasis_contDiffAt_one_of_coordinates
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coordinatesRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point)
    (index : MatterCoordinateIndex) :
    ContDiffAt ℝ 1
      (fun target =>
        current.conjugateMatter target
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) point := by
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have projectionRegular : ContDiffAt ℝ 1
      (projection.restrictScalars ℝ)
      (holonomicConjugateMatterCoordinates current point) :=
    (projection.restrictScalars ℝ).contDiff.contDiffAt
  have coordinateRegular : ContDiffAt ℝ 1
      (fun target =>
        holonomicConjugateMatterCoordinates current target index) point :=
    projectionRegular.comp point coordinatesRegular
  change ContDiffAt ℝ 1 (fun target =>
    matterDualCoordinates (current.conjugateMatter target) index) point
  exact coordinateRegular

private theorem spinResponse_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (matterRegular : ContDiffAt ℝ 0
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point) :
    ContDiffAt ℝ 0
      (diracDualFormNativeActionSpinResponseAt source current) point := by
  have outer : ContDiffAt ℝ 0
      (diracDualFormNativeActionSpinResponsePointCoframe source current)
      (point, current.coframe point) :=
    diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt_of_local_order
      (by norm_num) source current point (current.coframe point) nondegenerate
      matterRegular
      (conjugateMatterBasis_contDiffAt_of_coordinates current point
        conjugateRegular)
  have inner : ContDiffAt ℝ 0
      (fun candidate : BasePoint =>
        (candidate, current.coframe candidate)) point :=
    contDiffAt_id.prodMk (coframeRegular.of_le (by norm_num))
  have composed := outer.comp point inner
  rw [show
    diracDualFormNativeActionSpinResponseAt source current =
      fun candidate =>
        diracDualFormNativeActionSpinResponsePointCoframe source current
          (candidate, current.coframe candidate) by
    funext candidate
    exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
      source current candidate]
  exact composed

private theorem spinResponse_contDiffAt_one_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point) :
    ContDiffAt ℝ 1
      (diracDualFormNativeActionSpinResponseAt source current) point := by
  have outer : ContDiffAt ℝ 1
      (diracDualFormNativeActionSpinResponsePointCoframe source current)
      (point, current.coframe point) :=
    diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt_of_local_order
      (by norm_num) source current point (current.coframe point) nondegenerate
      matterRegular
      (conjugateMatterBasis_contDiffAt_one_of_coordinates current point
        conjugateRegular)
  have inner : ContDiffAt ℝ 1
      (fun candidate : BasePoint =>
        (candidate, current.coframe candidate)) point :=
    contDiffAt_id.prodMk (coframeRegular.of_le (by norm_num))
  have composed := outer.comp point inner
  rw [show
    diracDualFormNativeActionSpinResponseAt source current =
      fun candidate =>
        diracDualFormNativeActionSpinResponsePointCoframe source current
          (candidate, current.coframe candidate) by
    funext candidate
    exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
      source current candidate]
  exact composed

private def coframeSpinResponseCarrier
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    LorentzianCoframe × PhysicalBivectorThreeForm :=
  (current.coframe point,
    diracDualFormNativeActionSpinResponseAt source current point)

private theorem coframeSpinResponseCarrier_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞ (coframeSpinResponseCarrier source current) point :=
  (coframe_contDiff current smooth).contDiffAt.prodMk
    (spinResponse_contDiffAt source current smooth point nondegenerate)

private theorem coframeSpinResponseCarrier_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (matterRegular : ContDiffAt ℝ 0
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point) :
    ContDiffAt ℝ 0 (coframeSpinResponseCarrier source current) point :=
  (coframeRegular.of_le (by norm_num)).prodMk
    (spinResponse_contDiffAt_of_local source current point nondegenerate
      coframeRegular matterRegular conjugateRegular)

private theorem coframeSpinResponseCarrier_contDiffAt_one_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point) :
    ContDiffAt ℝ 1 (coframeSpinResponseCarrier source current) point :=
  (coframeRegular.of_le (by norm_num)).prodMk
    (spinResponse_contDiffAt_one_of_local source current point nondegenerate
      coframeRegular matterRegular conjugateRegular)

private theorem cartanContorsion_component_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiffAt ℝ ∞
      (fun candidate : BasePoint =>
        diracDualFormNativeActionCartanContorsionAt source current candidate
          formDirection internalPair) point := by
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have outerAt : ContDiffAt ℝ ∞ outer
      (coframeSpinResponseCarrier source current point) :=
    cartanContorsionCoframeResponseComponent_contDiffAt
      (current.coframe point)
      (diracDualFormNativeActionSpinResponseAt source current point)
      nondegenerate formDirection internalPair
  rw [show
    (fun candidate : BasePoint =>
      diracDualFormNativeActionCartanContorsionAt source current candidate
        formDirection internalPair) =
      outer ∘ coframeSpinResponseCarrier source current by rfl]
  exact outerAt.comp point
    (coframeSpinResponseCarrier_contDiffAt source current smooth point
      nondegenerate)

private theorem cartanContorsion_component_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (matterRegular : ContDiffAt ℝ 0
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiffAt ℝ 0
      (fun candidate : BasePoint =>
        diracDualFormNativeActionCartanContorsionAt source current candidate
          formDirection internalPair) point := by
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have outerAt : ContDiffAt ℝ 0 outer
      (coframeSpinResponseCarrier source current point) :=
    (cartanContorsionCoframeResponseComponent_contDiffAt
      (current.coframe point)
      (diracDualFormNativeActionSpinResponseAt source current point)
      nondegenerate formDirection internalPair).of_le (by norm_num)
  rw [show
    (fun candidate : BasePoint =>
      diracDualFormNativeActionCartanContorsionAt source current candidate
        formDirection internalPair) =
      outer ∘ coframeSpinResponseCarrier source current by rfl]
  exact outerAt.comp point
    (coframeSpinResponseCarrier_contDiffAt_of_local source current point
      nondegenerate coframeRegular matterRegular conjugateRegular)

private theorem cartanContorsion_component_contDiffAt_one_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point)
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiffAt ℝ 1
      (fun candidate : BasePoint =>
        diracDualFormNativeActionCartanContorsionAt source current candidate
          formDirection internalPair) point := by
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have outerAt : ContDiffAt ℝ 1 outer
      (coframeSpinResponseCarrier source current point) :=
    (cartanContorsionCoframeResponseComponent_contDiffAt
      (current.coframe point)
      (diracDualFormNativeActionSpinResponseAt source current point)
      nondegenerate formDirection internalPair).of_le (by norm_num)
  rw [show
    (fun candidate : BasePoint =>
      diracDualFormNativeActionCartanContorsionAt source current candidate
        formDirection internalPair) =
      outer ∘ coframeSpinResponseCarrier source current by rfl]
  exact outerAt.comp point
    (coframeSpinResponseCarrier_contDiffAt_one_of_local source current point
      nondegenerate coframeRegular matterRegular conjugateRegular)

private theorem leviCivita_component_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun candidate : BasePoint =>
        (holonomicCoframeFirstJetAt current.coframe candidate)
          |>.lorentzSpinConnection
            formDirection internalOut internalIn) point := by
  let outer := identityECSpinConnectionComponentOfCarrier
    formDirection internalOut internalIn
  have outerAt : ContDiffAt ℝ ∞ outer (coframeJetCarrier current point) :=
    spinConnectionComponentOfCarrier_contDiffAt
      (current.coframe point)
      (holonomicCoframeFirstJetAt current.coframe point).derivative
      nondegenerate formDirection internalOut internalIn
  rw [show
    (fun candidate : BasePoint =>
      (holonomicCoframeFirstJetAt current.coframe candidate)
        |>.lorentzSpinConnection formDirection internalOut internalIn) =
      outer ∘ coframeJetCarrier current by rfl]
  exact outerAt.comp point (coframeJetCarrier_contDiff current smooth).contDiffAt

private theorem leviCivita_component_contDiffAt_of_local
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ 0
      (fun candidate : BasePoint =>
        (holonomicCoframeFirstJetAt current.coframe candidate)
          |>.lorentzSpinConnection
            formDirection internalOut internalIn) point := by
  let outer := identityECSpinConnectionComponentOfCarrier
    formDirection internalOut internalIn
  have outerAt : ContDiffAt ℝ 0 outer (coframeJetCarrier current point) :=
    (spinConnectionComponentOfCarrier_contDiffAt
      (current.coframe point)
      (holonomicCoframeFirstJetAt current.coframe point).derivative
      nondegenerate formDirection internalOut internalIn).of_le (by norm_num)
  rw [show
    (fun candidate : BasePoint =>
      (holonomicCoframeFirstJetAt current.coframe candidate)
        |>.lorentzSpinConnection formDirection internalOut internalIn) =
      outer ∘ coframeJetCarrier current by rfl]
  exact outerAt.comp point
    (coframeJetCarrier_contDiffAt_of_local current point coframeRegular)

private theorem leviCivita_component_contDiffAt_one_of_local
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ 1
      (fun candidate : BasePoint =>
        (holonomicCoframeFirstJetAt current.coframe candidate)
          |>.lorentzSpinConnection
            formDirection internalOut internalIn) point := by
  let outer := identityECSpinConnectionComponentOfCarrier
    formDirection internalOut internalIn
  have outerAt : ContDiffAt ℝ 1 outer (coframeJetCarrier current point) :=
    (spinConnectionComponentOfCarrier_contDiffAt
      (current.coframe point)
      (holonomicCoframeFirstJetAt current.coframe point).derivative
      nondegenerate formDirection internalOut internalIn).of_le (by norm_num)
  rw [show
    (fun candidate : BasePoint =>
      (holonomicCoframeFirstJetAt current.coframe candidate)
        |>.lorentzSpinConnection formDirection internalOut internalIn) =
      outer ∘ coframeJetCarrier current by rfl]
  exact outerAt.comp point
    (coframeJetCarrier_contDiffAt_one_of_local current point coframeRegular)

theorem cartanReactionRestart_connection_component_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun candidate : BasePoint =>
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current).gravityConnection candidate
          formDirection internalOut internalIn) point := by
  have levi := leviCivita_component_contDiffAt current smooth point
    nondegenerate formDirection internalOut internalIn
  have contorsionSum : ContDiffAt ℝ ∞
      (fun candidate : BasePoint =>
        ∑ internalPair : Fin 6,
          diracDualFormNativeActionCartanContorsionAt source current candidate
              formDirection internalPair *
            orientedLorentzBivectorBasisCoefficient internalPair
              internalOut internalIn) point := by
    apply ContDiffAt.sum
    intro internalPair _
    exact
      (cartanContorsion_component_contDiffAt source current smooth point
        nondegenerate formDirection internalPair).mul contDiffAt_const
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  unfold diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
  exact levi.add (contDiffAt_const.mul contorsionSum)

theorem cartanReactionRestart_connection_component_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (matterRegular : ContDiffAt ℝ 0
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ 0
      (fun candidate : BasePoint =>
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current).gravityConnection candidate
          formDirection internalOut internalIn) point := by
  have levi := leviCivita_component_contDiffAt_of_local current point
    nondegenerate coframeRegular formDirection internalOut internalIn
  have contorsionSum : ContDiffAt ℝ 0
      (fun candidate : BasePoint =>
        ∑ internalPair : Fin 6,
          diracDualFormNativeActionCartanContorsionAt source current candidate
              formDirection internalPair *
            orientedLorentzBivectorBasisCoefficient internalPair
              internalOut internalIn) point := by
    apply ContDiffAt.sum
    intro internalPair _
    exact
      (cartanContorsion_component_contDiffAt_of_local source current point
        nondegenerate coframeRegular matterRegular conjugateRegular
        formDirection internalPair).mul contDiffAt_const
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  unfold diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
  exact levi.add (contDiffAt_const.mul contorsionSum)

/-- A locally twice-smooth coframe and once-smooth matter pair produce a
once-smooth Cartan connection component.  This is the exact order needed to
read a continuous curvature profile without assuming global smoothness of
an arbitrary current. -/
theorem cartanReactionRestart_connection_component_contDiffAt_one_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 2 current.coframe point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates current) point)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ 1
      (fun candidate : BasePoint =>
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current).gravityConnection candidate
          formDirection internalOut internalIn) point := by
  have levi := leviCivita_component_contDiffAt_one_of_local current point
    nondegenerate coframeRegular formDirection internalOut internalIn
  have contorsionSum : ContDiffAt ℝ 1
      (fun candidate : BasePoint =>
        ∑ internalPair : Fin 6,
          diracDualFormNativeActionCartanContorsionAt source current candidate
              formDirection internalPair *
            orientedLorentzBivectorBasisCoefficient internalPair
              internalOut internalIn) point := by
    apply ContDiffAt.sum
    intro internalPair _
    exact
      (cartanContorsion_component_contDiffAt_one_of_local source current point
        nondegenerate coframeRegular matterRegular conjugateRegular
        formDirection internalPair).mul contDiffAt_const
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  unfold diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
  exact levi.add (contDiffAt_const.mul contorsionSum)

theorem cartanReactionRestart_matterCovariantDerivative_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (direction : LorentzianIndex) :
    ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (holonomicMatterCovariantDerivative
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) candidate direction)) point := by
  have derivativeSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      fieldDirectionalDerivative
        (fun target => matterCoordinateEquiv (current.matter target))
        candidate direction) point :=
    (holonomicMatterCoordinateDerivative_contDiff_local current smooth direction
      ).contDiffAt
  have matterSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv (current.matter candidate)) point :=
    smooth.2.2.2.2.2.2.2.1.contDiffAt
  have gaugeSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      p286CoordinateEquiv
        (current.gaugeConnection candidate direction)) point :=
    (smooth.2.2.2.2.1 direction).contDiffAt
  have spinMatrixSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      diracSpinConnectionLift
        ((sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current).gravityConnection candidate) direction) point := by
    apply contDiffAt_pi'
    intro row
    apply contDiffAt_pi'
    intro column
    unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply ContDiffAt.sum
    intro pair _
    have realCoefficientSmooth : ContDiffAt ℝ ∞ (fun candidate =>
        minkowskiInternalSign (lorentzBivectorFirst pair) *
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current).gravityConnection candidate direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair)) point :=
      contDiffAt_const.mul
        (cartanReactionRestart_connection_component_contDiffAt
          source current smooth point nondegenerate direction
          (lorentzBivectorFirst pair) (lorentzBivectorSecond pair))
    have complexCoefficientSmooth : ContDiffAt ℝ ∞ (fun candidate =>
        ((minkowskiInternalSign (lorentzBivectorFirst pair) *
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current).gravityConnection candidate direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair) : ℝ) : ℂ)) point :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp point realCoefficientSmooth
    exact (contDiffAt_const.mul complexCoefficientSmooth).mul contDiffAt_const
  have spinActionSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            ((sourceActionGeneratedDiracDualCartanReactionCurrentRestart
              source current).gravityConnection candidate) direction)
          (current.matter candidate))) point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point spinMatrixSmooth).clm_apply matterSmooth
    change ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            ((sourceActionGeneratedDiracDualCartanReactionCurrentRestart
              source current).gravityConnection candidate) direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (current.matter candidate))))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have gaugeActionSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (current.gaugeConnection candidate direction))
          (current.matter candidate))) point := by
    have actual :=
      (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point gaugeSmooth).clm_apply matterSmooth
    change ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (current.gaugeConnection candidate direction))))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (current.matter candidate))))) point at actual
    simpa only [p286CoordinateEquiv.symm_apply_apply,
      matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicMatterCovariantDerivative
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection]
  simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
  exact derivativeSmooth.add spinActionSmooth |>.add gaugeActionSmooth

private theorem
    cartanReactionRestart_matterCovariantDerivative_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0 (fun candidate =>
        p286CoordinateEquiv
          (current.gaugeConnection candidate direction)) point)
    (direction : LorentzianIndex) :
    ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (holonomicMatterCovariantDerivative
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) candidate direction)) point := by
  have derivativeRegular : ContDiffAt ℝ 0 (fun candidate =>
      fieldDirectionalDerivative
        (fun target => matterCoordinateEquiv (current.matter target))
        candidate direction) point := by
    unfold fieldDirectionalDerivative
    exact (matterRegular.fderiv_right (m := 0) (by norm_num)).clm_apply
      contDiffAt_const
  have matterContinuous : ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv (current.matter candidate)) point :=
    matterRegular.of_le (by norm_num)
  have spinMatrixRegular : ContDiffAt ℝ 0 (fun candidate =>
      diracSpinConnectionLift
        ((sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current).gravityConnection candidate) direction) point := by
    apply contDiffAt_pi'
    intro row
    apply contDiffAt_pi'
    intro column
    unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply ContDiffAt.sum
    intro pair _
    have realCoefficientRegular : ContDiffAt ℝ 0 (fun candidate =>
        minkowskiInternalSign (lorentzBivectorFirst pair) *
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current).gravityConnection candidate direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair)) point :=
      contDiffAt_const.mul
        (cartanReactionRestart_connection_component_contDiffAt_of_local
          source current point nondegenerate coframeRegular
          (matterRegular.of_le (by norm_num))
          conjugateRegular direction (lorentzBivectorFirst pair)
          (lorentzBivectorSecond pair))
    have complexCoefficientRegular : ContDiffAt ℝ 0 (fun candidate =>
        ((minkowskiInternalSign (lorentzBivectorFirst pair) *
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current).gravityConnection candidate direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair) : ℝ) : ℂ)) point :=
      by
        have outer : ContDiffAt ℝ 0 Complex.ofRealCLM
            (minkowskiInternalSign (lorentzBivectorFirst pair) *
              (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
                source current).gravityConnection point direction
                (lorentzBivectorFirst pair)
                (lorentzBivectorSecond pair)) :=
          Complex.ofRealCLM.contDiff.contDiffAt
        exact outer.comp point realCoefficientRegular
    exact (contDiffAt_const.mul complexCoefficientRegular).mul contDiffAt_const
  have spinActionRegular : ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            ((sourceActionGeneratedDiracDualCartanReactionCurrentRestart
              source current).gravityConnection candidate) direction)
          (current.matter candidate))) point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point spinMatrixRegular).clm_apply matterContinuous
    change ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            ((sourceActionGeneratedDiracDualCartanReactionCurrentRestart
              source current).gravityConnection candidate) direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (current.matter candidate))))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have gaugeActionRegular : ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (current.gaugeConnection candidate direction))
          (current.matter candidate))) point := by
    have actual :=
      (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point (gaugeRegular direction)).clm_apply
          matterContinuous
    change ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (current.gaugeConnection candidate direction))))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (current.matter candidate))))) point at actual
    simpa only [p286CoordinateEquiv.symm_apply_apply,
      matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicMatterCovariantDerivative
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection]
  simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
  exact derivativeRegular.add spinActionRegular |>.add gaugeActionRegular

private theorem cartanReactionRestart_knownVector_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (holonomicDiracDualCurrentCoframeMatterKnownVector
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) candidate)) point := by
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have coframeSmooth : ContDiffAt ℝ ∞
      (fun candidate => restarted.coframe candidate) point := by
    simpa [restarted] using (coframe_contDiff current smooth).contDiffAt
  have inverseGammaSmooth : ∀ direction : Fin 3,
      ContDiffAt ℝ ∞ (fun candidate =>
        inverseCoframeDiracGamma
          { coframe := restarted.coframe candidate, derivative := 0 }
          direction.succ) point := by
    intro direction
    exact
      (inverseCoframeDiracGamma_contDiffAt
        (current.coframe point) nondegenerate direction.succ).comp
          point coframeSmooth
  have kineticDirectionSmooth : ∀ direction : Fin 3,
      ContDiffAt ℝ ∞ (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              direction.succ)
            (holonomicMatterCovariantDerivative restarted candidate
              direction.succ))) point := by
    intro direction
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point (inverseGammaSmooth direction)).clm_apply
          (cartanReactionRestart_matterCovariantDerivative_contDiffAt
            source current smooth point nondegenerate direction.succ)
    change ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := restarted.coframe candidate, derivative := 0 }
            direction.succ)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (holonomicMatterCovariantDerivative restarted candidate
                direction.succ))))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have kineticSumSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      ∑ direction : Fin 3,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              direction.succ)
            (holonomicMatterCovariantDerivative restarted candidate
              direction.succ))) point :=
    ContDiffAt.sum fun direction _ => kineticDirectionSmooth direction
  have kineticSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      Complex.I •
        ∑ direction : Fin 3,
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := restarted.coframe candidate, derivative := 0 }
                direction.succ)
              (holonomicMatterCovariantDerivative restarted candidate
                direction.succ))) point :=
    (contDiffAt_const :
      ContDiffAt ℝ ∞ (fun _ : BasePoint => (Complex.I : ℂ)) point).smul
        kineticSumSmooth
  have scalarSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      restarted.scalar candidate) point := by
    simpa [restarted] using smooth.2.2.2.2.2.2.1.contDiffAt
  have matterSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv (restarted.matter candidate)) point := by
    simpa [restarted] using smooth.2.2.2.2.2.2.2.1.contDiffAt
  have yukawaSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (restarted.scalar candidate))
          (restarted.matter candidate))) point := by
    have actual :=
      (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point scalarSmooth).clm_apply matterSmooth
    change ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (restarted.scalar candidate))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (restarted.matter candidate))))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  simp only [map_add, map_smul, map_sum]
  exact kineticSmooth.add yukawaSmooth

private theorem cartanReactionRestart_knownVector_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (scalarRegular : ContDiffAt ℝ 0 current.scalar point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0 (fun candidate =>
        p286CoordinateEquiv
          (current.gaugeConnection candidate direction)) point) :
    ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (holonomicDiracDualCurrentCoframeMatterKnownVector
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) candidate)) point := by
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have coframeContinuous : ContDiffAt ℝ 0
      (fun candidate => restarted.coframe candidate) point := by
    simpa [restarted] using coframeRegular.of_le (by norm_num)
  have inverseGammaRegular : ∀ direction : Fin 3,
      ContDiffAt ℝ 0 (fun candidate =>
        inverseCoframeDiracGamma
          { coframe := restarted.coframe candidate, derivative := 0 }
          direction.succ) point := by
    intro direction
    exact
      ((inverseCoframeDiracGamma_contDiffAt
        (current.coframe point) nondegenerate direction.succ).of_le
          (by norm_num)).comp point coframeContinuous
  have kineticDirectionRegular : ∀ direction : Fin 3,
      ContDiffAt ℝ 0 (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              direction.succ)
            (holonomicMatterCovariantDerivative restarted candidate
              direction.succ))) point := by
    intro direction
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point (inverseGammaRegular direction)).clm_apply
          (cartanReactionRestart_matterCovariantDerivative_contDiffAt_of_local
            source current point nondegenerate coframeRegular matterRegular
            conjugateRegular gaugeRegular direction.succ)
    change ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := restarted.coframe candidate, derivative := 0 }
            direction.succ)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (holonomicMatterCovariantDerivative restarted candidate
                direction.succ))))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have kineticSumRegular : ContDiffAt ℝ 0 (fun candidate =>
      ∑ direction : Fin 3,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := restarted.coframe candidate, derivative := 0 }
              direction.succ)
            (holonomicMatterCovariantDerivative restarted candidate
              direction.succ))) point :=
    ContDiffAt.sum fun direction _ => kineticDirectionRegular direction
  have kineticRegular : ContDiffAt ℝ 0 (fun candidate =>
      Complex.I •
        ∑ direction : Fin 3,
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := restarted.coframe candidate, derivative := 0 }
                direction.succ)
              (holonomicMatterCovariantDerivative restarted candidate
                direction.succ))) point :=
    (contDiffAt_const :
      ContDiffAt ℝ 0 (fun _ : BasePoint => (Complex.I : ℂ)) point).smul
        kineticSumRegular
  have restartedScalarRegular : ContDiffAt ℝ 0 (fun candidate =>
      restarted.scalar candidate) point := by
    simpa [restarted] using scalarRegular
  have restartedMatterRegular : ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv (restarted.matter candidate)) point := by
    simpa [restarted] using matterRegular.of_le (by norm_num)
  have yukawaRegular : ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (restarted.scalar candidate))
          (restarted.matter candidate))) point := by
    have actual :=
      (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point restartedScalarRegular).clm_apply
          restartedMatterRegular
    change ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (restarted.scalar candidate))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (restarted.matter candidate))))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  simp only [map_add, map_smul, map_sum]
  exact kineticRegular.add yukawaRegular

private theorem temporalPrincipalScalar_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate =>
      coframeTemporalPrincipalScalar (current.coframe candidate)) point := by
  have inverseSmooth : ContDiffAt ℝ ∞
      (fun candidate => (current.coframe candidate)⁻¹) point :=
    (coframe_inv_contDiffAt (current.coframe point) nondegenerate).comp
      point (coframe_contDiff current smooth).contDiffAt
  unfold coframeTemporalPrincipalScalar
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro internal _
  have inverseEntrySmooth : ContDiffAt ℝ ∞ (fun candidate =>
      (current.coframe candidate)⁻¹
        (0 : LorentzianIndex) internal) point :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp inverseSmooth (0 : LorentzianIndex)) internal
  exact contDiffAt_const.mul (inverseEntrySmooth.pow 2)

private theorem temporalPrincipalScalar_contDiffAt_of_local
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point) :
    ContDiffAt ℝ 0 (fun candidate =>
      coframeTemporalPrincipalScalar (current.coframe candidate)) point := by
  have inverseRegular : ContDiffAt ℝ 0
      (fun candidate => (current.coframe candidate)⁻¹) point :=
    ((coframe_inv_contDiffAt (current.coframe point) nondegenerate).of_le
      (by norm_num)).comp point (coframeRegular.of_le (by norm_num))
  unfold coframeTemporalPrincipalScalar
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro internal _
  have inverseEntryRegular : ContDiffAt ℝ 0 (fun candidate =>
      (current.coframe candidate)⁻¹
        (0 : LorentzianIndex) internal) point :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp inverseRegular (0 : LorentzianIndex)) internal
  exact contDiffAt_const.mul (inverseEntryRegular.pow 2)

private theorem generatedTimeCovariantDerivative_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) candidate)) point := by
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have qComplexSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      ((coframeTemporalPrincipalScalar
        (current.coframe candidate) : ℝ) : ℂ)) point :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp point
      (temporalPrincipalScalar_contDiffAt current smooth point nondegenerate)
  have qComplexPoint : ((coframeTemporalPrincipalScalar
      (current.coframe point) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast noncharacteristic
  have qInverseSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      (((coframeTemporalPrincipalScalar
        (current.coframe candidate) : ℝ) : ℂ)⁻¹)) point :=
    qComplexSmooth.inv qComplexPoint
  have coframeSmooth : ContDiffAt ℝ ∞
      (fun candidate => restarted.coframe candidate) point := by
    simpa [restarted] using (coframe_contDiff current smooth).contDiffAt
  have gammaTimeSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      inverseCoframeDiracGamma
        { coframe := restarted.coframe candidate, derivative := 0 }
        (0 : LorentzianIndex)) point :=
    (inverseCoframeDiracGamma_contDiffAt
      (current.coframe point) nondegenerate (0 : LorentzianIndex)).comp
        point coframeSmooth
  have gammaKnownActionSmooth : ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := restarted.coframe candidate, derivative := 0 }
            (0 : LorentzianIndex))
          (holonomicDiracDualCurrentCoframeMatterKnownVector
            restarted candidate))) point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point gammaTimeSmooth).clm_apply
          (cartanReactionRestart_knownVector_contDiffAt
            source current smooth point nondegenerate)
    change ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := restarted.coframe candidate, derivative := 0 }
            (0 : LorentzianIndex))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (holonomicDiracDualCurrentCoframeMatterKnownVector
                restarted candidate))))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have iSmooth :
      ContDiffAt ℝ ∞ (fun _ : BasePoint => (Complex.I : ℂ)) point :=
    contDiffAt_const
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    actionGeneratedCurrentCoframeMatterTemporalDerivative
    currentCoframeMatterTemporalPrincipalInverse
    currentCoframeMatterTemporalPrincipal
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  simp only [LinearMap.smul_apply, map_neg, map_smul]
  exact (qInverseSmooth.smul (iSmooth.smul gammaKnownActionSmooth)).neg

private theorem generatedTimeCovariantDerivative_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (scalarRegular : ContDiffAt ℝ 0 current.scalar point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0 (fun candidate =>
        p286CoordinateEquiv
          (current.gaugeConnection candidate direction)) point) :
    ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) candidate)) point := by
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have qRealRegular := temporalPrincipalScalar_contDiffAt_of_local
    current point nondegenerate coframeRegular
  have qComplexRegular : ContDiffAt ℝ 0 (fun candidate =>
      ((coframeTemporalPrincipalScalar
        (current.coframe candidate) : ℝ) : ℂ)) point := by
    have outer : ContDiffAt ℝ 0 Complex.ofRealCLM
        (coframeTemporalPrincipalScalar (current.coframe point)) :=
      Complex.ofRealCLM.contDiff.contDiffAt
    exact outer.comp point qRealRegular
  have qComplexPoint : ((coframeTemporalPrincipalScalar
      (current.coframe point) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast noncharacteristic
  have qInverseRegular : ContDiffAt ℝ 0 (fun candidate =>
      (((coframeTemporalPrincipalScalar
        (current.coframe candidate) : ℝ) : ℂ)⁻¹)) point :=
    qComplexRegular.inv qComplexPoint
  have coframeContinuous : ContDiffAt ℝ 0
      (fun candidate => restarted.coframe candidate) point := by
    simpa [restarted] using coframeRegular.of_le (by norm_num)
  have gammaTimeRegular : ContDiffAt ℝ 0 (fun candidate =>
      inverseCoframeDiracGamma
        { coframe := restarted.coframe candidate, derivative := 0 }
        (0 : LorentzianIndex)) point :=
    ((inverseCoframeDiracGamma_contDiffAt
      (current.coframe point) nondegenerate (0 : LorentzianIndex)).of_le
        (by norm_num)).comp point coframeContinuous
  have gammaKnownActionRegular : ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := restarted.coframe candidate, derivative := 0 }
            (0 : LorentzianIndex))
          (holonomicDiracDualCurrentCoframeMatterKnownVector
            restarted candidate))) point := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point gammaTimeRegular).clm_apply
          (cartanReactionRestart_knownVector_contDiffAt_of_local
            source current point nondegenerate coframeRegular scalarRegular
            matterRegular conjugateRegular gaugeRegular)
    change ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := restarted.coframe candidate, derivative := 0 }
            (0 : LorentzianIndex))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (holonomicDiracDualCurrentCoframeMatterKnownVector
                restarted candidate))))) point at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have iRegular :
      ContDiffAt ℝ 0 (fun _ : BasePoint => (Complex.I : ℂ)) point :=
    contDiffAt_const
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    actionGeneratedCurrentCoframeMatterTemporalDerivative
    currentCoframeMatterTemporalPrincipalInverse
    currentCoframeMatterTemporalPrincipal
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  simp only [LinearMap.smul_apply, map_neg, map_smul]
  exact (qInverseRegular.smul (iRegular.smul gammaKnownActionRegular)).neg

private theorem matterConnectionAction_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (holonomicMatterConnectionAction
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) candidate canonicalLorentzianTimeDirection)) point := by
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  rw [show
    (fun candidate =>
      matterCoordinateEquiv
        (holonomicMatterConnectionAction restarted candidate
          canonicalLorentzianTimeDirection)) =
    fun candidate =>
      matterCoordinateEquiv
          (holonomicMatterCovariantDerivative restarted candidate
            canonicalLorentzianTimeDirection) -
        fieldDirectionalDerivative
          (fun target => matterCoordinateEquiv (current.matter target))
          candidate canonicalLorentzianTimeDirection by
    funext candidate
    unfold holonomicMatterConnectionAction holonomicMatterCovariantDerivative
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
    simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
    module]
  exact
    (cartanReactionRestart_matterCovariantDerivative_contDiffAt
      source current smooth point nondegenerate
      canonicalLorentzianTimeDirection).sub
    (holonomicMatterCoordinateDerivative_contDiff_local current smooth
      canonicalLorentzianTimeDirection).contDiffAt

private theorem matterConnectionAction_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0 (fun candidate =>
        p286CoordinateEquiv
          (current.gaugeConnection candidate direction)) point) :
    ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (holonomicMatterConnectionAction
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) candidate canonicalLorentzianTimeDirection)) point := by
  let restarted :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  rw [show
    (fun candidate =>
      matterCoordinateEquiv
        (holonomicMatterConnectionAction restarted candidate
          canonicalLorentzianTimeDirection)) =
    fun candidate =>
      matterCoordinateEquiv
          (holonomicMatterCovariantDerivative restarted candidate
            canonicalLorentzianTimeDirection) -
        fieldDirectionalDerivative
          (fun target => matterCoordinateEquiv (current.matter target))
          candidate canonicalLorentzianTimeDirection by
    funext candidate
    unfold holonomicMatterConnectionAction holonomicMatterCovariantDerivative
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
    simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
    module]
  have derivativeRegular : ContDiffAt ℝ 0 (fun candidate =>
      fieldDirectionalDerivative
        (fun target => matterCoordinateEquiv (current.matter target))
        candidate canonicalLorentzianTimeDirection) point := by
    unfold fieldDirectionalDerivative
    exact (matterRegular.fderiv_right (m := 0) (by norm_num)).clm_apply
      contDiffAt_const
  exact
    (cartanReactionRestart_matterCovariantDerivative_contDiffAt_of_local
      source current point nondegenerate coframeRegular matterRegular
      conjugateRegular gaugeRegular canonicalLorentzianTimeDirection).sub
    derivativeRegular

theorem cartanReactionRestart_rawTimeVelocity_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate =>
      matterCoordinateEquiv
        (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) candidate)) point := by
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
  simp only [map_sub]
  exact
    (generatedTimeCovariantDerivative_contDiffAt source current smooth point
      nondegenerate noncharacteristic).sub
    (matterConnectionAction_contDiffAt source current smooth point
      nondegenerate)

theorem
    cartanReactionRestart_rawTimeVelocity_coordinate_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (scalarRegular : ContDiffAt ℝ 0 current.scalar point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0 (fun candidate =>
        p286CoordinateEquiv
          (current.gaugeConnection candidate direction)) point) :
    ContDiffAt ℝ 0 (fun candidate =>
      matterCoordinateEquiv
        (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current) candidate)) point := by
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
  simp only [map_sub]
  exact
    (generatedTimeCovariantDerivative_contDiffAt_of_local source current point
      nondegenerate noncharacteristic coframeRegular scalarRegular
      matterRegular conjugateRegular gaugeRegular).sub
    (matterConnectionAction_contDiffAt_of_local source current point
      nondegenerate coframeRegular matterRegular conjugateRegular gaugeRegular)

private theorem recenteredCurrent_coframeFirstJet_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicCoframeFirstJetAt
        (fullyRecenterHolonomicConfiguration current contact).coframe 0 =
      holonomicCoframeFirstJetAt current.coframe contact := by
  apply coframeJet_eq_of_fields_eq
  · exact fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · funext derivativeDirection internal coordinate
    change
      fieldDirectionalDerivative
          ((fun point => current.coframe point internal coordinate) ∘
            canonicalSpacetimeContactTranslation contact)
          0 derivativeDirection =
        fieldDirectionalDerivative
          (fun point => current.coframe point internal coordinate)
          contact derivativeDirection
    simpa [canonicalSpacetimeContactTranslation] using
      fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
        (fun point => current.coframe point internal coordinate)
        contact 0 derivativeDirection

private theorem recenteredCurrent_spinResponse_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    diracDualFormNativeActionSpinResponseAt source
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      diracDualFormNativeActionSpinResponseAt source current contact := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
  · exact fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · exact fullyRecenterHolonomicConfiguration_matter_origin _ _
  · exact fullyRecenterHolonomicConfiguration_conjugateMatter_origin _ _

private theorem recenteredCurrent_actionCartanConnection_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    diracDualFormNativeActionCartanConnectionAt source
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      diracDualFormNativeActionCartanConnectionAt source current contact := by
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [recenteredCurrent_coframeFirstJet_origin,
    fullyRecenterHolonomicConfiguration_coframe_origin,
    recenteredCurrent_spinResponse_origin]

private theorem restart_connection_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (completeJointGeneratedProfileRestartCurrent source current contact
      ).gravityConnection 0 =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
        ).gravityConnection contact := by
  change
    diracDualFormNativeActionCartanConnectionAt source
        (fullyRecenterHolonomicConfiguration current contact) 0 =
      diracDualFormNativeActionCartanConnectionAt source current contact
  exact recenteredCurrent_actionCartanConnection_origin source current contact

private theorem restart_matterCovariantDerivative_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicMatterCovariantDerivative
        (completeJointGeneratedProfileRestartCurrent source current contact) 0 =
      holonomicMatterCovariantDerivative
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current)
        contact := by
  funext direction
  unfold completeJointGeneratedProfileRestartCurrent
  unfold holonomicMatterCovariantDerivative
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection]
  change
    matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            ((fun point => matterCoordinateEquiv (current.matter point)) ∘
              canonicalSpacetimeContactTranslation contact)
            0 direction) +
        diracMatrixMatterAction
            (diracSpinConnectionLift
              ((completeJointGeneratedProfileRestartCurrent
                source current contact).gravityConnection 0) direction)
          (current.matter (canonicalSpacetimeContactTranslation contact 0)) +
      diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (current.gaugeConnection
              (canonicalSpacetimeContactTranslation contact 0) direction))
        (current.matter (canonicalSpacetimeContactTranslation contact 0)) =
      matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun point => matterCoordinateEquiv (current.matter point))
            contact direction) +
        diracMatrixMatterAction
            (diracSpinConnectionLift
              ((sourceActionGeneratedDiracDualCartanReactionCurrentRestart
                source current).gravityConnection contact) direction)
          (current.matter contact) +
      diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (current.gaugeConnection contact direction))
        (current.matter contact)
  rw [fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation,
    restart_connection_origin]
  simp [canonicalSpacetimeContactTranslation]

private theorem restart_rawTimeVelocity_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (completeJointGeneratedProfileRestartCurrent source current contact) 0 =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current)
        contact := by
  unfold completeJointGeneratedProfileRestartCurrent
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    holonomicDiracDualCurrentCoframeMatterKnownVector
    holonomicMatterConnectionAction
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection]
  simp only [fullyRecenterHolonomicConfiguration_coframe_origin,
    fullyRecenterHolonomicConfiguration_scalar_origin,
    fullyRecenterHolonomicConfiguration_matter_origin,
    fullyRecenterHolonomicConfiguration_gaugeConnection_origin]
  have covariantDerivativeEq :=
    restart_matterCovariantDerivative_origin source current contact
  unfold completeJointGeneratedProfileRestartCurrent at covariantDerivativeEq
  rw [recenteredCurrent_actionCartanConnection_origin,
    covariantDerivativeEq]

/-- Exact action-data normal form of the complete-joint matter correction.
The contact recenter is eliminated in favor of the same current's Cartan
restart at that contact. -/
theorem completeJointMatterTemporalCoordinateCorrection_normalForm
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    completeJointMatterTemporalCoordinateCorrection source current contact =
      matterCoordinateEquiv
          (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
            (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
              source current) contact) -
        fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (current.matter point))
          contact canonicalLorentzianTimeDirection := by
  unfold completeJointMatterTemporalCoordinateCorrection
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity,
    restart_rawTimeVelocity_origin]

/-- Arbitrary-contact local regularity of the action-generated primal
temporal correction. -/
theorem completeJointMatterTemporalCoordinateCorrection_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞
      (completeJointMatterTemporalCoordinateCorrection source current) point := by
  rw [show
    completeJointMatterTemporalCoordinateCorrection source current =
      fun contact =>
        matterCoordinateEquiv
            (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
              (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
                source current) contact) -
          fieldDirectionalDerivative
            (fun target => matterCoordinateEquiv (current.matter target))
            contact canonicalLorentzianTimeDirection by
    funext contact
    exact completeJointMatterTemporalCoordinateCorrection_normalForm
      source current contact]
  exact
    (cartanReactionRestart_rawTimeVelocity_coordinate_contDiffAt
      source current smooth point nondegenerate noncharacteristic).sub
    (holonomicMatterCoordinateDerivative_contDiff_local current smooth
      canonicalLorentzianTimeDirection).contDiffAt

/-- Minimal local regularity mouth for the complete-joint matter correction.
It consumes exactly the primitive first/value jets read by the Cartan restart
and the temporal principal inverse; no global `Smooth` receipt, residual,
target velocity, or branch choice is supplied. -/
theorem completeJointMatterTemporalCoordinateCorrection_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 1 current.coframe point)
    (scalarRegular : ContDiffAt ℝ 0 current.scalar point)
    (matterRegular : ContDiffAt ℝ 1
      (fun target => matterCoordinateEquiv (current.matter target)) point)
    (conjugateRegular : ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0 (fun candidate =>
        p286CoordinateEquiv
          (current.gaugeConnection candidate direction)) point) :
    ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection source current) point := by
  rw [show
    completeJointMatterTemporalCoordinateCorrection source current =
      fun contact =>
        matterCoordinateEquiv
            (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
              (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
                source current) contact) -
          fieldDirectionalDerivative
            (fun target => matterCoordinateEquiv (current.matter target))
            contact canonicalLorentzianTimeDirection by
    funext contact
    exact completeJointMatterTemporalCoordinateCorrection_normalForm
      source current contact]
  have derivativeRegular : ContDiffAt ℝ 0 (fun candidate =>
      fieldDirectionalDerivative
        (fun target => matterCoordinateEquiv (current.matter target))
        candidate canonicalLorentzianTimeDirection) point := by
    unfold fieldDirectionalDerivative
    exact (matterRegular.fderiv_right (m := 0) (by norm_num)).clm_apply
      contDiffAt_const
  exact
    (cartanReactionRestart_rawTimeVelocity_coordinate_contDiffAt_of_local
      source current point nondegenerate noncharacteristic coframeRegular
      scalarRegular matterRegular conjugateRegular gaugeRegular).sub
    derivativeRegular

/-! ## Local first-jet realization of the generated temporal field -/

/-- The canonical temporal primitive installs the action-generated matter
correction in the ambient first jet at the local origin.  Regularity is an
acceptance hypothesis for differentiating the already generated primitive;
it is not an input to the writer. -/
theorem
    completeJointTemporalMatterCoordinates_hasFDerivAt_zero_of_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (correctionRegular : ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection source current) 0) :
    HasFDerivAt
      (fun point =>
        matterCoordinateEquiv
          ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            source current).matter point))
      ((fderiv ℝ
          (fun point => matterCoordinateEquiv (current.matter point)) 0) +
        canonicalTimeProjection.smulRight
          (completeJointMatterTemporalCoordinateCorrection source current 0))
      0 := by
  have currentDerivative := currentDifferentiable.hasFDerivAt
  have primitiveDerivative :=
    canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt_zero
      (completeJointMatterTemporalCoordinateCorrection source current)
      correctionRegular
  have totalDerivative := currentDerivative.add primitiveDerivative
  have functionEquality :
      (fun point =>
        matterCoordinateEquiv
          ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            source current).matter point)) =
        (fun point => matterCoordinateEquiv (current.matter point)) +
          canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection source current) := by
    funext point
    change
      matterCoordinateEquiv
          (current.matter point +
            matterCoordinateEquiv.symm
              (canonicalTimePrimitive
                (completeJointMatterTemporalCoordinateCorrection source current)
                point)) = _
    rw [map_add, matterCoordinateEquiv.apply_symm_apply]
    rfl
  rw [functionEquality]
  exact totalDerivative

/-- At the local origin, the generated temporal field carries exactly the
total action velocity selected from the same source/current profile. -/
theorem completeJointGlobalTemporalCurrent_matterTimeDerivative_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (correctionRegular : ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection source current) 0) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            source current).matter point))
        0 canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        (sourceActionGeneratedDiracDualCompleteJointProfiles
          source current 0).matterVelocity := by
  unfold fieldDirectionalDerivative
  rw [
    (completeJointTemporalMatterCoordinates_hasFDerivAt_zero_of_contDiffAt
      source current currentDifferentiable correctionRegular).fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]
  have timeProjection :
      canonicalTimeProjection
          (coordinateDirection canonicalLorentzianTimeDirection) =
        1 := by
    simp [canonicalTimeProjection, canonicalLorentzianTimeDirection,
      coordinateDirection, localBaseCoordinate_apply]
  rw [timeProjection, one_smul]
  unfold completeJointMatterTemporalCoordinateCorrection
  unfold fieldDirectionalDerivative
  module

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
