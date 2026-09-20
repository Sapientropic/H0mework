import H0mework.Physics.MatterCurrent.CanonicalLorentzAdjointDiagonalActual

/-!
# C3h197: adjoint temporal first-germ coordinate support

This module supplies the finite-coordinate identities needed to evaluate the
adjoint Dirac--Yukawa temporal first germ on the C3h196 actual.  It only exposes
representation-faithful readouts of the existing action and fields; it neither
constructs a repair jet nor treats an Euler--Lagrange readback as an independent
Cauchy constraint.

The coordinate case tree remains together because its identities share one
Dirac/P286 basis normalization and are consumed as one mechanism by the
structural and stress modules below.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCoframeScalarMatterRegularity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineConnectionSectorSourceBalance
open StageNineP286GaugeConnectionActionVariation
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionLine
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzTangentSimplicity
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance su7MotherIndexLinearOrder : LinearOrder SU7MotherIndex :=
  SU7ExteriorMatterRestriction.instLinearOrderSU7MotherIndex

def holonomicConjugateMatterCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterDualCoordinates (configuration.conjugateMatter point)

theorem holonomicConjugateMatterCoordinates_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates configuration) := by
  let assemble : (MatterCoordinateIndex → ℂ) →L[ℝ]
      MatterCoordinateCarrier :=
    (EuclideanSpace.equiv MatterCoordinateIndex ℂ).symm.toContinuousLinearMap
      |>.restrictScalars ℝ
  have coordinateSmooth : ContDiff ℝ ∞ (fun point index =>
      configuration.conjugateMatter point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) := by
    apply contDiff_pi'
    intro index
    exact smooth.2.2.2.2.2.2.2.2 index
  have assembled := assemble.contDiff.comp coordinateSmooth
  rw [show holonomicConjugateMatterCoordinates configuration =
      fun point =>
        (EuclideanSpace.equiv MatterCoordinateIndex ℂ).symm
          (fun index =>
            configuration.conjugateMatter point
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ)))) by
    funext point
    apply PiLp.ext
    intro index
    rfl]
  exact assembled

def holonomicConjugateMatterDerivativeCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) :
    MatterCoordinateCarrier :=
  fieldDirectionalDerivative
    (holonomicConjugateMatterCoordinates configuration) point direction

theorem holonomicConjugateMatterDerivativeCoordinates_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ (fun point =>
      holonomicConjugateMatterDerivativeCoordinates configuration point
        direction) := by
  have derivativeSmooth : ContDiff ℝ ∞
      (fderiv ℝ (holonomicConjugateMatterCoordinates configuration)) :=
    (holonomicConjugateMatterCoordinates_contDiff configuration smooth).fderiv_right
      (m := ∞) (by simp)
  simpa [holonomicConjugateMatterDerivativeCoordinates,
    fieldDirectionalDerivative] using
    derivativeSmooth.clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint =>
        coordinateDirection direction))

def holonomicConjugateMatterDerivativeDual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  matterDualOfCoordinates
    (holonomicConjugateMatterDerivativeCoordinates configuration point
      direction)

def holonomicIdentityCoframeMatterConnectionOperator
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
      (diracSpinConnectionLift
        (configuration.gravityConnection point) direction) +
    diracExteriorMotherLieAction
      (p286LieBlockEmbed (configuration.gaugeConnection point direction))

def holonomicIdentityCoframeMatterAlgebraicOperator
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I •
      ∑ direction : LorentzianIndex,
        (diracMatrixMatterAction (diracGamma direction)).comp
          (holonomicIdentityCoframeMatterConnectionOperator configuration
            point direction) +
    chiralExteriorYukawaAction
      (scalarCoordinateEquiv.symm (configuration.scalar point))

def holonomicIdentityCoframeConjugateMatterSpatialTransport
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  ∑ direction : Fin 3,
    (holonomicConjugateMatterDerivativeDual configuration point
      direction.succ).comp
      (identityCoframeMatterPrincipal direction.succ)

def holonomicIdentityCoframeConjugateMatterKnownDual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (configuration.conjugateMatter point).comp
      (holonomicIdentityCoframeMatterAlgebraicOperator configuration point) -
    holonomicIdentityCoframeConjugateMatterSpatialTransport configuration point

def holonomicIdentityCoframeConjugateMatterActionVelocity
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (holonomicIdentityCoframeConjugateMatterKnownDual configuration point).comp
    (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection)

def HolonomicIdentityCoframeConjugateMatterTimeActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeDerivative : Module.Dual ℂ DiracExteriorMatterCarrier) : Prop :=
  timeDerivative.comp
        (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection) +
      holonomicIdentityCoframeConjugateMatterSpatialTransport configuration point =
    (configuration.conjugateMatter point).comp
      (holonomicIdentityCoframeMatterAlgebraicOperator configuration point)

theorem holonomicIdentityCoframeConjugateMatterActionVelocity_satisfies
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw configuration point
      (holonomicIdentityCoframeConjugateMatterActionVelocity configuration
        point) := by
  apply LinearMap.ext
  intro matter
  simp only [holonomicIdentityCoframeConjugateMatterActionVelocity,
    holonomicIdentityCoframeConjugateMatterKnownDual,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [identityCoframeMatterPrincipal_time_involutive]
  abel

theorem holonomicIdentityCoframeConjugateMatterTimeActionLaw_unique
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (first second : Module.Dual ℂ DiracExteriorMatterCarrier)
    (firstLaw :
      HolonomicIdentityCoframeConjugateMatterTimeActionLaw configuration point
        first)
    (secondLaw :
      HolonomicIdentityCoframeConjugateMatterTimeActionLaw configuration point
        second) :
    first = second := by
  have composedEqual :
      first.comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) =
        second.comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) := by
    apply LinearMap.ext
    intro matter
    have firstAt := LinearMap.congr_fun firstLaw matter
    have secondAt := LinearMap.congr_fun secondLaw matter
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at firstAt secondAt
    exact add_right_cancel (firstAt.trans secondAt.symm)
  apply LinearMap.ext
  intro matter
  calc
    first matter =
        first
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection matter)) := by
      rw [identityCoframeMatterPrincipal_time_involutive]
    _ =
        second
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection matter)) := by
      exact LinearMap.congr_fun composedEqual
        (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection matter)
    _ = second matter := by
      rw [identityCoframeMatterPrincipal_time_involutive]

/-- At identity coframe the adjoint Dirac equation is a genuine evolution
law: the involutive time principal symbol selects one and only one temporal
derivative.  In particular it contributes no separate Cauchy constraint. -/
theorem holonomicIdentityCoframeConjugateMatterTimeActionLaw_iff
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (candidate : Module.Dual ℂ DiracExteriorMatterCarrier) :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw configuration point
          candidate ↔
      candidate =
        holonomicIdentityCoframeConjugateMatterActionVelocity configuration
          point := by
  constructor
  · intro candidateLaw
    exact holonomicIdentityCoframeConjugateMatterTimeActionLaw_unique
      configuration point candidate
        (holonomicIdentityCoframeConjugateMatterActionVelocity configuration
          point)
      candidateLaw
      (holonomicIdentityCoframeConjugateMatterActionVelocity_satisfies
        configuration point)
  · rintro rfl
    exact holonomicIdentityCoframeConjugateMatterActionVelocity_satisfies
      configuration point

theorem holonomicIdentityCoframeConjugateMatterActionVelocity_eq_zero_iff
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicIdentityCoframeConjugateMatterActionVelocity configuration point =
          0 ↔
      holonomicIdentityCoframeConjugateMatterKnownDual configuration point =
        0 := by
  constructor
  · intro velocityZero
    apply LinearMap.ext
    intro matter
    have atPrincipal := LinearMap.congr_fun velocityZero
      (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection matter)
    change
      holonomicIdentityCoframeConjugateMatterKnownDual configuration point
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
              matter)) =
        0 at atPrincipal
    rw [identityCoframeMatterPrincipal_time_involutive] at atPrincipal
    exact atPrincipal
  · rintro knownZero
    rw [holonomicIdentityCoframeConjugateMatterActionVelocity, knownZero]
    rfl

/-! ## Joint spacetime regularity of the full-dependency response -/

private theorem holonomicDiracSpinConnectionLift_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ (fun point =>
      diracSpinConnectionLift
        (configuration.gravityConnection point) direction) := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiff.sum
  intro pair _
  have realCoefficientSmooth : ContDiff ℝ ∞ (fun point =>
      minkowskiInternalSign (lorentzBivectorFirst pair) *
        configuration.gravityConnection point direction
          (lorentzBivectorFirst pair)
          (lorentzBivectorSecond pair)) :=
    contDiff_const.mul
      (smooth.2.1 direction (lorentzBivectorFirst pair)
        (lorentzBivectorSecond pair))
  have complexCoefficientSmooth : ContDiff ℝ ∞ (fun point =>
      ((minkowskiInternalSign (lorentzBivectorFirst pair) *
        configuration.gravityConnection point direction
          (lorentzBivectorFirst pair)
          (lorentzBivectorSecond pair) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp realCoefficientSmooth
  exact (contDiff_const.mul complexCoefficientSmooth).mul contDiff_const

theorem holonomicIdentityCoframeMatterAlgebraicOperator_coordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (holonomicIdentityCoframeMatterAlgebraicOperator configuration point
          matter)) := by
  have matterCoordinatesConstant : ContDiff ℝ ∞
      (fun _ : BasePoint => matterCoordinateEquiv matter) :=
    contDiff_const
  have connectionSummandSmooth : ∀ direction : LorentzianIndex,
      ContDiff ℝ ∞ (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma direction)
            (holonomicIdentityCoframeMatterConnectionOperator configuration
              point direction matter))) := by
    intro direction
    have spinActionSmooth : ContDiff ℝ ∞ (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (configuration.gravityConnection point) direction)
            matter)) := by
      have actual :=
        (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
          (holonomicDiracSpinConnectionLift_contDiff configuration smooth
            direction)).clm_apply matterCoordinatesConstant
      change ContDiff ℝ ∞ (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (configuration.gravityConnection point) direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv matter)))) at actual
      simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
    have gaugeActionSmooth : ContDiff ℝ ∞ (fun point =>
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (configuration.gaugeConnection point direction)) matter)) := by
      have actual :=
        (StageNineCoframeScalarMatterRegularity.matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff.comp
          (smooth.2.2.2.2.1 direction)).clm_apply matterCoordinatesConstant
      change ContDiff ℝ ∞ (fun point =>
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                (p286CoordinateEquiv
                  (configuration.gaugeConnection point direction))))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv matter)))) at actual
      simpa only [p286CoordinateEquiv.symm_apply_apply,
        matterCoordinateEquiv.symm_apply_apply] using actual
    have innerSmooth : ContDiff ℝ ∞ (fun point =>
        matterCoordinateEquiv
          (holonomicIdentityCoframeMatterConnectionOperator configuration
            point direction matter)) := by
      unfold holonomicIdentityCoframeMatterConnectionOperator
      simpa only [LinearMap.add_apply, map_add] using
        spinActionSmooth.add gaugeActionSmooth
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : BasePoint => diracGamma direction))).clm_apply innerSmooth
    change ContDiff ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction (diracGamma direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (holonomicIdentityCoframeMatterConnectionOperator configuration
                point direction matter))))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have connectionSumSmooth : ContDiff ℝ ∞ (fun point =>
      ∑ direction : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma direction)
            (holonomicIdentityCoframeMatterConnectionOperator configuration
              point direction matter))) := by
    apply ContDiff.sum
    intro direction _
    exact connectionSummandSmooth direction
  have phasedConnectionSmooth : ContDiff ℝ ∞ (fun point =>
      Complex.I •
        ∑ direction : LorentzianIndex,
          matterCoordinateEquiv
            (diracMatrixMatterAction (diracGamma direction)
              (holonomicIdentityCoframeMatterConnectionOperator configuration
                point direction matter))) :=
    (contDiff_const : ContDiff ℝ ∞
      (fun _ : BasePoint => Complex.I)).smul connectionSumSmooth
  have yukawaSmooth : ContDiff ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point)) matter)) := by
    have actual :=
      (chiralExteriorYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        smooth.2.2.2.2.2.2.1).clm_apply matterCoordinatesConstant
    change ContDiff ℝ ∞ (fun point =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv matter)))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicIdentityCoframeMatterAlgebraicOperator
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, map_add, map_smul, map_sum]
  exact phasedConnectionSmooth.add yukawaSmooth

private theorem varyingConjugateMatterDual_apply_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (vector : BasePoint → DiracExteriorMatterCarrier)
    (vectorSmooth : ContDiff ℝ ∞ (fun point =>
      matterCoordinateEquiv (vector point))) :
    ContDiff ℝ ∞ (fun point =>
      configuration.conjugateMatter point (vector point)) := by
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
  apply ContDiff.sum
  intro index _
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have vectorCoordinateSmooth : ContDiff ℝ ∞ (fun point =>
      matterCoordinateEquiv (vector point) index) :=
    (projection.restrictScalars ℝ).contDiff.comp vectorSmooth
  exact vectorCoordinateSmooth.mul
    (smooth.2.2.2.2.2.2.2.2 index)

private theorem holonomicConjugateMatterDerivativeDual_apply_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun point =>
      holonomicConjugateMatterDerivativeDual configuration point direction
        matter) := by
  rw [show (fun point =>
      holonomicConjugateMatterDerivativeDual configuration point direction
        matter) =
    fun point => ∑ index : MatterCoordinateIndex,
      matterCoordinateEquiv matter index *
        holonomicConjugateMatterDerivativeCoordinates configuration point
          direction index by
    funext point
    exact matterDualOfCoordinates_apply _ _]
  apply ContDiff.sum
  intro index _
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have derivativeCoordinateSmooth : ContDiff ℝ ∞ (fun point =>
      holonomicConjugateMatterDerivativeCoordinates configuration point
        direction index) :=
    (projection.restrictScalars ℝ).contDiff.comp
      (holonomicConjugateMatterDerivativeCoordinates_contDiff configuration
        smooth direction)
  exact contDiff_const.mul derivativeCoordinateSmooth

theorem holonomicIdentityCoframeConjugateMatterKnownDual_apply_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun point =>
      holonomicIdentityCoframeConjugateMatterKnownDual configuration point
        matter) := by
  have algebraicPairingSmooth : ContDiff ℝ ∞ (fun point =>
      configuration.conjugateMatter point
        (holonomicIdentityCoframeMatterAlgebraicOperator configuration point
          matter)) :=
    varyingConjugateMatterDual_apply_contDiff configuration smooth _
      (holonomicIdentityCoframeMatterAlgebraicOperator_coordinate_contDiff
        configuration smooth matter)
  have spatialTransportSmooth : ContDiff ℝ ∞ (fun point =>
      holonomicIdentityCoframeConjugateMatterSpatialTransport configuration
        point matter) := by
    unfold holonomicIdentityCoframeConjugateMatterSpatialTransport
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    apply ContDiff.sum
    intro direction _
    exact holonomicConjugateMatterDerivativeDual_apply_contDiff configuration
      smooth direction.succ
      (identityCoframeMatterPrincipal direction.succ matter)
  unfold holonomicIdentityCoframeConjugateMatterKnownDual
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  exact algebraicPairingSmooth.sub spatialTransportSmooth

theorem holonomicIdentityCoframeConjugateMatterActionVelocity_apply_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun point =>
      holonomicIdentityCoframeConjugateMatterActionVelocity configuration point
        matter) := by
  unfold holonomicIdentityCoframeConjugateMatterActionVelocity
  simp only [LinearMap.comp_apply]
  exact holonomicIdentityCoframeConjugateMatterKnownDual_apply_contDiff
    configuration smooth
    (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection matter)

/-! ## Exact identity-coframe Euler--Lagrange readout -/

def matterDualCoordinateEvaluation
    (matter : DiracExteriorMatterCarrier) :
    MatterCoordinateCarrier →L[ℂ] ℂ :=
  ∑ index : MatterCoordinateIndex,
    (matterCoordinateEquiv matter index) •
      ((ContinuousLinearMap.proj index).comp
        (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap)

@[simp] theorem matterDualCoordinateEvaluation_apply
    (matter : DiracExteriorMatterCarrier)
    (coordinates : MatterCoordinateCarrier) :
    matterDualCoordinateEvaluation matter coordinates =
      matterDualOfCoordinates coordinates matter := by
  simp [matterDualCoordinateEvaluation, matterDualOfCoordinates_apply]

theorem holonomicConjugateMatterDerivativeDual_apply
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    holonomicConjugateMatterDerivativeDual configuration point direction
        matter =
      fieldDirectionalDerivative
        (fun candidate => configuration.conjugateMatter candidate matter)
        point direction := by
  have coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point :=
    (holonomicConjugateMatterCoordinates_contDiff configuration smooth)
      |>.differentiable (by simp) |>.differentiableAt
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (matterDualCoordinateEvaluation matter).restrictScalars ℝ
  have evaluationIdentity :
      (fun candidate => configuration.conjugateMatter candidate matter) =
        fun candidate =>
          evaluation (holonomicConjugateMatterCoordinates configuration
            candidate) := by
    funext candidate
    change configuration.conjugateMatter candidate matter =
      matterDualCoordinateEvaluation matter
        (matterDualCoordinates (configuration.conjugateMatter candidate))
    rw [matterDualCoordinateEvaluation_apply,
      matterDualOfCoordinates_surjective]
  have derivative := evaluation.hasFDerivAt.comp point
    coordinateDifferentiable.hasFDerivAt
  rw [evaluationIdentity]
  unfold fieldDirectionalDerivative
  change
    holonomicConjugateMatterDerivativeDual configuration point direction
          matter =
      fderiv ℝ
          (evaluation ∘ holonomicConjugateMatterCoordinates configuration)
          point (coordinateDirection direction)
  rw [derivative.fderiv]
  change
    matterDualOfCoordinates
        (fderiv ℝ (holonomicConjugateMatterCoordinates configuration) point
          (coordinateDirection direction)) matter =
      matterDualCoordinateEvaluation matter
        (fderiv ℝ (holonomicConjugateMatterCoordinates configuration) point
          (coordinateDirection direction))
  rw [matterDualCoordinateEvaluation_apply]

theorem holonomicConjugateMatterDerivativeDual_apply_re
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    (holonomicConjugateMatterDerivativeDual configuration point direction
        matter).re =
      fieldDirectionalDerivative
        (fun candidate => (configuration.conjugateMatter candidate matter).re)
        point direction := by
  have complexSmooth : ContDiff ℝ ∞ (fun candidate =>
      configuration.conjugateMatter candidate matter) :=
    varyingConjugateMatterDual_apply_contDiff configuration smooth
      (fun _ => matter) contDiff_const
  have complexDifferentiable : DifferentiableAt ℝ (fun candidate =>
      configuration.conjugateMatter candidate matter) point :=
    complexSmooth.differentiable (by simp) |>.differentiableAt
  have realDerivative := Complex.reCLM.hasFDerivAt.comp point
    complexDifferentiable.hasFDerivAt
  unfold fieldDirectionalDerivative
  change
    (holonomicConjugateMatterDerivativeDual configuration point direction
        matter).re =
      fderiv ℝ
          (Complex.reCLM ∘ fun candidate =>
            configuration.conjugateMatter candidate matter)
          point (coordinateDirection direction)
  rw [realDerivative.fderiv]
  change
    (holonomicConjugateMatterDerivativeDual configuration point direction
      matter).re =
      (fderiv ℝ (fun candidate =>
          configuration.conjugateMatter candidate matter) point
        (coordinateDirection direction)).re
  rw [holonomicConjugateMatterDerivativeDual_apply configuration smooth]
  rfl

theorem holonomicIdentityCoframeMatterAlgebraicVector
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    matterAlgebraicVariationVector source configuration direction point =
      holonomicIdentityCoframeMatterAlgebraicOperator configuration point
        (matterCoordinateEquiv.symm direction) := by
  unfold matterAlgebraicVariationVector matterFieldVariationVector
    holonomicIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  rw [matterGaugeKineticSum_zeroChart]
  simp only [toContinuumPointField]
  rw [show configuration.coframe point = 1 by
    exact congrFun identityCoframe point]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
    identityCoframeMatterGeometry by rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply]
  unfold holonomicMatterVariationAlgebraicDirection
  rfl

theorem holonomicIdentityCoframeMatterAlgebraicCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    matterAlgebraicDirectionalCoefficient source configuration direction
        point =
      (configuration.conjugateMatter point
        (holonomicIdentityCoframeMatterAlgebraicOperator configuration point
          (matterCoordinateEquiv.symm direction))).re := by
  unfold matterAlgebraicDirectionalCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [show configuration.coframe point = 1 by
    exact congrFun identityCoframe point]
  rw [Matrix.det_one, abs_one, one_mul,
    holonomicIdentityCoframeMatterAlgebraicVector source configuration
      identityCoframe]

theorem holonomicIdentityCoframeMatterDifferentialMomentum
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum source configuration direction
        derivativeDirection =
      fun point =>
        (configuration.conjugateMatter point
          (identityCoframeMatterPrincipal derivativeDirection
            (matterCoordinateEquiv.symm direction))).re := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [show configuration.coframe point = 1 by
    exact congrFun identityCoframe point]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
    identityCoframeMatterGeometry by rfl]
  rw [inverseCoframeDiracGamma_identity]
  simp [identityCoframeMatterPrincipal]

theorem holonomicIdentityCoframeMatterMomentumDivergence
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    matterDifferentialMomentumDivergence source configuration direction
        point =
      ∑ derivativeDirection : LorentzianIndex,
        (holonomicConjugateMatterDerivativeDual configuration point
          derivativeDirection
          (identityCoframeMatterPrincipal derivativeDirection
            (matterCoordinateEquiv.symm direction))).re := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [holonomicIdentityCoframeMatterDifferentialMomentum source configuration
    identityCoframe direction derivativeDirection]
  exact (holonomicConjugateMatterDerivativeDual_apply_re configuration smooth
    point derivativeDirection
    (identityCoframeMatterPrincipal derivativeDirection
      (matterCoordinateEquiv.symm direction))).symm

def holonomicIdentityCoframeConjugateMatterActionResidual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicIdentityCoframeConjugateMatterKnownDual configuration point -
    (holonomicConjugateMatterDerivativeDual configuration point
      canonicalLorentzianTimeDirection).comp
      (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection)

theorem holonomicIdentityCoframeMatterEulerLagrange_eq_actionResidual_re
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    matterEulerLagrangeDirectionalCoefficient source configuration direction
        point =
      (holonomicIdentityCoframeConjugateMatterActionResidual configuration
        point (matterCoordinateEquiv.symm direction)).re := by
  rw [show
    matterEulerLagrangeDirectionalCoefficient source configuration direction
        point =
      matterAlgebraicDirectionalCoefficient source configuration direction
          point -
        matterDifferentialMomentumDivergence source configuration direction
          point by rfl]
  rw [holonomicIdentityCoframeMatterAlgebraicCoefficient source configuration
      identityCoframe,
    holonomicIdentityCoframeMatterMomentumDivergence source configuration
      smooth identityCoframe]
  unfold holonomicIdentityCoframeConjugateMatterActionResidual
    holonomicIdentityCoframeConjugateMatterKnownDual
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    Complex.sub_re]
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  simp only [Complex.add_re, canonicalLorentzianTimeDirection]
  simp
  ring

theorem positiveAdjointDiagonalActual_hasIdentityCoframe :
    HasIdentityCoframe
      positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual := by
  funext point
  exact
    positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift_coframe_one
      0 point

theorem positiveAdjointDiagonalActual_matterEulerLagrange_eq_actionResidual_re
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual direction
        point =
      (holonomicIdentityCoframeConjugateMatterActionResidual
        positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual point
        (matterCoordinateEquiv.symm direction)).re := by
  exact holonomicIdentityCoframeMatterEulerLagrange_eq_actionResidual_re
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual_smooth
    positiveAdjointDiagonalActual_hasIdentityCoframe direction point

/-! ## Direct C3h196 adjoint evolution first-germ verdict -/

def c3h196TemporalAdjointELProbe : MatterCoordinateCarrier :=
  matterCoordinateEquiv (Complex.I • diracSpinTwoMatterProbe)

def c3h196TemporalAdjointELCoefficient (point : BasePoint) : ℝ :=
  matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
    positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
    c3h196TemporalAdjointELProbe point

/-! ## Exact Riesz normal form of the inherited P286 Gauss charge -/

def p506MatterCurrentGaussColorRaw : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun index =>
    if index = 0 then -(2 / 3 : ℂ) * Complex.I
    else (1 / 3 : ℂ) * Complex.I

def p506MatterCurrentGaussColor : SU3BlockLieMatrix := by
  refine ⟨p506MatterCurrentGaussColorRaw, ?_, ?_⟩
  · ext row column
    fin_cases row <;> fin_cases column <;>
      simp [p506MatterCurrentGaussColorRaw]
  · simp [p506MatterCurrentGaussColorRaw, Matrix.trace, Fin.sum_univ_three]
    ring

def p506MatterCurrentGaussData : P286LieBlockData :=
  (p506MatterCurrentGaussColor, 0, -hyperchargeGenerator)

def p506MatterCurrentGaussCoordinate : P286CoordinateCarrier :=
  p286CoordinateEquiv p506MatterCurrentGaussData

theorem p506MatterCurrentGaussCoordinate_pairing_self :
    p286CoordinateLiePairing p506MatterCurrentGaussCoordinate
        p506MatterCurrentGaussCoordinate = 5 / 3 := by
  unfold p286CoordinateLiePairing p506MatterCurrentGaussCoordinate
    p506MatterCurrentGaussData p286LiePairing
  rw [p286CoordinateEquiv.symm_apply_apply]
  rw [specialUnitaryLiePairing_self_eq_sum_normSq]
  simp [p506MatterCurrentGaussColor, p506MatterCurrentGaussColorRaw,
    specialUnitaryLiePairing, hyperchargeLiePairing, hyperchargeGenerator,
    Complex.normSq_apply, Matrix.diagonal_apply, Fin.sum_univ_three]
  norm_num

theorem p506MatterCurrentGaussCoordinate_pairing
    (data : P286LieBlockData) :
    p286CoordinateLiePairing p506MatterCurrentGaussCoordinate
        (p286CoordinateEquiv data) =
      (Complex.I *
        ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 + data.2.2.1)).re := by
  have traceZero := specialUnitaryLieMatrix_trace data.1
  have imaginaryTraceZero := congrArg Complex.im traceZero
  simp [Matrix.trace, Fin.sum_univ_three] at imaginaryTraceZero
  simp [p506MatterCurrentGaussCoordinate, p506MatterCurrentGaussData,
    p286CoordinateLiePairing, p286LiePairing, p506MatterCurrentGaussColor,
    p506MatterCurrentGaussColorRaw, specialUnitaryLiePairing,
    hyperchargeLiePairing, hyperchargeGenerator, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_three, Complex.mul_re]
  linarith

theorem fundamentalMotherLieAction_basis_coordinate
    (matrix : SU7MotherLieMatrix) (out input : SU7MotherIndex) :
    (su7FundamentalBasis.repr
        (fundamentalMotherLieAction matrix (su7FundamentalBasis input))) out =
      (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) out input := by
  simp [fundamentalMotherLieAction, su7FundamentalBasis,
    Matrix.mulVecLin]

theorem occupiedExteriorBasisLieAction_coordinate
    (matrix : SU7MotherLieMatrix) :
    (su7ExteriorBasis 2).repr
        (exteriorBasisLieAction 2 matrix hyperchargeDegreeTwoIndex)
        hyperchargeDegreeTwoIndex =
      ∑ position : Fin 2,
        (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)
          (exteriorPositionEquiv hyperchargeDegreeTwoIndex position).1
          (exteriorPositionEquiv hyperchargeDegreeTwoIndex position).1 := by
  unfold exteriorBasisLieAction
  calc
    _ = ∑ position : Fin 2,
        (su7ExteriorBasis 2).repr
          ((exteriorPower.ιMulti ℂ 2)
            (StageNineP286GaugeConnectionVariation.exteriorBasisLieActionInput
              2 matrix hyperchargeDegreeTwoIndex position))
          hyperchargeDegreeTwoIndex := by
      rw [map_sum]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro position _
      rw [StageNineP286GaugeConnectionVariation.exteriorBasisLieActionTerm_eq_update]
      unfold su7ExteriorBasis
      rw [exteriorPower.basis_repr_apply,
        exteriorPower.ιMultiDual_apply_ιMulti, Matrix.det_fin_two]
      have positionValue (candidate : Fin 2) :
          Set.powersetCard.ofFinEmbEquiv.symm hyperchargeDegreeTwoIndex
              candidate =
            (exteriorPositionEquiv hyperchargeDegreeTwoIndex candidate).1 :=
        by rfl
      simp only [positionValue]
      fin_cases position <;>
        simp [StageNineP286GaugeConnectionVariation.exteriorBasisInput,
          fundamentalMotherLieAction_basis_coordinate]

theorem occupiedExteriorAction_coordinate (data : P286LieBlockData) :
    (su7ExteriorBasis 2).repr
        (exteriorMotherLieAction 2 (p286LieBlockEmbed data)
          (su7ExteriorBasis 2 hyperchargeDegreeTwoIndex))
        hyperchargeDegreeTwoIndex =
      (data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 + data.2.2.1 := by
  rw [exteriorMotherLieAction_basis_current,
    occupiedExteriorBasisLieAction_coordinate]
  let mother : Matrix SU7MotherIndex SU7MotherIndex ℂ := p286LieBlockEmbed data
  change
    (∑ position : Fin 2,
      mother (exteriorPositionEquiv hyperchargeDegreeTwoIndex position).1
        (exteriorPositionEquiv hyperchargeDegreeTwoIndex position).1) = _
  calc
    _ = ∑ basisIndex ∈ hyperchargeDegreeTwoIndex.1,
        mother basisIndex basisIndex :=
      exteriorPosition_sum_eq_subset_sum_complex
        hyperchargeDegreeTwoIndex (fun basisIndex => mother basisIndex basisIndex)
    _ = _ := by
      simp [mother, hyperchargeDegreeTwoIndex, hyperchargeDegreeTwoSubset,
        hyperPlusIndex,
        p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
        hyperchargeLieBlock, scalarLieBlock]

theorem p286SpinTwoInternalVariation_time_readout
    (data : P286LieBlockData) :
    diracSpinZeroMatterCoordinate
        (diracMatrixMatterAction diracGammaZero
          (p286SpinTwoInternalVariation (p286CoordinateEquiv data))) =
      (data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 + data.2.2.1 := by
  simp [p286SpinTwoInternalVariation,
    diracExteriorMotherLieAction_spinTwo_normalForm,
    diracSpinZeroMatterCoordinate, diracMatrixMatterAction,
    diracGammaZero, Fin.sum_univ_four, exteriorSpinorMotherLieAction,
    p286HyperchargeMatterProbe, hyperchargeDegreeTwoMatterCoordinate,
    occupiedExteriorAction_coordinate]

theorem gravityCoupledTemporalMatterKineticSum_normalForm
    (data : P286LieBlockData) :
    matterGaugeKineticSum positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506MatterCurrentGravityCoupledLocalActualLift 0)
        (holonomicMatterGaugeConnectionVariation
          positiveP506MatterCurrentGravityCoupledLocalActualLift
          (fun _ => p286TemporalGaugeOneForm (p286CoordinateEquiv data)) 0) =
      diracMatrixMatterAction diracGammaZero
        (p286SpinTwoInternalVariation (p286CoordinateEquiv data)) := by
  have coframeEq :
      positiveP506MatterCurrentGravityCoupledLocalActualLift.coframe 0 = 1 :=
    positiveP506MatterCurrentGravityCoupledLocalActualLift_coframe_one 0
  rw [temporalMatterVariation_normalForm]
  unfold matterGaugeKineticSum
  simp only [toContinuumPointField, coframeEq, Fin.sum_univ_four]
  simp only [matterDerivativeFrameRelative, matterFrameRelative_chartZero]
  simp
  change
    diracMatrixMatterAction
        (inverseCoframeDiracGamma identityCoframeMatterGeometry 0)
        (p286SpinTwoInternalVariation (p286CoordinateEquiv data)) = _
  rw [inverseCoframeDiracGamma_identity]
  rfl

theorem gravityCoupledTemporalMatterFirstVariationDensity_normalForm
    (data : P286LieBlockData) :
    matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource
        0 0
        (toContinuumPointField
          positiveP506MatterCurrentGravityCoupledLocalActualLift 0)
        (holonomicMatterGaugeConnectionVariation
          positiveP506MatterCurrentGravityCoupledLocalActualLift
          (fun _ => p286TemporalGaugeOneForm (p286CoordinateEquiv data)) 0) =
      (Complex.I *
        ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 + data.2.2.1)).re := by
  have conjugateEq :
      positiveP506MatterCurrentGravityCoupledLocalActualLift.conjugateMatter
          0 =
        diracSpinZeroMatterCoordinate :=
    positiveP506MatterCurrentGravityCoupledLocalActualLift_conjugate_origin
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector
  rw [gravityCoupledTemporalMatterKineticSum_normalForm]
  simp only [toContinuumPointField, conjugateEq,
    matterDualFrameRelative_chartZero, map_smul]
  rw [p286SpinTwoInternalVariation_time_readout]
  rfl

theorem gravityCoupledTemporalMatterCurrent_normalForm
    (data : P286LieBlockData) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (p286TemporalGaugeOneForm (p286CoordinateEquiv data)) 0 =
      (Complex.I *
        ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 + data.2.2.1)).re := by
  have baseCoframeEq :
      positiveP506MatterCurrentGravityCoupledBaseActual.coframe 0 = 1 :=
    positiveP506MatterCurrentGravityCoupledBaseField_coframe
  unfold p286MatterCurrentCoefficient
  rw [gravityCoupledTemporalMatterFirstVariationDensity_normalForm]
  simp [generatedVolumeDensity, toContinuumPointField, baseCoframeEq]

theorem gravityCoupledTemporalGaussActionTarget_normalForm
    (data : P286LieBlockData) :
    positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget
        (p286CoordinateEquiv data) =
      (Complex.I *
        ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 + data.2.2.1)).re := by
  change
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift
        (p286TemporalGaugeOneForm (p286CoordinateEquiv data)) 0 = _
  rw [currentMomentum_actionCurrent_origin_eq_currentU5]
  rw [p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors]
  rw [p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift (by
        rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
        rfl),
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift
      (positiveP506MatterCurrentGravityCoupledLocalActualLift_scalarCovariantDerivative_zero
        0)]
  simp only [zero_add]
  exact gravityCoupledTemporalMatterCurrent_normalForm data

theorem gravityCoupledGaussCharge_eq_normalForm :
    positiveP506MatterCurrentGravityCoupledP286GaussCharge =
      p506MatterCurrentGaussCoordinate := by
  symm
  apply positiveP506MatterCurrentGravityCoupledP286GaussCharge_unique
  intro component
  rw [← p286CoordinateEquiv.apply_symm_apply component]
  rw [p506MatterCurrentGaussCoordinate_pairing,
    gravityCoupledTemporalGaussActionTarget_normalForm]

theorem currentGaussCharge_eq_normalForm :
    positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge =
      p506MatterCurrentGaussCoordinate := by
  rw [currentGaussCharge_eq_priorGaussCharge,
    gravityCoupledGaussCharge_eq_normalForm]

private def currentGaussFundamentalCoefficient
    (index : SU7MotherIndex) : ℂ :=
  (p286LieBlockEmbed p506MatterCurrentGaussData :
    Matrix SU7MotherIndex SU7MotherIndex ℂ) index index

private theorem currentGaussFundamentalAction_basis
    (index : SU7MotherIndex) :
    fundamentalMotherLieAction
        (p286LieBlockEmbed p506MatterCurrentGaussData)
        (su7FundamentalBasis index) =
      currentGaussFundamentalCoefficient index •
        su7FundamentalBasis index := by
  funext row
  fin_cases index <;> fin_cases row <;>
    simp +decide [currentGaussFundamentalCoefficient,
      fundamentalMotherLieAction, p506MatterCurrentGaussData,
      p506MatterCurrentGaussColor, p506MatterCurrentGaussColorRaw,
      p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock, hyperchargeGenerator,
      su7FundamentalBasis, Matrix.mulVecLin, Matrix.mulVec]

private theorem currentGaussExteriorAction_basis
    (degree : ℕ) (index : ExteriorBasisIndex degree) :
    exteriorMotherLieAction degree
        (p286LieBlockEmbed p506MatterCurrentGaussData)
        (su7ExteriorBasis degree index) =
      (∑ position : Fin degree,
          currentGaussFundamentalCoefficient
            (exteriorPositionEquiv index position).1) •
        su7ExteriorBasis degree index := by
  rw [exteriorMotherLieAction_basis_current]
  unfold exteriorBasisLieAction
  calc
    _ = ∑ position : Fin degree,
        currentGaussFundamentalCoefficient
            (exteriorPositionEquiv index position).1 •
          su7ExteriorBasis degree index := by
      apply Finset.sum_congr rfl
      intro position _
      change
        (exteriorPower.ιMulti ℂ degree)
            (StageNineP286GaugeConnectionVariation.exteriorBasisLieActionInput
              degree (p286LieBlockEmbed p506MatterCurrentGaussData)
              index position) = _
      rw [StageNineP286GaugeConnectionVariation.exteriorBasisLieActionTerm_eq_update,
        show StageNineP286GaugeConnectionVariation.exteriorBasisInput degree
              index position =
            su7FundamentalBasis
              (exteriorPositionEquiv index position).1 by
          rfl,
        currentGaussFundamentalAction_basis,
        (exteriorPower.ιMulti ℂ degree).map_update_smul,
        show su7FundamentalBasis
              (exteriorPositionEquiv index position).1 =
            StageNineP286GaugeConnectionVariation.exteriorBasisInput degree
              index position by rfl,
        Function.update_eq_self]
      exact congrArg
        (fun value =>
          currentGaussFundamentalCoefficient
              (exteriorPositionEquiv index position).1 • value)
        (exteriorBasisInput_wedge_eq_basis_current degree index)
    _ = _ := by rw [← Finset.sum_smul]

private theorem currentGaussExteriorAction_degreeTwo :
    exteriorMotherLieAction 2
        (p286LieBlockEmbed p506MatterCurrentGaussData)
        (su7ExteriorBasis 2 hyperchargeDegreeTwoIndex) =
      (-(5 / 3 : ℂ) * Complex.I) •
        su7ExteriorBasis 2 hyperchargeDegreeTwoIndex := by
  rw [exteriorMotherLieAction_basis_current]
  unfold exteriorBasisLieAction
  calc
    _ = ∑ position : Fin 2,
        currentGaussFundamentalCoefficient
            (exteriorPositionEquiv hyperchargeDegreeTwoIndex position).1 •
          su7ExteriorBasis 2 hyperchargeDegreeTwoIndex := by
      apply Finset.sum_congr rfl
      intro position _
      change
        (exteriorPower.ιMulti ℂ 2)
            (StageNineP286GaugeConnectionVariation.exteriorBasisLieActionInput 2
              (p286LieBlockEmbed p506MatterCurrentGaussData)
              hyperchargeDegreeTwoIndex position) = _
      rw [StageNineP286GaugeConnectionVariation.exteriorBasisLieActionTerm_eq_update,
        show StageNineP286GaugeConnectionVariation.exteriorBasisInput 2
              hyperchargeDegreeTwoIndex position =
            su7FundamentalBasis
              (exteriorPositionEquiv hyperchargeDegreeTwoIndex position).1 by
          rfl,
        currentGaussFundamentalAction_basis,
        (exteriorPower.ιMulti ℂ 2).map_update_smul,
        show su7FundamentalBasis
              (exteriorPositionEquiv hyperchargeDegreeTwoIndex position).1 =
            StageNineP286GaugeConnectionVariation.exteriorBasisInput 2
              hyperchargeDegreeTwoIndex position by rfl,
        Function.update_eq_self]
      exact congrArg
        (fun value =>
          currentGaussFundamentalCoefficient
              (exteriorPositionEquiv hyperchargeDegreeTwoIndex position).1 •
            value)
        (exteriorBasisInput_wedge_eq_basis_current 2
          hyperchargeDegreeTwoIndex)
    _ = (∑ position : Fin 2,
          currentGaussFundamentalCoefficient
            (exteriorPositionEquiv hyperchargeDegreeTwoIndex position).1) •
        su7ExteriorBasis 2 hyperchargeDegreeTwoIndex := by
      rw [Finset.sum_smul]
    _ = _ := by
      congr 1
      calc
        _ = ∑ basisIndex ∈ hyperchargeDegreeTwoIndex.1,
            currentGaussFundamentalCoefficient basisIndex :=
          exteriorPosition_sum_eq_subset_sum_complex
            hyperchargeDegreeTwoIndex currentGaussFundamentalCoefficient
        _ = _ := by
          simp +decide [hyperchargeDegreeTwoIndex,
            hyperchargeDegreeTwoSubset, currentGaussFundamentalCoefficient,
            p506MatterCurrentGaussData, p506MatterCurrentGaussColor,
            p506MatterCurrentGaussColorRaw, p286LieBlockEmbed,
            rawP286LieBlock, weakHyperchargeLieBlock, hyperchargeLieBlock,
            scalarLieBlock, hyperchargeGenerator,
            Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂,
            hyperPlusIndex]
          ring

/-- The source-generated P506 Gauss charge acts on the occupied degree-two
hypercharge state with its exact `-5i/3` weight. -/
theorem currentGaussCharge_hyperchargeProbe_action_normalForm :
    exteriorSpinorMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
        p286HyperchargeMatterProbe =
      (-(5 / 3 : ℂ) * Complex.I) •
        p286HyperchargeMatterProbe := by
  rw [currentGaussCharge_eq_normalForm]
  rw [show p286CoordinateEquiv.symm p506MatterCurrentGaussCoordinate =
      p506MatterCurrentGaussData by
    simp [p506MatterCurrentGaussCoordinate]]
  simp [exteriorSpinorMotherLieAction, p286HyperchargeMatterProbe,
    currentGaussExteriorAction_degreeTwo]

/-- The same source charge acts diagonally on the occupied degree-two
coordinate of every exterior-spinor field, not only on the calibration
basis vector. -/
theorem currentGaussCharge_hyperchargeCoordinate_action_normalForm
    (matter : SU7ExteriorSpinorMatterCarrier) :
    hyperchargeDegreeTwoMatterCoordinate
        (exteriorSpinorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
          matter) =
      (-(5 / 3 : ℂ) * Complex.I) *
        hyperchargeDegreeTwoMatterCoordinate matter := by
  rw [currentGaussCharge_eq_normalForm]
  rw [show p286CoordinateEquiv.symm p506MatterCurrentGaussCoordinate =
      p506MatterCurrentGaussData by
    simp [p506MatterCurrentGaussCoordinate]]
  change
    (su7ExteriorBasis 2).repr
        (∑ index : ExteriorBasisIndex 2,
          ((su7ExteriorBasis 2).repr matter.2.1 index) •
            exteriorBasisLieAction 2
              (p286LieBlockEmbed p506MatterCurrentGaussData) index)
        hyperchargeDegreeTwoIndex =
      (-(5 / 3 : ℂ) * Complex.I) *
        (su7ExteriorBasis 2).repr matter.2.1 hyperchargeDegreeTwoIndex
  rw [map_sum, Finset.sum_apply']
  rw [Finset.sum_eq_single hyperchargeDegreeTwoIndex]
  · rw [map_smul, ← exteriorMotherLieAction_basis_current,
      currentGaussExteriorAction_degreeTwo, map_smul]
    simp
    ring
  · intro index _ indexNe
    rw [map_smul, ← exteriorMotherLieAction_basis_current,
      currentGaussExteriorAction_basis, map_smul]
    simp [Ne.symm indexNe]
  · simp

theorem currentGaussCharge_diracCoordinate_action_normalForm
    (matter : DiracExteriorMatterCarrier) :
    diracSpinZeroMatterCoordinate
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
          matter) =
      (-(5 / 3 : ℂ) * Complex.I) *
        diracSpinZeroMatterCoordinate matter := by
  exact currentGaussCharge_hyperchargeCoordinate_action_normalForm (matter 0)

theorem currentGaussCharge_realSmul_diracCoordinate_action_normalForm
    (parameter : ℝ) (matter : DiracExteriorMatterCarrier) :
    diracSpinZeroMatterCoordinate
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (parameter •
                positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)))
          matter) =
      ((parameter : ℂ) * (-(5 / 3 : ℂ) * Complex.I)) *
        diracSpinZeroMatterCoordinate matter := by
  rw [p286CoordinateEquiv.symm.map_smul,
    StageNineP286GaugeConnectionVariation.p286LieBlockEmbed_real_smul,
    StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_real_smul,
    LinearMap.smul_apply, map_smul,
    currentGaussCharge_diracCoordinate_action_normalForm]
  ring

theorem currentGaussCharge_realSmul_diracCoordinate_principal_action_normalForm
    (parameter : ℝ) (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    diracSpinZeroMatterCoordinate
        (identityCoframeMatterPrincipal direction
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                (parameter •
                  positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)))
            matter)) =
      ((parameter : ℂ) * (-(5 / 3 : ℂ) * Complex.I)) *
        diracSpinZeroMatterCoordinate
          (identityCoframeMatterPrincipal direction matter) := by
  simp only [identityCoframeMatterPrincipal_apply, map_smul]
  rw [show diracMatrixMatterAction (diracGamma direction)
      (diracExteriorMotherLieAction
        (p286LieBlockEmbed
          (parameter • p286CoordinateEquiv.symm
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
        matter) =
      diracExteriorMotherLieAction
        (p286LieBlockEmbed
          (parameter • p286CoordinateEquiv.symm
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
        (diracMatrixMatterAction (diracGamma direction) matter) by
    exact LinearMap.congr_fun
      (diracMatrixMatterAction_commutes_internal
        (diracGamma direction)
        (exteriorSpinorMotherLieAction
          (p286LieBlockEmbed
            (parameter • p286CoordinateEquiv.symm
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))))
      matter]
  have evaluated :=
    currentGaussCharge_realSmul_diracCoordinate_action_normalForm parameter
      (diracMatrixMatterAction (diracGamma direction) matter)
  rw [show
    diracSpinZeroMatterCoordinate
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (parameter • p286CoordinateEquiv.symm
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
          (diracMatrixMatterAction (diracGamma direction) matter)) =
      ((parameter : ℂ) * (-(5 / 3 : ℂ) * Complex.I)) *
        diracSpinZeroMatterCoordinate
          (diracMatrixMatterAction (diracGamma direction) matter) by
    simpa only [p286CoordinateEquiv.symm.map_smul] using evaluated]
  ring

theorem currentGaussCharge_spinTwo_action_normalForm :
    diracExteriorMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
        diracSpinTwoMatterProbe =
      (-(5 / 3 : ℂ) * Complex.I) • diracSpinTwoMatterProbe := by
  funext spinIndex
  fin_cases spinIndex <;>
    simp [diracExteriorMotherLieAction, internalMatterLinearAction,
      diracSpinTwoMatterProbe,
      currentGaussCharge_hyperchargeProbe_action_normalForm]

/-- The fixed Gauss charge keeps the same occupied-state weight after any
Dirac-matrix action, since the two actions live on independent factors. -/
theorem currentGaussCharge_diracMatrix_spinTwo_action_normalForm
    (matrix : DiracMatrix) :
    diracExteriorMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
        (diracMatrixMatterAction matrix diracSpinTwoMatterProbe) =
      (-(5 / 3 : ℂ) * Complex.I) •
        diracMatrixMatterAction matrix diracSpinTwoMatterProbe := by
  rw [show diracExteriorMotherLieAction
      (p286LieBlockEmbed
        (p286CoordinateEquiv.symm
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
      (diracMatrixMatterAction matrix diracSpinTwoMatterProbe) =
        diracMatrixMatterAction matrix
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
            diracSpinTwoMatterProbe) by
    simpa only [diracExteriorMotherLieAction, LinearMap.comp_apply] using
      (LinearMap.congr_fun
        (diracMatrixMatterAction_commutes_internal matrix
          (exteriorSpinorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))))
        diracSpinTwoMatterProbe).symm]
  rw [currentGaussCharge_spinTwo_action_normalForm, map_smul]

/-- The same fixed charge weight after the temporal principal factor used by
the adjoint profile and one arbitrary Dirac-current probe. -/
theorem currentGaussCharge_timePrincipal_diracProbe_action_normalForm
    (direction : LorentzianIndex) :
    diracExteriorMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
        (identityCoframeMatterPrincipal
          canonicalLorentzianTimeDirection
          (diracMatrixMatterAction (diracGamma direction)
            diracSpinTwoMatterProbe)) =
      (-(5 / 3 : ℂ) * Complex.I) •
        identityCoframeMatterPrincipal
          canonicalLorentzianTimeDirection
          (diracMatrixMatterAction (diracGamma direction)
            diracSpinTwoMatterProbe) := by
  rw [identityCoframeMatterPrincipal_apply, map_smul]
  rw [show diracExteriorMotherLieAction
      (p286LieBlockEmbed
        (p286CoordinateEquiv.symm
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
      (diracMatrixMatterAction
        (diracGamma canonicalLorentzianTimeDirection)
        (diracMatrixMatterAction (diracGamma direction)
          diracSpinTwoMatterProbe)) =
        diracMatrixMatterAction
          (diracGamma canonicalLorentzianTimeDirection)
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
            (diracMatrixMatterAction (diracGamma direction)
              diracSpinTwoMatterProbe)) by
    change internalMatterLinearAction
        (exteriorSpinorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)))
        (diracMatrixMatterAction
          (diracGamma canonicalLorentzianTimeDirection)
          (diracMatrixMatterAction (diracGamma direction)
            diracSpinTwoMatterProbe)) =
      diracMatrixMatterAction
        (diracGamma canonicalLorentzianTimeDirection)
        (internalMatterLinearAction
          (exteriorSpinorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)))
          (diracMatrixMatterAction (diracGamma direction)
            diracSpinTwoMatterProbe))
    exact (LinearMap.congr_fun
      (diracMatrixMatterAction_commutes_internal
        (diracGamma canonicalLorentzianTimeDirection)
        (exteriorSpinorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))))
      (diracMatrixMatterAction (diracGamma direction)
        diracSpinTwoMatterProbe)).symm]
  rw [currentGaussCharge_diracMatrix_spinTwo_action_normalForm, map_smul]
  simp only [smul_smul]
  congr 1
  ring

theorem currentGaussCharge_realSmul_timePrincipal_diracProbe_action_normalForm
    (parameter : ℝ) (direction : LorentzianIndex) :
    diracExteriorMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (parameter •
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)))
        (identityCoframeMatterPrincipal
          canonicalLorentzianTimeDirection
          (diracMatrixMatterAction (diracGamma direction)
            diracSpinTwoMatterProbe)) =
      ((parameter : ℂ) * (-(5 / 3 : ℂ) * Complex.I)) •
        identityCoframeMatterPrincipal
          canonicalLorentzianTimeDirection
          (diracMatrixMatterAction (diracGamma direction)
            diracSpinTwoMatterProbe) := by
  rw [p286CoordinateEquiv.symm.map_smul,
    StageNineP286GaugeConnectionVariation.p286LieBlockEmbed_real_smul,
    StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_real_smul,
    LinearMap.smul_apply,
    currentGaussCharge_timePrincipal_diracProbe_action_normalForm,
    smul_smul]

theorem currentGaussCharge_pairing_self :
    p286CoordinateLiePairing
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge =
      5 / 3 := by
  rw [currentGaussCharge_eq_normalForm]
  exact p506MatterCurrentGaussCoordinate_pairing_self

end


end
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport
