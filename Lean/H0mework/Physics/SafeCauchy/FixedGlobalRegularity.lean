import H0mework.Physics.SafeCauchy.FixedGlobalOperator
import H0mework.Physics.JointVariation.MatterTemporalLocalRegularity
import H0mework.Physics.CoframeVariation.CoframeGaugeEulerParameterContinuity
import H0mework.Physics.CoframeVariation.CoframeMatterEulerParameterContinuity
import H0mework.Physics.Geometry.CanonicalTimePrimitiveSegmentRegularity

/-!
# Fixed P506/L0 Cauchy-safe Cartan--EC Cauchy global regularity

The Cauchy-safe prepared current already carries smooth primitive
fields and pointwise coframe nondegeneracy.  This module proves that its
source/current-only Cartan restart, EC profile, canonical time primitive, and
reaction write generate a smooth final Cauchy actual.  No output regularity,
target curvature, residual, support, branch, or completed field is accepted at
the theorem mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalRegularity

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity
open StageNineDiracDualFormNativeCoframeMatterEulerParameterContinuity
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineCanonicalTimePrimitiveSegmentRegularity
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Module.Free.ChooseBasisIndex.fintype ℝ P286LieBlockData

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeGlobalActual

private abbrev Base : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source Prepared

private theorem base_connection_smooth :
    ∀ direction internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        Base.gravityConnection point direction internalOut internalIn := by
  intro direction internalOut internalIn
  rw [contDiff_iff_contDiffAt]
  intro point
  exact cartanReactionRestart_connection_component_contDiffAt
    Source Prepared
    fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth point
    (fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate point)
    direction internalOut internalIn

private theorem base_auxiliary_smooth :
    ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        Base.gravityAuxiliary point internalPair spacetimePair := by
  intro internalPair spacetimePair
  change ContDiff ℝ ∞ fun point =>
    physicalIIPlusBivector (Prepared.coframe point)
      internalPair spacetimePair
  have preparedCoframeSmooth : ContDiff ℝ ∞ Prepared.coframe := by
    apply contDiff_pi'
    intro row
    apply contDiff_pi'
    intro column
    exact fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth.1
      row column
  exact contDiff_pi.mp
    (contDiff_pi.mp
      (physicalIIPlusBivector_contDiff.comp preparedCoframeSmooth)
      internalPair)
    spacetimePair

private theorem base_multiplier_smooth :
    ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        Base.gravitySimplicityMultiplier point internalPair spacetimePair := by
  intro internalPair spacetimePair
  change ContDiff ℝ ∞ fun point =>
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      Source Prepared).gravitySimplicityMultiplier point
        internalPair spacetimePair
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated]
  exact formNativeGravityReactionField_component_contDiff
    Base base_connection_smooth base_auxiliary_smooth
    internalPair spacetimePair

private theorem base_smooth : Base.Smooth := by
  let preparedSmooth :=
    fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth
  exact
    ⟨preparedSmooth.1, base_connection_smooth, base_auxiliary_smooth,
      base_multiplier_smooth,
      preparedSmooth.2.2.2.2.1,
      preparedSmooth.2.2.2.2.2.1,
      preparedSmooth.2.2.2.2.2.2.1,
      preparedSmooth.2.2.2.2.2.2.2.1,
      preparedSmooth.2.2.2.2.2.2.2.2⟩

private abbrev ECPrepared : StageNineHolonomicConfiguration :=
  diracDualFormNativeECNormalPreparedActual Base

private theorem ecPrepared_smooth : ECPrepared.Smooth :=
  restrictHolonomicConfigurationToIIPlus_smooth Base base_smooth

private def FixedField (contact : BasePoint) : StageNineContinuumPointField :=
  restrictContinuumPointFieldToIIPlus (toContinuumPointField Base contact)

private theorem fixedField_coframe_contDiff :
    ContDiff ℝ ∞ fun contact => (FixedField contact).coframe := by
  change ContDiff ℝ ∞ Base.coframe
  exact holonomicCoframe_contDiff Base base_smooth

private theorem fixedGaugeParameter_contDiff :
    ContDiff ℝ ∞ fun contact =>
      coframeGaugeActionParameterOfField (FixedField contact) := by
  apply ContDiff.prodMk
  · apply contDiff_pi'
    intro pair
    change ContDiff ℝ ∞ fun contact =>
      p286CoordinateEquiv (ECPrepared.gaugeAuxiliary contact pair)
    exact ecPrepared_smooth.2.2.2.2.2.1 pair
  · apply contDiff_pi'
    intro pair
    change ContDiff ℝ ∞ fun contact =>
      p286CoordinateEquiv (holonomicGaugeCurvature ECPrepared contact pair)
    exact holonomicGaugeCurvature_coordinate_contDiff
      ECPrepared ecPrepared_smooth pair

private theorem fixedMatterParameter_contDiff :
    ContDiff ℝ ∞ fun contact =>
      coframeMatterActionParameterOfField (FixedField contact) := by
  have scalarRegular : ContDiff ℝ ∞ ECPrepared.scalar :=
    ecPrepared_smooth.2.2.2.2.2.2.1
  have scalarDerivativeRegular : ContDiff ℝ ∞ fun contact =>
      holonomicScalarCovariantDerivative ECPrepared contact := by
    apply contDiff_pi'
    intro direction
    exact holonomicScalarCovariantDerivative_contDiff_local
      ECPrepared ecPrepared_smooth direction
  have matterRegular : ContDiff ℝ ∞ fun contact =>
      matterCoordinateEquiv (ECPrepared.matter contact) :=
    ecPrepared_smooth.2.2.2.2.2.2.2.1
  have matterDerivativeRegular : ContDiff ℝ ∞ fun contact =>
      fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative ECPrepared contact direction) := by
    apply contDiff_pi'
    intro direction
    exact holonomicMatterCovariantDerivative_coordinate_contDiff_local
      ECPrepared ecPrepared_smooth direction
  have conjugateRegular : ContDiff ℝ ∞ fun contact =>
      matterDualCoordinates (ECPrepared.conjugateMatter contact) :=
    holonomicConjugateMatterCoordinates_contDiff ECPrepared ecPrepared_smooth
  change ContDiff ℝ ∞ fun contact =>
    (ECPrepared.scalar contact,
      holonomicScalarCovariantDerivative ECPrepared contact,
      matterCoordinateEquiv (ECPrepared.matter contact),
      (fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative ECPrepared contact direction)),
      matterDualCoordinates (ECPrepared.conjugateMatter contact))
  exact scalarRegular.prodMk
    (scalarDerivativeRegular.prodMk
      (matterRegular.prodMk
        (matterDerivativeRegular.prodMk conjugateRegular)))

private theorem profileField_eq_fixedField (contact : BasePoint) :
    diracDualFormNativeECNormalContactField
        (cartanECCauchyTemporalProfileInput Source Prepared contact) =
      FixedField contact := by
  unfold diracDualFormNativeECNormalContactField
    diracDualFormNativeECNormalPreparedActual FixedField
    cartanECCauchyTemporalProfileInput
  rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
  rw [fullyRecenterHolonomicConfiguration_pointField_origin_unconditional]
  rfl

private theorem profileGaugeEuler_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun contact =>
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Prepared contact))
        (coframeCoordinateDirection row column) := by
  rw [show
    (fun contact =>
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Prepared contact))
        (coframeCoordinateDirection row column)) =
      fun contact =>
        diracDualFormNativeCoframeGaugeEulerCovector Source
          (FixedField contact) (coframeCoordinateDirection row column) by
    funext contact
    rw [profileField_eq_fixedField]]
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_infty
    Source FixedField contact
    fixedGaugeParameter_contDiff.contDiffAt
    fixedField_coframe_contDiff.contDiffAt
    (by
      change Matrix.det (Prepared.coframe contact) ≠ 0
      exact
        fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate
          contact)
    row column

private theorem profileMatterEuler_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun contact =>
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Prepared contact))
        (coframeCoordinateDirection row column) := by
  rw [show
    (fun contact =>
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Prepared contact))
        (coframeCoordinateDirection row column)) =
      fun contact =>
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (FixedField contact) (coframeCoordinateDirection row column) by
    funext contact
    rw [profileField_eq_fixedField]]
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_infty
    Source 0 FixedField contact
    fixedMatterParameter_contDiff.contDiffAt
    fixedField_coframe_contDiff.contDiffAt
    (by
      change Matrix.det (Prepared.coframe contact) ≠ 0
      exact
        fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate
          contact)
    row column

private theorem profileLoad_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun contact =>
      diracDualFormNativeIdentityECLoad Source
        (cartanECCauchyTemporalProfileInput Source Prepared contact)
        (coframeCoordinateDirection row column) := by
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  exact
    (contDiff_const.add
      (profileGaugeEuler_coordinate_contDiff row column)).add
      (profileMatterEuler_coordinate_contDiff row column)

private theorem profileCurrentCurvature_eq_base (contact : BasePoint) :
    diracDualFormNativeECCauchyCurrentCurvature
        (cartanECCauchyTemporalProfileInput Source Prepared contact) =
      holonomicGravityCurvature ECPrepared contact := by
  unfold diracDualFormNativeECCauchyCurrentCurvature
    diracDualFormNativeECNormalPreparedActual
    cartanECCauchyTemporalProfileInput ECPrepared
  change
    holonomicGravityCurvature
        (fullyRecenterHolonomicConfiguration Base contact) 0 =
      holonomicGravityCurvature
        (restrictHolonomicConfigurationToIIPlus Base) contact
  change
    holonomicGravityCurvature
        (fullyRecenterHolonomicConfiguration Base contact) 0 =
      holonomicGravityCurvature Base contact
  exact fullyRecenterHolonomicConfiguration_gravityCurvature_origin_unconditional
    Base contact

private theorem profileCurrentCurvature_contDiff :
    ContDiff ℝ ∞ fun contact =>
      diracDualFormNativeECCauchyCurrentCurvature
        (cartanECCauchyTemporalProfileInput Source Prepared contact) := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro spacetimePair
  rw [show
    (fun contact =>
      diracDualFormNativeECCauchyCurrentCurvature
        (cartanECCauchyTemporalProfileInput Source Prepared contact)
        internalPair spacetimePair) =
      fun contact =>
        holonomicGravityCurvature ECPrepared contact
          internalPair spacetimePair by
    funext contact
    rw [profileCurrentCurvature_eq_base]]
  exact holonomicGravityCurvature_component_contDiff
    ECPrepared ecPrepared_smooth internalPair spacetimePair

private theorem profileDesiredEvolution_contDiff :
    ContDiff ℝ ∞ fun contact =>
      diracDualFormNativeECDesiredEvolutionObservation Source
        (cartanECCauchyTemporalProfileInput Source Prepared contact) := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro direction
  unfold diracDualFormNativeECDesiredEvolutionObservation
    identityECSpatialCoframeCoordinatesOfCovector
  exact (profileLoad_coordinate_contDiff row direction.succ).neg

private theorem profileIncrement_contDiff :
    ContDiff ℝ ∞ fun contact =>
      diracDualFormNativeECTemporalCurvatureIncrement Source
        (cartanECCauchyTemporalProfileInput Source Prepared contact) := by
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact diracDualFormNativeECTemporalCurvatureIncrement_contDiffAt
    Source
    (fun point =>
      cartanECCauchyTemporalProfileInput Source Prepared point)
    contact profileCurrentCurvature_contDiff.contDiffAt
      profileDesiredEvolution_contDiff.contDiffAt

private theorem correctionProfile_coordinate_contDiff
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiff ℝ ∞ fun contact =>
      cartanECCauchyTemporalConnectionCorrectionProfile Source Prepared contact
        formDirection internalPair := by
  fin_cases formDirection
  · exact contDiff_const
  · simpa [cartanECCauchyTemporalConnectionCorrectionProfile] using
      contDiff_pi.mp (contDiff_pi.mp profileIncrement_contDiff internalPair) 0
  · simpa [cartanECCauchyTemporalConnectionCorrectionProfile] using
      contDiff_pi.mp (contDiff_pi.mp profileIncrement_contDiff internalPair) 1
  · simpa [cartanECCauchyTemporalConnectionCorrectionProfile] using
      contDiff_pi.mp (contDiff_pi.mp profileIncrement_contDiff internalPair) 2

private theorem canonicalTimePrimitive_contDiff_of_contDiff
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile) :
    ContDiff ℝ ∞ (canonicalTimePrimitive profile) := by
  rw [contDiff_infty]
  intro order
  rw [contDiff_iff_contDiffAt]
  intro point
  apply canonicalTimePrimitive_contDiffAt_of_contDiffOn_segment_finite
    order profile Set.univ isOpen_univ
  · exact (regular.of_le
      (show ((((order + 1 : ℕ) : ℕ∞)) : ℕ∞ω) ≤
          ((⊤ : ℕ∞) : ℕ∞ω) from
        WithTop.coe_le_coe.mpr le_top)).contDiffOn
  · simp

private theorem correctionPrimitive_coordinate_contDiff
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      cartanECCauchyTemporalConnectionCorrectionPrimitive Source Prepared point
        formDirection internalPair := by
  exact canonicalTimePrimitive_contDiff_of_contDiff _
    (correctionProfile_coordinate_contDiff formDirection internalPair)

private def correctionConnectionLinearMap :
    LorentzBivectorOneForm →ₗ[ℝ] PointwiseLorentzSpinConnection where
  toFun := lorentzSkewConnectionOfBivectorOneForm
  map_add' := lorentzSkewConnectionOfBivectorOneForm_add
  map_smul' := lorentzSkewConnectionOfBivectorOneForm_smul

private theorem correctionConnection_contDiff :
    ContDiff ℝ ∞ fun point =>
      lorentzSkewConnectionOfBivectorOneForm
        (cartanECCauchyTemporalConnectionCorrectionPrimitive
          Source Prepared point) := by
  have primitiveRegular : ContDiff ℝ ∞
      (cartanECCauchyTemporalConnectionCorrectionPrimitive
        Source Prepared) := by
    apply contDiff_pi'
    intro formDirection
    apply contDiff_pi'
    intro internalPair
    exact correctionPrimitive_coordinate_contDiff
      formDirection internalPair
  exact correctionConnectionLinearMap.toContinuousLinearMap.contDiff.comp
    primitiveRegular

private theorem current_connection_smooth :
    ∀ direction internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        Current.gravityConnection point direction internalOut internalIn := by
  intro direction internalOut internalIn
  change ContDiff ℝ ∞ fun point =>
    (cartanECCauchyTemporalConnectedActual Source Prepared).gravityConnection
      point direction internalOut internalIn
  unfold cartanECCauchyTemporalConnectedActual
  dsimp only
  apply ContDiff.add
  · rw [contDiff_iff_contDiffAt]
    intro point
    exact cartanReactionRestart_connection_component_contDiffAt
      Source Prepared
      fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth point
      (fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate
        point)
      direction internalOut internalIn
  · exact contDiff_pi.mp
      (contDiff_pi.mp
        (contDiff_pi.mp correctionConnection_contDiff direction)
        internalOut)
      internalIn

theorem fixedP506L0CartanECConstraintCauchySafeGlobalActual_smooth :
    Current.Smooth := by
  have preparedSmooth : Prepared.Smooth :=
    fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth
  have coframeSmooth : ∀ row column,
      ContDiff ℝ ∞ fun point => Current.coframe point row column := by
    intro row column
    rw [fixedP506L0CartanECConstraintCauchySafeGlobalActual_coframe]
    exact preparedSmooth.1 row column
  have auxiliarySmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        Current.gravityAuxiliary point internalPair spacetimePair := by
    intro internalPair spacetimePair
    change ContDiff ℝ ∞ fun point =>
      physicalIIPlusBivector (Prepared.coframe point)
        internalPair spacetimePair
    have preparedCoframeSmooth : ContDiff ℝ ∞ Prepared.coframe := by
      apply contDiff_pi'
      intro row
      apply contDiff_pi'
      intro column
      exact preparedSmooth.1 row column
    exact contDiff_pi.mp
      (contDiff_pi.mp
        (physicalIIPlusBivector_contDiff.comp preparedCoframeSmooth)
        internalPair)
      spacetimePair
  have multiplierSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        Current.gravitySimplicityMultiplier point
          internalPair spacetimePair := by
    intro internalPair spacetimePair
    change ContDiff ℝ ∞ fun point =>
      formNativeGravityReactionField
        (cartanECCauchyTemporalConnectedActual Source Prepared)
        point internalPair spacetimePair
    exact formNativeGravityReactionField_component_contDiff
      (cartanECCauchyTemporalConnectedActual Source Prepared)
      current_connection_smooth auxiliarySmooth internalPair spacetimePair
  exact ⟨coframeSmooth, current_connection_smooth, auxiliarySmooth,
    multiplierSmooth,
    preparedSmooth.2.2.2.2.1,
    preparedSmooth.2.2.2.2.2.1,
    preparedSmooth.2.2.2.2.2.2.1,
    preparedSmooth.2.2.2.2.2.2.2.1,
    preparedSmooth.2.2.2.2.2.2.2.2⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalRegularity
