import H0mework.Physics.SynchronizedJoint.FixedLorentzGlobalActual
import H0mework.Physics.CoframeVariation.CoframeECCurvatureTargetLocalRegularity
import H0mework.Physics.CoframeVariation.CoframeGaugeEulerParameterContinuity
import H0mework.Physics.CoframeVariation.CoframeMatterEulerParameterContinuity
import H0mework.Physics.Coframe.CoframeGravityGaugeRegularity
import H0mework.Physics.Coframe.CoframeScalarMatterRegularity
import H0mework.Physics.Holonomic.HolonomicIdentityCoframeConjugateMatterActionResponse

/-!
# Fixed P506/L0 synchronized-section Lorentz profile regularity

The exact four-leg occurrence already fixes the synchronized spacetime
section before the Lorentz path is emitted.  This module reads the finite EC
profile from that one pre-path actual and proves it is `C¹` on all of
spacetime.  The proof consumes the base actual's generated smoothness and
global identity coframe; it accepts no target, residual, support, branch,
completed field, or regularity certificate for the output profile.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECCurvatureNormalSection
open StageNineDiracDualFormNativeCoframeECCurvatureTargetLocalRegularity
open StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCoframeMatterEulerParameterContinuity
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeWedge
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineTopologicalFourFormPairing

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance profileP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity.p286CoordinateIndexFintype

local instance profileMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Base : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual

private theorem pathBase_eq :
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathBase
        Source Input =
      Base := by
  unfold
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathBase
  exact
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_eq_actionWrite.symm

private abbrev PreparedBase : StageNineHolonomicConfiguration :=
  diracDualFormNativeCoframeECContactPreparedActual Base

private abbrev FixedField
    (contact : BasePoint) : StageNineContinuumPointField :=
  diracDualFormNativeCoframeECContactField Base contact

private theorem base_smooth : Base.Smooth :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_smooth

private theorem preparedBase_smooth : PreparedBase.Smooth :=
  restrictHolonomicConfigurationToIIPlus_smooth Base base_smooth

private theorem base_coframe_contDiff : ContDiff ℝ ∞ Base.coframe :=
  holonomicCoframe_contDiff Base base_smooth

private theorem fixedField_coframe_contDiff :
    ContDiff ℝ ∞ fun contact => (FixedField contact).coframe := by
  change ContDiff ℝ ∞ Base.coframe
  exact base_coframe_contDiff

private theorem fixedGaugeParameter_contDiff :
    ContDiff ℝ ∞ fun contact =>
      coframeGaugeActionParameterOfField (FixedField contact) := by
  apply ContDiff.prodMk
  · apply contDiff_pi'
    intro pair
    change ContDiff ℝ ∞ fun contact =>
      p286CoordinateEquiv (PreparedBase.gaugeAuxiliary contact pair)
    exact preparedBase_smooth.2.2.2.2.2.1 pair
  · apply contDiff_pi'
    intro pair
    change ContDiff ℝ ∞ fun contact =>
      p286CoordinateEquiv
        (holonomicGaugeCurvature PreparedBase contact pair)
    exact holonomicGaugeCurvature_coordinate_contDiff
      PreparedBase preparedBase_smooth pair

private theorem fixedMatterParameter_contDiff :
    ContDiff ℝ ∞ fun contact =>
      coframeMatterActionParameterOfField (FixedField contact) := by
  have scalarRegular : ContDiff ℝ ∞ PreparedBase.scalar :=
    preparedBase_smooth.2.2.2.2.2.2.1
  have scalarDerivativeRegular : ContDiff ℝ ∞ fun contact =>
      holonomicScalarCovariantDerivative PreparedBase contact := by
    apply contDiff_pi'
    intro direction
    exact holonomicScalarCovariantDerivative_contDiff_local
      PreparedBase preparedBase_smooth direction
  have matterRegular : ContDiff ℝ ∞ fun contact =>
      matterCoordinateEquiv (PreparedBase.matter contact) :=
    preparedBase_smooth.2.2.2.2.2.2.2.1
  have matterDerivativeRegular : ContDiff ℝ ∞ fun contact =>
      fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative PreparedBase contact direction) := by
    apply contDiff_pi'
    intro direction
    exact holonomicMatterCovariantDerivative_coordinate_contDiff_local
      PreparedBase preparedBase_smooth direction
  have conjugateRegular : ContDiff ℝ ∞ fun contact =>
      matterDualCoordinates (PreparedBase.conjugateMatter contact) := by
    exact holonomicConjugateMatterCoordinates_contDiff
      PreparedBase preparedBase_smooth
  change ContDiff ℝ ∞ fun contact =>
    (PreparedBase.scalar contact,
      holonomicScalarCovariantDerivative PreparedBase contact,
      matterCoordinateEquiv (PreparedBase.matter contact),
      (fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative PreparedBase contact direction)),
      matterDualCoordinates (PreparedBase.conjugateMatter contact))
  exact scalarRegular.prodMk
    (scalarDerivativeRegular.prodMk
      (matterRegular.prodMk
        (matterDerivativeRegular.prodMk conjugateRegular)))

private theorem profileField_eq_fixedField
    (contact : BasePoint) :
    diracDualFormNativeCoframeECContactField
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
          Source Input contact)
        0 =
      FixedField contact := by
  calc
    _ = diracDualFormNativeCoframeECContactField
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathBase
          Source Input)
        contact :=
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileField_eq_base
        Source Input contact
    _ = FixedField contact := by
      rw [pathBase_eq]

private theorem profileCoframe_eq_base
    (contact : BasePoint) :
    (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
      Source Input contact).coframe 0 =
      Base.coframe contact := by
  exact fullyRecenterHolonomicConfiguration_coframe_origin Base contact

private theorem profilePreparedCurvature_eq_base
    (contact : BasePoint) :
    holonomicGravityCurvature
        (diracDualFormNativeCoframeECContactPreparedActual
          (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
            Source Input contact))
        0 =
      holonomicGravityCurvature PreparedBase contact := by
  calc
    _ = holonomicGravityCurvature
        (diracDualFormNativeCoframeECContactPreparedActual
          (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathBase
            Source Input))
        contact :=
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfilePreparedCurvature_eq_base
        Source Input contact
    _ = holonomicGravityCurvature PreparedBase contact := by
      rw [pathBase_eq]

private theorem profileGaugeEuler_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ 1 fun contact =>
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (diracDualFormNativeCoframeECContactField
          (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
            Source Input contact)
          0)
        (coframeCoordinateDirection row column) := by
  rw [show
    (fun contact =>
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (diracDualFormNativeCoframeECContactField
          (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
            Source Input contact)
          0)
        (coframeCoordinateDirection row column)) =
      fun contact =>
        diracDualFormNativeCoframeGaugeEulerCovector Source
          (FixedField contact)
          (coframeCoordinateDirection row column) by
    funext contact
    rw [profileField_eq_fixedField]]
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact
    diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_one
      Source FixedField contact
      (fixedGaugeParameter_contDiff.contDiffAt.of_le
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
      (fixedField_coframe_contDiff.contDiffAt.of_le
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
      (by
        change Matrix.det (Base.coframe contact) ≠ 0
        rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_coframe_eq_one]
        norm_num)
      row column

private theorem profileMatterEuler_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ 1 fun contact =>
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (diracDualFormNativeCoframeECContactField
          (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
            Source Input contact)
          0)
        (coframeCoordinateDirection row column) := by
  rw [show
    (fun contact =>
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (diracDualFormNativeCoframeECContactField
          (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
            Source Input contact)
          0)
        (coframeCoordinateDirection row column)) =
      fun contact =>
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (FixedField contact)
          (coframeCoordinateDirection row column) by
    funext contact
    rw [profileField_eq_fixedField]]
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact
    diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_one
      Source 0 FixedField contact
      (fixedMatterParameter_contDiff.contDiffAt.of_le
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
      (fixedField_coframe_contDiff.contDiffAt.of_le
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
      (by
        change Matrix.det (Base.coframe contact) ≠ 0
        rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_coframe_eq_one]
        norm_num)
      row column

private theorem profileLoad_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ 1 fun contact =>
      (-diracDualFormNativeCoframeECContactLoad Source
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
          Source Input contact)
        0) (coframeCoordinateDirection row column) := by
  have geometryRegular : ContDiff ℝ 1 fun contact =>
      coframeDiracDualECCurvatureObservation
        ((completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
          Source Input contact).coframe 0)
        (gravityInternalPairVarianceNormalization
          (coframeWedge
            ((completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
              Source Input contact).coframe 0)))
        (coframeCoordinateDirection row column) := by
    rw [show
      (fun contact =>
        coframeDiracDualECCurvatureObservation
          ((completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
            Source Input contact).coframe 0)
          (gravityInternalPairVarianceNormalization
            (coframeWedge
              ((completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
                Source Input contact).coframe 0)))
          (coframeCoordinateDirection row column)) =
        fun _ =>
          coframeDiracDualECCurvatureObservation
            (1 : LorentzianCoframe)
            (gravityInternalPairVarianceNormalization
              (coframeWedge (1 : LorentzianCoframe)))
            (coframeCoordinateDirection row column) by
      funext contact
      rw [profileCoframe_eq_base,
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_coframe_eq_one]]
    exact contDiff_const
  unfold diracDualFormNativeCoframeECContactLoad
  simp only [neg_apply, add_apply]
  exact
    (geometryRegular.add
      (profileGaugeEuler_coordinate_contDiff row column) |>.add
        (profileMatterEuler_coordinate_contDiff row column)).neg

private theorem profileTarget_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ 1 fun contact =>
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileTarget
        Source Input contact internalPair spacetimePair := by
  rw [contDiff_iff_contDiffAt]
  intro center
  unfold
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileTarget
    diracDualFormNativeCoframeECContactCurvatureTarget
  apply coframeDiracDualECCurvatureTarget_component_contDiffAt
    (n := 1)
  · rw [show
      (fun contact =>
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
          Source Input contact).coframe 0) = Base.coframe by
      funext contact
      exact profileCoframe_eq_base contact]
    exact base_coframe_contDiff.contDiffAt.of_le
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  · apply contDiffAt_pi'
    intro targetInternalPair
    apply contDiffAt_pi'
    intro targetSpacetimePair
    rw [show
      (fun contact =>
        holonomicGravityCurvature
          (diracDualFormNativeCoframeECContactPreparedActual
            (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileInput
              Source Input contact))
          0 targetInternalPair targetSpacetimePair) =
        fun contact =>
          holonomicGravityCurvature PreparedBase contact
            targetInternalPair targetSpacetimePair by
      funext contact
      rw [profilePreparedCurvature_eq_base]]
    exact
      (holonomicGravityCurvature_component_contDiff
        PreparedBase preparedBase_smooth targetInternalPair
          targetSpacetimePair).contDiffAt.of_le
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  · intro row column
    exact (profileLoad_coordinate_contDiff row column).contDiffAt
  · rw [profileCoframe_eq_base,
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_coframe_eq_one]
    apply coframeTwoFormWedgeScale_ne_zero
    rw [Matrix.det_transpose]
    norm_num

private theorem profileOrigin_component_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ 1 fun contact =>
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileOrigin
        Source Input contact formDirection internalOut internalIn := by
  rw [show
    (fun contact =>
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileOrigin
        Source Input contact formDirection internalOut internalIn) =
      fun contact =>
        Base.gravityConnection contact formDirection internalOut internalIn by
    funext contact
    rw [completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileOrigin_eq_base]
    rw [pathBase_eq]]
  exact (base_smooth.2.1 formDirection internalOut internalIn).of_le
    (show (1 : WithTop ℕ∞) ≤ ∞ by simp)

private theorem normalizedDerivative_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ 1 fun contact =>
      normalizedDerivativeBivector
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileOrigin
          Source Input contact)
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileTarget
          Source Input contact)
        internalPair spacetimePair := by
  unfold normalizedDerivativeBivector originLorentzBracketCurvature
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine contDiff_const.mul
    ((profileTarget_component_contDiff internalPair spacetimePair).sub
      (contDiff_const.mul ?_))
  apply ContDiff.sum
  intro middle _
  exact
    ((profileOrigin_component_contDiff
      (pairFirst spacetimePair) (pairFirst internalPair) middle).mul
      (profileOrigin_component_contDiff
        (pairSecond spacetimePair) middle (pairSecond internalPair))).sub
      ((profileOrigin_component_contDiff
        (pairSecond spacetimePair) (pairFirst internalPair) middle).mul
        (profileOrigin_component_contDiff
          (pairFirst spacetimePair) middle (pairSecond internalPair)))

private theorem loweredConnectionFirstJet_contDiff
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    ContDiff ℝ 1 fun contact =>
      completeJointActionSpacetimeSectionCartanECSynchronizedLoweredConnectionFirstJet
        Source Input contact derivativeDirection formDirection internalPair := by
  rw [show
    (fun contact =>
      completeJointActionSpacetimeSectionCartanECSynchronizedLoweredConnectionFirstJet
        Source Input contact derivativeDirection formDirection internalPair) =
      fun contact =>
        ∑ spacetimePair : Fin 6,
          normalizedDerivativeBivector
              (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileOrigin
                Source Input contact)
              (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileTarget
                Source Input contact)
              internalPair spacetimePair *
            orientedLorentzBivectorBasisCoefficient spacetimePair
              derivativeDirection formDirection by
    funext contact
    exact
      completeJointActionSpacetimeSectionCartanECSynchronizedLoweredConnectionFirstJet_normalForm
        Source Input contact derivativeDirection formDirection internalPair]
  apply ContDiff.sum
  intro spacetimePair _
  exact
    (normalizedDerivative_component_contDiff
      internalPair spacetimePair).mul contDiff_const

@[fun_prop] private theorem lorentzJetOneForm_contDiff
    (derivativeDirection : LorentzianIndex) :
    ContDiff ℝ 1 fun contact =>
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetOneForm
        Source Input contact derivativeDirection := by
  apply contDiff_pi'
  intro formDirection
  apply contDiff_pi'
  intro internalPair
  exact loweredConnectionFirstJet_contDiff
    derivativeDirection formDirection internalPair

/-- The exact action-owned Lorentz profile of the fixed P506/L0 occurrence
is `C¹` on all spacetime. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM_contDiff :
    ContDiff ℝ 1
      (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor) := by
  change ContDiff ℝ 1
    (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
      Source Input)
  unfold
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
  apply ContDiff.sum
  intro derivativeDirection _
  fun_prop (disch := exact lorentzJetOneForm_contDiff derivativeDirection)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileRegularity
