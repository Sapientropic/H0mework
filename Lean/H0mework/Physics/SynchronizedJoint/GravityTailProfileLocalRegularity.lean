import H0mework.Physics.CartanAction.CartanAlgebraicSmoothness
import H0mework.Physics.SynchronizedJoint.GravityTailJointPathOperator
import H0mework.Physics.CoframeVariation.CoframeECCurvatureTargetLocalRegularity
import H0mework.Physics.CoframeVariation.CoframeGaugeEulerParameterContinuity
import H0mework.Physics.CoframeVariation.CoframeMatterEulerParameterContinuity
import H0mework.Physics.Coframe.CoframeGravityGaugeRegularity
import H0mework.Physics.Holonomic.CoframeRegularity
import H0mework.Physics.Coframe.CoframeScalarMatterRegularity
import H0mework.Physics.Holonomic.HolonomicIdentityCoframeConjugateMatterActionResponse
import H0mework.Physics.Coframe.LinearPlebanskiCoframeActionPrincipal

/-!
# Local regularity of the synchronized gravity-tail action profile

A smooth source/current gravity base and one nondegenerate contact suffice to
make both occurrence-native action one-forms continuous at that contact.  The
theorems are generic in the source/current and expose no target field,
residual, support, branch, or completion payload.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanECSynchronizedGravityTailProfileLocalRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanTorsionThreeFormEquiv
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanAlgebraicSmoothness
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECCurvatureTargetLocalRegularity
open StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity
open StageNineDiracDualFormNativeCoframeMatterEulerParameterContinuity
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
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
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineLorentzConnectionVariation
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance (priority := high) gravityTailBasePointNormedAddCommGroup :
    NormedAddCommGroup BasePoint :=
  PiLp.normedAddCommGroup 2 (fun _ : LorentzianIndex => ℝ)

local instance (priority := high) gravityTailBasePointNormedSpace :
    NormedSpace ℝ BasePoint :=
  PiLp.normedSpace 2 ℝ (fun _ : LorentzianIndex => ℝ)

local instance gravityTailP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance gravityTailP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance gravityTailP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

local instance gravityTailMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev Base
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase source current

private abbrev PreparedBase
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeCoframeECContactPreparedActual (Base source current)

private def FixedField
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineContinuumPointField :=
  diracDualFormNativeCoframeECContactField (Base source current) contact

private theorem preparedBase_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth) :
    (PreparedBase source current).Smooth :=
  restrictHolonomicConfigurationToIIPlus_smooth
    (Base source current) baseSmooth

private theorem fixedGaugeParameter_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth) :
    ContDiff ℝ ∞ fun contact =>
      coframeGaugeActionParameterOfField (FixedField source current contact) := by
  let prepared := PreparedBase source current
  have smooth : prepared.Smooth := preparedBase_smooth source current baseSmooth
  apply ContDiff.prodMk
  · apply contDiff_pi'
    intro pair
    change ContDiff ℝ ∞ fun contact =>
      p286CoordinateEquiv (prepared.gaugeAuxiliary contact pair)
    exact smooth.2.2.2.2.2.1 pair
  · apply contDiff_pi'
    intro pair
    change ContDiff ℝ ∞ fun contact =>
      p286CoordinateEquiv (holonomicGaugeCurvature prepared contact pair)
    exact holonomicGaugeCurvature_coordinate_contDiff prepared smooth pair

private theorem fixedMatterParameter_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth) :
    ContDiff ℝ ∞ fun contact =>
      coframeMatterActionParameterOfField (FixedField source current contact) := by
  let prepared := PreparedBase source current
  have smooth : prepared.Smooth := preparedBase_smooth source current baseSmooth
  have scalarDerivativeRegular : ContDiff ℝ ∞ fun contact =>
      holonomicScalarCovariantDerivative prepared contact := by
    apply contDiff_pi'
    intro direction
    exact holonomicScalarCovariantDerivative_contDiff_local
      prepared smooth direction
  have matterDerivativeRegular : ContDiff ℝ ∞ fun contact =>
      fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative prepared contact direction) := by
    apply contDiff_pi'
    intro direction
    exact holonomicMatterCovariantDerivative_coordinate_contDiff_local
      prepared smooth direction
  change ContDiff ℝ ∞ fun contact =>
    (prepared.scalar contact,
      holonomicScalarCovariantDerivative prepared contact,
      matterCoordinateEquiv (prepared.matter contact),
      (fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative prepared contact direction)),
      matterDualCoordinates (prepared.conjugateMatter contact))
  exact smooth.2.2.2.2.2.2.1.prodMk
    (scalarDerivativeRegular.prodMk
      (smooth.2.2.2.2.2.2.2.1.prodMk
        (matterDerivativeRegular.prodMk
          (holonomicConjugateMatterCoordinates_contDiff
            prepared smooth))))

private theorem profileGaugeEuler_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ 1 (fun center =>
      diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeCoframeECContactField
          (cartanECSynchronizedGravityTailProfileInput
            source current center) 0)
        (coframeCoordinateDirection row column)) contact := by
  rw [show
    (fun center =>
      diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeCoframeECContactField
          (cartanECSynchronizedGravityTailProfileInput
            source current center) 0)
        (coframeCoordinateDirection row column)) =
      fun center =>
        diracDualFormNativeCoframeGaugeEulerCovector source
          (FixedField source current center)
          (coframeCoordinateDirection row column) by
    funext center
    rw [cartanECSynchronizedGravityTailProfileField_eq_base]
    rfl]
  exact diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_one
    source (FixedField source current) contact
    ((fixedGaugeParameter_contDiff source current baseSmooth).contDiffAt.of_le
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
    ((holonomicCoframe_contDiff (Base source current) baseSmooth
      ).contDiffAt.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
    nondegenerate row column

private theorem profileMatterEuler_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ 1 (fun center =>
      diracDualFormNativeCoframeMatterEulerCovector source 0
        (diracDualFormNativeCoframeECContactField
          (cartanECSynchronizedGravityTailProfileInput
            source current center) 0)
        (coframeCoordinateDirection row column)) contact := by
  rw [show
    (fun center =>
      diracDualFormNativeCoframeMatterEulerCovector source 0
        (diracDualFormNativeCoframeECContactField
          (cartanECSynchronizedGravityTailProfileInput
            source current center) 0)
        (coframeCoordinateDirection row column)) =
      fun center =>
        diracDualFormNativeCoframeMatterEulerCovector source 0
          (FixedField source current center)
          (coframeCoordinateDirection row column) by
    funext center
    rw [cartanECSynchronizedGravityTailProfileField_eq_base]
    rfl]
  exact diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_one
    source 0 (FixedField source current) contact
    ((fixedMatterParameter_contDiff source current baseSmooth).contDiffAt.of_le
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
    ((holonomicCoframe_contDiff (Base source current) baseSmooth
      ).contDiffAt.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
    nondegenerate row column

private theorem profileLoad_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ 1 (fun center =>
      (-diracDualFormNativeCoframeECContactLoad source
        (cartanECSynchronizedGravityTailProfileInput source current center) 0)
        (coframeCoordinateDirection row column)) contact := by
  unfold diracDualFormNativeCoframeECContactLoad
  simp only [neg_apply, add_apply]
  apply ContDiffAt.neg
  apply ContDiffAt.add
  · apply ContDiffAt.add
    · apply coframeDiracDualECCurvatureObservation_coordinate_contDiffAt
        (fun center =>
          (cartanECSynchronizedGravityTailProfileInput
            source current center).coframe 0)
        (fun center =>
          gravityInternalPairVarianceNormalization
            (coframeWedge
              ((cartanECSynchronizedGravityTailProfileInput
                source current center).coframe 0)))
        contact
      · rw [show
          (fun center =>
            (cartanECSynchronizedGravityTailProfileInput
              source current center).coframe 0) =
            (Base source current).coframe by
          funext center
          exact fullyRecenterHolonomicConfiguration_coframe_origin
            (Base source current) center]
        exact (holonomicCoframe_contDiff
          (Base source current) baseSmooth).contDiffAt.of_le
            (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
      · apply contDiffAt_pi'
        intro internalPair
        apply contDiffAt_pi'
        intro spacetimePair
        rw [show
          (fun center =>
            gravityInternalPairVarianceNormalization
              (coframeWedge
                ((cartanECSynchronizedGravityTailProfileInput
                  source current center).coframe 0))
              internalPair spacetimePair) =
            fun center =>
              gravityInternalPairVarianceNormalization
                (coframeWedge ((Base source current).coframe center))
                internalPair spacetimePair by
          funext center
          unfold cartanECSynchronizedGravityTailProfileInput
          rw [fullyRecenterHolonomicConfiguration_coframe_origin]]
        simp only [gravityInternalPairVarianceNormalization_apply]
        unfold coframeWedge
        have coframeComponent
            (row column : LorentzianIndex) :
            ContDiffAt ℝ 1 (fun center =>
              (Base source current).coframe center row column) contact :=
          (baseSmooth.1 row column).contDiffAt.of_le
            (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
        fun_prop
    · exact profileGaugeEuler_coordinate_contDiffAt
        source current baseSmooth contact nondegenerate row column
  · exact profileMatterEuler_coordinate_contDiffAt
      source current baseSmooth contact nondegenerate row column

private theorem profileTarget_component_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ 1 (fun center =>
      cartanECSynchronizedGravityTailProfileTarget
        source current center internalPair spacetimePair) contact := by
  unfold cartanECSynchronizedGravityTailProfileTarget
    diracDualFormNativeCoframeECContactCurvatureTarget
  apply coframeDiracDualECCurvatureTarget_component_contDiffAt (n := 1)
  · rw [show
      (fun center =>
        (cartanECSynchronizedGravityTailProfileInput
          source current center).coframe 0) =
        (Base source current).coframe by
      funext center
      exact fullyRecenterHolonomicConfiguration_coframe_origin
        (Base source current) center]
    exact (holonomicCoframe_contDiff
      (Base source current) baseSmooth).contDiffAt.of_le
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  · apply contDiffAt_pi'
    intro targetInternalPair
    apply contDiffAt_pi'
    intro targetSpacetimePair
    rw [show
      (fun center =>
        holonomicGravityCurvature
          (diracDualFormNativeCoframeECContactPreparedActual
            (cartanECSynchronizedGravityTailProfileInput
              source current center)) 0
          targetInternalPair targetSpacetimePair) =
        fun center =>
          holonomicGravityCurvature (PreparedBase source current) center
            targetInternalPair targetSpacetimePair by
      funext center
      rw [cartanECSynchronizedGravityTailProfilePreparedCurvature_eq_base]]
    exact
      (holonomicGravityCurvature_component_contDiff
        (PreparedBase source current)
        (preparedBase_smooth source current baseSmooth)
        targetInternalPair targetSpacetimePair).contDiffAt.of_le
          (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  · intro row column
    exact profileLoad_coordinate_contDiffAt
      source current baseSmooth contact nondegenerate row column
  · unfold cartanECSynchronizedGravityTailProfileInput
    rw [fullyRecenterHolonomicConfiguration_coframe_origin]
    apply coframeTwoFormWedgeScale_ne_zero
    rw [Matrix.det_transpose]
    exact nondegenerate

private theorem normalizedDerivative_component_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ 1 (fun center =>
      normalizedDerivativeBivector
        (cartanECSynchronizedGravityTailProfileOrigin
          source current center)
        (cartanECSynchronizedGravityTailProfileTarget
          source current center)
        internalPair spacetimePair) contact := by
  unfold normalizedDerivativeBivector originLorentzBracketCurvature
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine contDiffAt_const.mul
    ((profileTarget_component_contDiffAt source current baseSmooth contact
      nondegenerate internalPair spacetimePair).sub
      (contDiffAt_const.mul ?_))
  apply ContDiffAt.sum
  intro middle _
  have originComponent
      (formDirection internalOut internalIn : LorentzianIndex) :
      ContDiffAt ℝ 1 (fun center =>
        cartanECSynchronizedGravityTailProfileOrigin source current center
          formDirection internalOut internalIn) contact := by
    rw [show
      (fun center =>
        cartanECSynchronizedGravityTailProfileOrigin source current center
          formDirection internalOut internalIn) =
        fun center =>
          (Base source current).gravityConnection center
            formDirection internalOut internalIn by
      funext center
      rw [cartanECSynchronizedGravityTailProfileOrigin_eq_base]]
    exact (baseSmooth.2.1 formDirection internalOut internalIn
      ).contDiffAt.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  exact
    ((originComponent (pairFirst spacetimePair)
      (pairFirst internalPair) middle).mul
      (originComponent (pairSecond spacetimePair)
        middle (pairSecond internalPair))).sub
      ((originComponent (pairSecond spacetimePair)
        (pairFirst internalPair) middle).mul
        (originComponent (pairFirst spacetimePair)
          middle (pairSecond internalPair)))

private theorem loweredConnectionFirstJet_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    ContDiffAt ℝ 1 (fun center =>
      cartanECSynchronizedGravityTailLoweredConnectionFirstJet
        source current center derivativeDirection formDirection internalPair)
      contact := by
  rw [show
    (fun center =>
      cartanECSynchronizedGravityTailLoweredConnectionFirstJet
        source current center derivativeDirection formDirection internalPair) =
      fun center =>
        ∑ spacetimePair : Fin 6,
          normalizedDerivativeBivector
              (cartanECSynchronizedGravityTailProfileOrigin
                source current center)
              (cartanECSynchronizedGravityTailProfileTarget
                source current center)
              internalPair spacetimePair *
            orientedLorentzBivectorBasisCoefficient spacetimePair
              derivativeDirection formDirection by
    funext center
    exact cartanECSynchronizedGravityTailLoweredConnectionFirstJet_normalForm
      source current center derivativeDirection formDirection internalPair]
  apply ContDiffAt.sum
  intro spacetimePair _
  exact
    (normalizedDerivative_component_contDiffAt source current baseSmooth
      contact nondegenerate internalPair spacetimePair).mul contDiffAt_const

/-- The exact Lorentz action one-form is locally continuous wherever the
generated gravity base is smooth and its coframe is nondegenerate. -/
theorem cartanECSynchronizedGravityTailLorentzJetCLM_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0) :
    ContDiffAt ℝ 1
      (cartanECSynchronizedGravityTailJetCLM source current) contact := by
  unfold cartanECSynchronizedGravityTailJetCLM
  apply ContDiffAt.sum
  intro derivativeDirection _
  have oneFormRegular : ContDiffAt ℝ 1 (fun center =>
      cartanECSynchronizedGravityTailJetOneForm
        source current center derivativeDirection) contact := by
    apply contDiffAt_pi'
    intro formDirection
    apply contDiffAt_pi'
    intro internalPair
    exact
      (loweredConnectionFirstJet_contDiffAt source current baseSmooth contact
        nondegenerate derivativeDirection formDirection internalPair).of_le
        (by norm_num)
  fun_prop

private theorem baseSpinResponse_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0) :
    ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponseAt source (Base source current))
      contact := by
  have outer :=
    diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
      source (Base source current) baseSmooth contact
      ((Base source current).coframe contact) nondegenerate
  have inner : ContDiffAt ℝ ∞
      (fun center : BasePoint =>
        (center, (Base source current).coframe center)) contact :=
    contDiffAt_id.prodMk
      (holonomicCoframe_contDiff (Base source current) baseSmooth).contDiffAt
  have composed := outer.comp contact inner
  rw [show
    diracDualFormNativeActionSpinResponseAt source (Base source current) =
      fun center =>
        diracDualFormNativeActionSpinResponsePointCoframe
          source (Base source current)
          (center, (Base source current).coframe center) by
    funext center
    exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
      source (Base source current) center]
  exact composed

private theorem baseCartanTorsion_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (spacetimePair : Fin 6) (internal : LorentzianIndex) :
    ContDiffAt ℝ ∞ (fun center =>
      diracDualFormNativeActionCartanTorsionAt
        source (Base source current) center spacetimePair internal) contact := by
  let response := diracDualFormNativeActionSpinResponseAt
    source (Base source current) contact
  let carrier := fun center : BasePoint =>
    ((Base source current).coframe center,
      diracDualFormNativeActionSpinResponseAt
        source (Base source current) center)
  have outer := cartanTorsionOfThreeForm_component_contDiffAt
    ((Base source current).coframe contact) response nondegenerate
    spacetimePair internal
  have inner : ContDiffAt ℝ ∞ carrier contact :=
    (holonomicCoframe_contDiff
      (Base source current) baseSmooth).contDiffAt.prodMk
        (baseSpinResponse_contDiffAt source current baseSmooth
          contact nondegenerate)
  change ContDiffAt ℝ ∞
    ((fun data : LorentzianCoframe × PhysicalBivectorThreeForm =>
      cartanTorsionOfThreeForm data.1 data.2 spacetimePair internal) ∘
      carrier) contact
  exact outer.comp contact inner

private theorem profileCoframeDerivative_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    ContDiffAt ℝ 1 (fun center =>
      (cartanECSynchronizedGravityTailProfileCoframeFirstJet
        source current center).derivative
          derivativeDirection internal coordinate) contact := by
  rw [show
    (fun center =>
      (cartanECSynchronizedGravityTailProfileCoframeFirstJet
        source current center).derivative
          derivativeDirection internal coordinate) =
      fun center =>
        -coframeConnectionAction
            ((Base source current).gravityConnection center)
            derivativeDirection ((Base source current).coframe center)
            internal coordinate +
          ((1 : ℝ) / 2) *
            orderedCartanTorsionComponent
              (diracDualFormNativeActionCartanTorsionAt
                source (Base source current) center)
              internal derivativeDirection coordinate by
    funext center
    exact
      cartanECSynchronizedGravityTailProfileCoframeFirstJet_derivative_normalForm
        source current center derivativeDirection internal coordinate]
  unfold coframeConnectionAction orderedCartanTorsionComponent
  apply ContDiffAt.add
  · apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro middle _
    exact
      ((baseSmooth.2.1 derivativeDirection internal middle).contDiffAt.mul
        (contDiff_pi.mp
          (contDiff_pi.mp
            (holonomicCoframe_contDiff (Base source current) baseSmooth)
            middle) coordinate).contDiffAt).of_le (by norm_num)
  · apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.sum
    intro spacetimePair _
    exact
      ((baseCartanTorsion_coordinate_contDiffAt source current baseSmooth
        contact nondegenerate spacetimePair internal).mul
        contDiffAt_const).of_le (by norm_num)

/-- Every coordinate of the exact coframe action one-form is locally
continuous under the same generated-base hypotheses. -/
theorem cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (internal coordinate : LorentzianIndex) :
    ContDiffAt ℝ 1 (fun center =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current center internal coordinate) contact := by
  unfold cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
    cartanECSynchronizedGravityTailCoframeJetOneForm
  apply ContDiffAt.sum
  intro derivativeDirection _
  have coefficientRegular :=
    profileCoframeDerivative_contDiffAt source current baseSmooth contact
      nondegenerate derivativeDirection internal coordinate
  fun_prop

/-! ## C-infinity upgrade for GL-valued gravity material -/

private theorem profileGaugeEuler_coordinate_contDiffAt_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ ∞ (fun center =>
      diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeCoframeECContactField
          (cartanECSynchronizedGravityTailProfileInput
            source current center) 0)
        (coframeCoordinateDirection row column)) contact := by
  rw [show
    (fun center =>
      diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeCoframeECContactField
          (cartanECSynchronizedGravityTailProfileInput
            source current center) 0)
        (coframeCoordinateDirection row column)) =
      fun center =>
        diracDualFormNativeCoframeGaugeEulerCovector source
          (FixedField source current center)
          (coframeCoordinateDirection row column) by
    funext center
    rw [cartanECSynchronizedGravityTailProfileField_eq_base]
    rfl]
  exact diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_infty
    source (FixedField source current) contact
    (fixedGaugeParameter_contDiff source current baseSmooth).contDiffAt
    (holonomicCoframe_contDiff
      (Base source current) baseSmooth).contDiffAt
    nondegenerate row column

private theorem profileMatterEuler_coordinate_contDiffAt_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ ∞ (fun center =>
      diracDualFormNativeCoframeMatterEulerCovector source 0
        (diracDualFormNativeCoframeECContactField
          (cartanECSynchronizedGravityTailProfileInput
            source current center) 0)
        (coframeCoordinateDirection row column)) contact := by
  rw [show
    (fun center =>
      diracDualFormNativeCoframeMatterEulerCovector source 0
        (diracDualFormNativeCoframeECContactField
          (cartanECSynchronizedGravityTailProfileInput
            source current center) 0)
        (coframeCoordinateDirection row column)) =
      fun center =>
        diracDualFormNativeCoframeMatterEulerCovector source 0
          (FixedField source current center)
          (coframeCoordinateDirection row column) by
    funext center
    rw [cartanECSynchronizedGravityTailProfileField_eq_base]
    rfl]
  exact diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_infty
    source 0 (FixedField source current) contact
    (fixedMatterParameter_contDiff source current baseSmooth).contDiffAt
    (holonomicCoframe_contDiff
      (Base source current) baseSmooth).contDiffAt
    nondegenerate row column

private theorem profileLoad_coordinate_contDiffAt_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ ∞ (fun center =>
      (-diracDualFormNativeCoframeECContactLoad source
        (cartanECSynchronizedGravityTailProfileInput source current center) 0)
        (coframeCoordinateDirection row column)) contact := by
  unfold diracDualFormNativeCoframeECContactLoad
  simp only [neg_apply, add_apply]
  apply ContDiffAt.neg
  apply ContDiffAt.add
  · apply ContDiffAt.add
    · apply coframeDiracDualECCurvatureObservation_coordinate_contDiffAt
        (fun center =>
          (cartanECSynchronizedGravityTailProfileInput
            source current center).coframe 0)
        (fun center =>
          gravityInternalPairVarianceNormalization
            (coframeWedge
              ((cartanECSynchronizedGravityTailProfileInput
                source current center).coframe 0)))
        contact
      · rw [show
          (fun center =>
            (cartanECSynchronizedGravityTailProfileInput
              source current center).coframe 0) =
            (Base source current).coframe by
          funext center
          exact fullyRecenterHolonomicConfiguration_coframe_origin
            (Base source current) center]
        exact (holonomicCoframe_contDiff
          (Base source current) baseSmooth).contDiffAt
      · apply contDiffAt_pi'
        intro internalPair
        apply contDiffAt_pi'
        intro spacetimePair
        rw [show
          (fun center =>
            gravityInternalPairVarianceNormalization
              (coframeWedge
                ((cartanECSynchronizedGravityTailProfileInput
                  source current center).coframe 0))
              internalPair spacetimePair) =
            fun center =>
              gravityInternalPairVarianceNormalization
                (coframeWedge ((Base source current).coframe center))
                internalPair spacetimePair by
          funext center
          unfold cartanECSynchronizedGravityTailProfileInput
          rw [fullyRecenterHolonomicConfiguration_coframe_origin]]
        simp only [gravityInternalPairVarianceNormalization_apply]
        unfold coframeWedge
        have coframeComponent
            (targetRow targetColumn : LorentzianIndex) :
            ContDiffAt ℝ ∞ (fun center =>
              (Base source current).coframe center targetRow targetColumn)
              contact :=
          (baseSmooth.1 targetRow targetColumn).contDiffAt
        fun_prop
    · exact profileGaugeEuler_coordinate_contDiffAt_infty
        source current baseSmooth contact nondegenerate row column
  · exact profileMatterEuler_coordinate_contDiffAt_infty
      source current baseSmooth contact nondegenerate row column

private theorem profileTarget_component_contDiffAt_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ ∞ (fun center =>
      cartanECSynchronizedGravityTailProfileTarget
        source current center internalPair spacetimePair) contact := by
  unfold cartanECSynchronizedGravityTailProfileTarget
    diracDualFormNativeCoframeECContactCurvatureTarget
  apply coframeDiracDualECCurvatureTarget_component_contDiffAt (n := ∞)
  · rw [show
      (fun center =>
        (cartanECSynchronizedGravityTailProfileInput
          source current center).coframe 0) =
        (Base source current).coframe by
      funext center
      exact fullyRecenterHolonomicConfiguration_coframe_origin
        (Base source current) center]
    exact (holonomicCoframe_contDiff
      (Base source current) baseSmooth).contDiffAt
  · apply contDiffAt_pi'
    intro targetInternalPair
    apply contDiffAt_pi'
    intro targetSpacetimePair
    rw [show
      (fun center =>
        holonomicGravityCurvature
          (diracDualFormNativeCoframeECContactPreparedActual
            (cartanECSynchronizedGravityTailProfileInput
              source current center)) 0
          targetInternalPair targetSpacetimePair) =
        fun center =>
          holonomicGravityCurvature (PreparedBase source current) center
            targetInternalPair targetSpacetimePair by
      funext center
      rw [cartanECSynchronizedGravityTailProfilePreparedCurvature_eq_base]]
    exact
      (holonomicGravityCurvature_component_contDiff
        (PreparedBase source current)
        (preparedBase_smooth source current baseSmooth)
        targetInternalPair targetSpacetimePair).contDiffAt
  · intro row column
    exact profileLoad_coordinate_contDiffAt_infty
      source current baseSmooth contact nondegenerate row column
  · unfold cartanECSynchronizedGravityTailProfileInput
    rw [fullyRecenterHolonomicConfiguration_coframe_origin]
    apply coframeTwoFormWedgeScale_ne_zero
    rw [Matrix.det_transpose]
    exact nondegenerate

private theorem normalizedDerivative_component_contDiffAt_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ ∞ (fun center =>
      normalizedDerivativeBivector
        (cartanECSynchronizedGravityTailProfileOrigin
          source current center)
        (cartanECSynchronizedGravityTailProfileTarget
          source current center)
        internalPair spacetimePair) contact := by
  unfold normalizedDerivativeBivector originLorentzBracketCurvature
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine contDiffAt_const.mul
    ((profileTarget_component_contDiffAt_infty source current baseSmooth contact
      nondegenerate internalPair spacetimePair).sub
      (contDiffAt_const.mul ?_))
  apply ContDiffAt.sum
  intro middle _
  have originComponent
      (formDirection internalOut internalIn : LorentzianIndex) :
      ContDiffAt ℝ ∞ (fun center =>
        cartanECSynchronizedGravityTailProfileOrigin source current center
          formDirection internalOut internalIn) contact := by
    rw [show
      (fun center =>
        cartanECSynchronizedGravityTailProfileOrigin source current center
          formDirection internalOut internalIn) =
        fun center =>
          (Base source current).gravityConnection center
            formDirection internalOut internalIn by
      funext center
      rw [cartanECSynchronizedGravityTailProfileOrigin_eq_base]]
    exact (baseSmooth.2.1 formDirection internalOut internalIn).contDiffAt
  exact
    ((originComponent (pairFirst spacetimePair)
      (pairFirst internalPair) middle).mul
      (originComponent (pairSecond spacetimePair)
        middle (pairSecond internalPair))).sub
      ((originComponent (pairSecond spacetimePair)
        (pairFirst internalPair) middle).mul
        (originComponent (pairFirst spacetimePair)
          middle (pairSecond internalPair)))

private theorem loweredConnectionFirstJet_contDiffAt_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    ContDiffAt ℝ ∞ (fun center =>
      cartanECSynchronizedGravityTailLoweredConnectionFirstJet
        source current center derivativeDirection formDirection internalPair)
      contact := by
  rw [show
    (fun center =>
      cartanECSynchronizedGravityTailLoweredConnectionFirstJet
        source current center derivativeDirection formDirection internalPair) =
      fun center =>
        ∑ spacetimePair : Fin 6,
          normalizedDerivativeBivector
              (cartanECSynchronizedGravityTailProfileOrigin
                source current center)
              (cartanECSynchronizedGravityTailProfileTarget
                source current center)
              internalPair spacetimePair *
            orientedLorentzBivectorBasisCoefficient spacetimePair
              derivativeDirection formDirection by
    funext center
    exact cartanECSynchronizedGravityTailLoweredConnectionFirstJet_normalForm
      source current center derivativeDirection formDirection internalPair]
  apply ContDiffAt.sum
  intro spacetimePair _
  exact
    (normalizedDerivative_component_contDiffAt_infty source current baseSmooth
      contact nondegenerate internalPair spacetimePair).mul contDiffAt_const

theorem cartanECSynchronizedGravityTailLorentzJetCLM_contDiffAt_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0) :
    ContDiffAt ℝ ∞
      (cartanECSynchronizedGravityTailJetCLM source current) contact := by
  unfold cartanECSynchronizedGravityTailJetCLM
  apply ContDiffAt.sum
  intro derivativeDirection _
  have oneFormRegular : ContDiffAt ℝ ∞ (fun center =>
      cartanECSynchronizedGravityTailJetOneForm
        source current center derivativeDirection) contact := by
    apply contDiffAt_pi'
    intro formDirection
    apply contDiffAt_pi'
    intro internalPair
    exact loweredConnectionFirstJet_contDiffAt_infty
      source current baseSmooth contact nondegenerate derivativeDirection
        formDirection internalPair
  fun_prop

theorem cartanECSynchronizedGravityTailLorentzJetCLM_contDiff_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (baseNondegenerate : (Base source current).Nondegenerate) :
    ContDiff ℝ ∞
      (cartanECSynchronizedGravityTailJetCLM source current) := by
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact cartanECSynchronizedGravityTailLorentzJetCLM_contDiffAt_infty
    source current baseSmooth contact (baseNondegenerate contact)

private theorem profileCoframeDerivative_contDiffAt_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    ContDiffAt ℝ ∞ (fun center =>
      (cartanECSynchronizedGravityTailProfileCoframeFirstJet
        source current center).derivative
          derivativeDirection internal coordinate) contact := by
  rw [show
    (fun center =>
      (cartanECSynchronizedGravityTailProfileCoframeFirstJet
        source current center).derivative
          derivativeDirection internal coordinate) =
      fun center =>
        -coframeConnectionAction
            ((Base source current).gravityConnection center)
            derivativeDirection ((Base source current).coframe center)
            internal coordinate +
          ((1 : ℝ) / 2) *
            orderedCartanTorsionComponent
              (diracDualFormNativeActionCartanTorsionAt
                source (Base source current) center)
              internal derivativeDirection coordinate by
    funext center
    exact
      cartanECSynchronizedGravityTailProfileCoframeFirstJet_derivative_normalForm
        source current center derivativeDirection internal coordinate]
  unfold coframeConnectionAction orderedCartanTorsionComponent
  apply ContDiffAt.add
  · apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro middle _
    exact
      (baseSmooth.2.1 derivativeDirection internal middle).contDiffAt.mul
        (contDiff_pi.mp
          (contDiff_pi.mp
            (holonomicCoframe_contDiff (Base source current) baseSmooth)
            middle) coordinate).contDiffAt
  · apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.sum
    intro spacetimePair _
    exact
      (baseCartanTorsion_coordinate_contDiffAt source current baseSmooth
        contact nondegenerate spacetimePair internal).mul contDiffAt_const

theorem cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiffAt_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (contact : BasePoint)
    (nondegenerate : Matrix.det ((Base source current).coframe contact) ≠ 0)
    (internal coordinate : LorentzianIndex) :
    ContDiffAt ℝ ∞ (fun center =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current center internal coordinate) contact := by
  unfold cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
    cartanECSynchronizedGravityTailCoframeJetOneForm
  apply ContDiffAt.sum
  intro derivativeDirection _
  have coefficientRegular :=
    profileCoframeDerivative_contDiffAt_infty source current baseSmooth contact
      nondegenerate derivativeDirection internal coordinate
  fun_prop

theorem cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiff_infty
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (baseNondegenerate : (Base source current).Nondegenerate)
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ ∞ (fun center =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current center internal coordinate) := by
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact
    cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiffAt_infty
      source current baseSmooth contact (baseNondegenerate contact)
        internal coordinate

/- The public C-infinity mouths use the workspace's canonical `BasePoint`
norm instances.  The high-priority PiLp aliases above are proof-local
implementation details and must not leak into downstream theorem types. -/
attribute [-instance] gravityTailBasePointNormedAddCommGroup
attribute [-instance] gravityTailBasePointNormedSpace

theorem cartanECSynchronizedGravityTailLorentzJetCLM_contDiff_infty_default
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (baseNondegenerate : (Base source current).Nondegenerate) :
    ContDiff ℝ ∞
      (cartanECSynchronizedGravityTailJetCLM source current) := by
  simpa only [gravityTailBasePointNormedAddCommGroup,
    gravityTailBasePointNormedSpace] using
    cartanECSynchronizedGravityTailLorentzJetCLM_contDiff_infty
      source current baseSmooth baseNondegenerate

theorem
    cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiff_infty_default
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (baseSmooth : (Base source current).Smooth)
    (baseNondegenerate : (Base source current).Nondegenerate)
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ ∞ (fun center =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current center internal coordinate) := by
  simpa only [gravityTailBasePointNormedAddCommGroup,
    gravityTailBasePointNormedSpace] using
    cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiff_infty
      source current baseSmooth baseNondegenerate internal coordinate

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanECSynchronizedGravityTailProfileLocalRegularity
