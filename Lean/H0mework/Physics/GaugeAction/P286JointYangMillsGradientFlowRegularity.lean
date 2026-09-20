import H0mework.Physics.GaugeAction.P286JointYangMillsGradientFlow
import H0mework.Physics.SafeCauchy.FixedJointGlobalECJetRegularity
import H0mework.Physics.Constitutive.P286GaugeConstitutiveEliminationRegularity

/-!
# Regularity of the source-native P286 Yang--Mills gradient flow

This module proves that the canonical all-point A/F/B Euler step preserves
the smooth, nondegenerate configuration domain.  The proof differentiates the
actual action-generated Euler three-form and transports it through the two
finite-dimensional linear equivalences; no smooth gradient or next state is
accepted as constructor data.
-/

namespace SaturationMonoid.PhysicsCore
namespace StageNineP286JointYangMillsGradientFlowRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalECJetRegularity
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286JointYangMillsGradientFlow
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance gradientFlowRegularityP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective

local instance gradientFlowRegularityP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance gradientFlowRegularityP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Smooth action gradient -/

private theorem auxiliaryExteriorDerivative_contDiff_of_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryExteriorDerivative configuration) := by
  have coordinateRegular : ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate configuration) := by
    apply contDiff_pi'
    intro pair
    exact smooth.2.2.2.2.2.1 pair
  have firstJetRegular : ContDiff ℝ ∞
      (fderiv ℝ (holonomicP286GaugeAuxiliaryCoordinate configuration)) :=
    coordinateRegular.fderiv_right (by simp)
  have directionalRegular (direction : LorentzianIndex) :
      ContDiff ℝ ∞ (fun point =>
        p286GaugeAuxiliaryDirectionalDerivative configuration point direction) := by
    unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
    exact firstJetRegular.clm_apply contDiff_const
  have orderedRegular (direction first second : LorentzianIndex) :
      ContDiff ℝ ∞ (fun point =>
        orderedP286GaugeTwoFormComponent
          (p286GaugeAuxiliaryDirectionalDerivative configuration point direction)
          first second) := by
    unfold orderedP286GaugeTwoFormComponent
    apply ContDiff.sum
    intro pair _
    exact
      (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint =>
        (orientedLorentzBivectorBasisCoefficient pair first second : ℝ))).smul
        (contDiff_pi.mp (directionalRegular direction) pair)
  apply contDiff_pi'
  intro triple
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
  exact
    ((orderedRegular (threeFormFirst triple) (threeFormSecond triple)
      (threeFormThird triple)).add
      (orderedRegular (threeFormSecond triple) (threeFormThird triple)
        (threeFormFirst triple))).add
      (orderedRegular (threeFormThird triple) (threeFormFirst triple)
        (threeFormSecond triple))

theorem holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_contDiff_of_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative configuration) := by
  rw [show
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative configuration =
      fun point =>
        holonomicP286GaugeAuxiliaryExteriorDerivative configuration point +
          pointwiseP286GaugeTwoFormConnectionExteriorAction
            (holonomicP286GaugeConnectionCoordinate configuration point)
            (holonomicP286GaugeAuxiliaryCoordinate configuration point) by
    funext point
    exact
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts
        configuration point]
  exact (auxiliaryExteriorDerivative_contDiff_of_smooth configuration smooth).add
    (pointwiseP286GaugeTwoFormConnectionExteriorAction_contDiff_of_smooth
      configuration smooth)

theorem holonomicFormNativeP286GaugeEulerThreeForm_contDiff_of_smooth
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞
      (holonomicFormNativeP286GaugeEulerThreeForm source 0 configuration) := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  exact
    (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_contDiff_of_smooth
      configuration smooth).add
      (formNativeChargedGaugeThreeForm_contDiff_of_smooth source configuration
        smooth nondegenerate)

theorem p286JointYangMillsActionGradient_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞ (p286JointYangMillsActionGradient source configuration) := by
  let basis := Module.finBasis ℝ P286GaugeOneForm
  let coordinates := fun point =>
    basis.dualBasis.equivFun
      (p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm source 0 configuration
          point))
  have eulerRegular :=
    holonomicFormNativeP286GaugeEulerThreeForm_contDiff_of_smooth source
      configuration smooth nondegenerate
  have coordinatesRegular : ContDiff ℝ ∞ coordinates := by
    apply contDiff_pi'
    intro index
    let evaluationLinear : P286GaugeThreeForm →ₗ[ℝ] ℝ :=
      { toFun := fun threeForm =>
          p286GaugeOneFormThreeFormWedgeCoefficient (basis index) threeForm
        map_add' := fun first second =>
          p286GaugeOneFormThreeFormWedgeCoefficient_add_right
            (basis index) first second
        map_smul' := by
          intro parameter threeForm
          simpa only [RingHom.id_apply, smul_eq_mul] using
            p286GaugeOneFormThreeFormWedgeCoefficient_smul_right parameter
              (basis index) threeForm }
    let evaluationCLM : P286GaugeThreeForm →L[ℝ] ℝ :=
      ⟨evaluationLinear,
        evaluationLinear.continuous_of_finiteDimensional⟩
    rw [show (fun point => coordinates point index) =
        fun point => evaluationCLM
          (holonomicFormNativeP286GaugeEulerThreeForm source 0 configuration
            point) by
      funext point
      calc
        coordinates point index =
            p286GaugeThreeFormWedgeLinearDual
              (holonomicFormNativeP286GaugeEulerThreeForm source 0
                configuration point) (basis index) :=
          basis.dualBasis_equivFun _ index
        _ = _ := rfl]
    exact evaluationCLM.contDiff.comp eulerRegular
  let reconstruct :=
    basis.dualBasis.equivFun.symm.trans p286GaugeOneFormPairingEquiv.symm
  let reconstructCLM :
      (Fin (Module.finrank ℝ P286GaugeOneForm) → ℝ) →L[ℝ]
        P286GaugeOneForm :=
    ⟨reconstruct.toLinearMap,
      reconstruct.toLinearMap.continuous_of_finiteDimensional⟩
  rw [show p286JointYangMillsActionGradient source configuration =
      fun point => reconstructCLM (coordinates point) by
    funext point
    change
      p286GaugeOneFormPairingEquiv.symm
          (p286GaugeThreeFormWedgeLinearDual
            (holonomicFormNativeP286GaugeEulerThreeForm source 0 configuration
              point)) =
        reconstruct (coordinates point)
    unfold reconstruct coordinates
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]]
  exact reconstructCLM.contDiff.comp coordinatesRegular

/-! ## Smooth A step and constitutive recomputation -/

theorem p286JointYangMillsConnectionEulerStep_smooth
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    (p286JointYangMillsConnectionEulerStep source configuration).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  refine ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    multiplierSmooth, ?_, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
    conjugateMatterSmooth⟩
  have gradientRegular :=
    p286JointYangMillsActionGradient_contDiff source configuration
      ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
        multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
        scalarSmooth, matterSmooth, conjugateMatterSmooth⟩ nondegenerate
  intro direction
  rw [show (fun point => p286CoordinateEquiv
      ((p286JointYangMillsConnectionEulerStep source configuration
        ).gaugeConnection point direction)) =
    fun point =>
      holonomicP286GaugeConnectionCoordinate configuration point direction -
        p286JointYangMillsActionGradient source configuration point direction by
    funext point
    have coordinateEq := congrFun
      (holonomicP286GaugeConnectionCoordinate_vary configuration
        (fun candidate =>
          -p286JointYangMillsActionGradient source configuration candidate)
        1 point) direction
    change
      holonomicP286GaugeConnectionCoordinate
          (p286JointYangMillsConnectionEulerStep source configuration)
          point direction = _
    rw [p286JointYangMillsConnectionEulerStep]
    simpa only [Pi.add_apply, Pi.neg_apply, one_smul, sub_eq_add_neg] using
      coordinateEq]
  exact (gaugeConnectionSmooth direction).sub
    (contDiff_pi.mp gradientRegular direction)

theorem p286JointYangMillsConnectionEulerStep_nondegenerate
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (p286JointYangMillsConnectionEulerStep source configuration
      ).Nondegenerate := by
  intro point
  change Matrix.det (configuration.coframe point) ≠ 0
  exact nondegenerate point

private theorem constitutiveReadout_auxiliaryCoordinate_eq
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    holonomicP286GaugeAuxiliaryCoordinate
        (formNativeP286GaugeConstitutiveReadout source configuration) =
      fun point =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings source) (configuration.coframe point)
          (holonomicP286GaugeCurvatureCoordinate configuration point) := by
  funext point pair
  unfold holonomicP286GaugeAuxiliaryCoordinate
    formNativeP286GaugeConstitutiveReadout
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
    holonomicP286GaugeCurvatureCoordinate
  rw [show (fun pair => p286CoordinateEquiv
      (holonomicGaugeCurvature configuration point pair)) =
      formNativeP286GaugeActualToCoordinateLinear
        (holonomicGaugeCurvature configuration point) by rfl,
    formNativeP286GaugeActual_coordinate_actual,
    formNativeP286GaugeActualToCoordinateLinear_apply]

theorem formNativeP286GaugeConstitutiveReadout_smooth
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    (formNativeP286GaugeConstitutiveReadout source configuration).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, _oldAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  refine ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    multiplierSmooth, gaugeConnectionSmooth, ?_, scalarSmooth, matterSmooth,
    conjugateMatterSmooth⟩
  have configurationSmooth : configuration.Smooth :=
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, _oldAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  have curvatureRegular : ContDiff ℝ ∞
      (holonomicP286GaugeCurvatureCoordinate configuration) := by
    apply contDiff_pi'
    intro pair
    exact holonomicGaugeCurvature_coordinate_contDiff configuration
      configurationSmooth pair
  intro pair
  rw [show (fun point => p286CoordinateEquiv
      ((formNativeP286GaugeConstitutiveReadout source configuration
        ).gaugeAuxiliary point pair)) =
    fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source) (configuration.coframe point)
        (holonomicP286GaugeCurvatureCoordinate configuration point) pair by
    funext point
    exact congrFun (congrFun
      (constitutiveReadout_auxiliaryCoordinate_eq source configuration) point)
      pair]
  rw [contDiff_iff_contDiffAt]
  intro point
  have outer :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings source) (configuration.coframe point)
      (nondegenerate point)
      (holonomicP286GaugeCurvatureCoordinate configuration point)
  have inner : ContDiffAt ℝ ∞ (fun candidate =>
      (configuration.coframe candidate,
        holonomicP286GaugeCurvatureCoordinate configuration candidate)) point :=
    (holonomicCoframe_contDiff configuration configurationSmooth).contDiffAt.prodMk
      curvatureRegular.contDiffAt
  exact contDiffAt_pi.mp (outer.comp point inner) pair

theorem p286JointYangMillsEulerStep_smooth
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    (p286JointYangMillsEulerStep source configuration).Smooth := by
  apply formNativeP286GaugeConstitutiveReadout_smooth
  · exact p286JointYangMillsConnectionEulerStep_smooth source configuration
      smooth nondegenerate
  · exact p286JointYangMillsConnectionEulerStep_nondegenerate source
      configuration nondegenerate

theorem p286JointYangMillsEulerStep_nondegenerate
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (p286JointYangMillsEulerStep source configuration).Nondegenerate := by
  intro point
  change Matrix.det (configuration.coframe point) ≠ 0
  exact nondegenerate point

end
end StageNineP286JointYangMillsGradientFlowRegularity
end PhysicsCore
end SaturationMonoid
