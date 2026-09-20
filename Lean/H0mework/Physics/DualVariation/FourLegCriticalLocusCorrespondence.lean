import H0mework.Physics.CoframeVariation.CoframePointwiseEquation
import H0mework.Physics.DualVariation.GravityMultiplierAuxiliaryVariation
import H0mework.Physics.DualVariation.IIPlusReductionIntegratedVariation
import H0mework.Physics.DualVariation.LorentzConnectionVariation

/-!
# Four-leg critical-locus correspondence for the Dirac-dual root

This module assembles the repaired action's multiplier, gravity-auxiliary,
coframe, and Lorentz-connection variation producers.  On the generated
simplicity and independent `B`-Euler zero fibers, the full coframe coefficient
agrees with the actual nonlinear `B(t)=II+(e+t h)` coefficient.  The computed
restriction also commutes with the primitive connection path.

The terminal theorem is exact action reduction / producer soundness for one
action hash.  It asserts no inhabitant, stationary actual, joint variation,
local Lorentz covariance, or Einstein--Cartan equivalence.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence

open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCoframeIntegratedVariation
open StageNineDiracDualFormNativeCoframePointwiseEquation
open StageNineDiracDualFormNativeGravityMultiplierAuxiliaryVariation
open StageNineDiracDualFormNativeIIPlusReductionIntegratedVariation
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation
open StageNineDiracDualFormNativeLorentzConnectionVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNineCompactSupportIntegrationByParts
open scoped ContDiff Matrix.Norms.Elementwise Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Simplicity as the computed-restriction fixed locus -/

theorem
    restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
    (configuration : StageNineHolonomicConfiguration) :
    restrictHolonomicConfigurationToIIPlus configuration = configuration ↔
      FormNativeGravitySimplicityEquation configuration := by
  constructor
  · intro fixedPoint point
    have auxiliaryEquality := congrArg
      StageNineHolonomicConfiguration.gravityAuxiliary fixedPoint
    exact (congrFun auxiliaryEquality point).symm
  · intro simplicity
    apply StageNineHolonomicConfiguration.ext
    · rfl
    · rfl
    · funext point
      exact (simplicity point).symm
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

private theorem restrictContinuumPointFieldToIIPlus_eq_self_of_simplicity
    (configuration : StageNineHolonomicConfiguration)
    (simplicity : FormNativeGravitySimplicityEquation configuration)
    (point : BasePoint) :
    restrictContinuumPointFieldToIIPlus
        (toContinuumPointField configuration point) =
      toContinuumPointField configuration point := by
  have fixedPoint :=
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      configuration).2 simplicity
  calc
    restrictContinuumPointFieldToIIPlus
        (toContinuumPointField configuration point) =
      toContinuumPointField
        (restrictHolonomicConfigurationToIIPlus configuration) point :=
          (toContinuumPointField_restrictHolonomicConfigurationToIIPlus
            configuration point).symm
    _ = toContinuumPointField configuration point := by rw [fixedPoint]

/-! ## Coframe coefficient and stationarity correspondence -/

theorem
    holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_of_equations
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (simplicity : FormNativeGravitySimplicityEquation configuration)
    (auxiliaryEquation : FormNativeGravityAuxiliaryEquation configuration)
    (variation : BasePoint → LorentzianCoframe)
    (point : BasePoint) :
    holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
        source configuration variation point =
      holonomicDiracDualFormNativeCoframeFirstVariationDensity
        source configuration variation point := by
  let field := toContinuumPointField configuration point
  have fixedField : restrictContinuumPointFieldToIIPlus field = field := by
    exact restrictContinuumPointFieldToIIPlus_eq_self_of_simplicity
      configuration simplicity point
  have auxiliaryZero :
      formNativeGravityAuxiliaryEulerResidual
        (restrictContinuumPointFieldToIIPlus field) = 0 := by
    rw [fixedField]
    exact congrFun auxiliaryEquation point
  have actual :=
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_frozenCoframe_of_auxiliaryEulerZero
      source point field (variation point) auxiliaryZero
  simpa
    [holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity,
      holonomicDiracDualFormNativeCoframeFirstVariationDensity, field,
      fixedField] using actual

theorem
    holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationIntegral_eq_full_of_equations
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (simplicity : FormNativeGravitySimplicityEquation configuration)
    (auxiliaryEquation : FormNativeGravityAuxiliaryEquation configuration)
    (variation : BasePoint → LorentzianCoframe) :
    (∫ point : BasePoint,
        holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
          source configuration variation point) =
      ∫ point : BasePoint,
        holonomicDiracDualFormNativeCoframeFirstVariationDensity
          source configuration variation point := by
  apply integral_congr_ae
  filter_upwards with point
  exact
    holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_of_equations
      source configuration simplicity auxiliaryEquation variation point

def DiracDualFormNativeIIPlusReducedCoframeActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzianCoframe,
    HasDerivAt
      (fun parameter =>
        holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction
          source 0 (varyCoframe configuration variation parameter))
      0 0

theorem diracDualFormNativeGravityCoframeActionStationary_iff_reduced
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration)
    (simplicity : FormNativeGravitySimplicityEquation configuration)
    (auxiliaryEquation : FormNativeGravityAuxiliaryEquation configuration) :
    DiracDualFormNativeGravityCoframeActionStationary source configuration ↔
      DiracDualFormNativeIIPlusReducedCoframeActionStationary source
        configuration := by
  have fixedPoint :=
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      configuration).2 simplicity
  have restrictedIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        (restrictHolonomicConfigurationToIIPlus configuration) := by
    simpa only [fixedPoint] using densityIntegrable
  constructor
  · intro fullStationary variation
    have fullActual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_coframe_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    have reducedActual :=
      holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction_coframe_hasDerivAt
        source configuration smooth nondegenerate restrictedIntegrable
          variation
    have fullCoefficientZero :
        (∫ point : BasePoint,
          holonomicDiracDualFormNativeCoframeFirstVariationDensity
            source configuration variation point) = 0 :=
      ((fullStationary variation).unique fullActual).symm
    have coefficientEquality :=
      holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationIntegral_eq_full_of_equations
        source configuration simplicity auxiliaryEquation variation
    have reducedCoefficientZero :
        (∫ point : BasePoint,
          holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
            source configuration variation point) = 0 :=
      coefficientEquality.trans fullCoefficientZero
    rw [reducedCoefficientZero] at reducedActual
    exact reducedActual
  · intro reducedStationary variation
    have fullActual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_coframe_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    have reducedActual :=
      holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction_coframe_hasDerivAt
        source configuration smooth nondegenerate restrictedIntegrable
          variation
    have reducedCoefficientZero :
        (∫ point : BasePoint,
          holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
            source configuration variation point) = 0 :=
      ((reducedStationary variation).unique reducedActual).symm
    have coefficientEquality :=
      holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationIntegral_eq_full_of_equations
        source configuration simplicity auxiliaryEquation variation
    have fullCoefficientZero :
        (∫ point : BasePoint,
          holonomicDiracDualFormNativeCoframeFirstVariationDensity
            source configuration variation point) = 0 :=
      coefficientEquality.symm.trans reducedCoefficientZero
    rw [fullCoefficientZero] at fullActual
    exact fullActual

/-! ## Connection path and stationarity correspondence -/

theorem restrictHolonomicConfigurationToIIPlus_varyLorentzConnection
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm)
    (parameter : ℝ) :
    restrictHolonomicConfigurationToIIPlus
        (varyLorentzConnection configuration variation parameter) =
      varyLorentzConnection
        (restrictHolonomicConfigurationToIIPlus configuration)
        variation parameter := by
  rfl

theorem
    holonomicIIPlusReducedDiracDualFormNativeIntegratedAction_varyLorentzConnection_eq_full
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (simplicity : FormNativeGravitySimplicityEquation configuration)
    (variation : BasePoint → LorentzBivectorOneForm)
    (parameter : ℝ) :
    holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction source
        chart (varyLorentzConnection configuration variation parameter) =
      holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        (varyLorentzConnection configuration variation parameter) := by
  have fixedPoint :=
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      configuration).2 simplicity
  calc
    holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction source
        chart (varyLorentzConnection configuration variation parameter) =
      holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        (restrictHolonomicConfigurationToIIPlus
          (varyLorentzConnection configuration variation parameter)) :=
            (holonomicDiracDualFormNativeIntegratedAction_restrictIIPlus source
              chart
              (varyLorentzConnection configuration variation parameter)).symm
    _ = holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        (varyLorentzConnection
          (restrictHolonomicConfigurationToIIPlus configuration)
          variation parameter) := by
      rw [restrictHolonomicConfigurationToIIPlus_varyLorentzConnection]
    _ = holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        (varyLorentzConnection configuration variation parameter) := by
      rw [fixedPoint]

def DiracDualFormNativeIIPlusReducedLorentzConnectionActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm,
    HasDerivAt
      (fun parameter =>
        holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction source
          0 (varyLorentzConnection configuration variation parameter))
      0 0

theorem diracDualFormNativeLorentzConnectionActionStationary_iff_reduced
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (simplicity : FormNativeGravitySimplicityEquation configuration) :
    DiracDualFormNativeLorentzConnectionActionStationary source configuration ↔
      DiracDualFormNativeIIPlusReducedLorentzConnectionActionStationary source
        configuration := by
  constructor
  · intro fullStationary variation
    have actionEquality :
        (fun parameter =>
          holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction
            source 0
            (varyLorentzConnection configuration variation parameter)) =
        fun parameter =>
          holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
            (varyLorentzConnection configuration variation parameter) := by
      funext parameter
      exact
        holonomicIIPlusReducedDiracDualFormNativeIntegratedAction_varyLorentzConnection_eq_full
          source 0 configuration simplicity variation parameter
    rw [actionEquality]
    exact fullStationary variation
  · intro reducedStationary variation
    have actionEquality :
        (fun parameter =>
          holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction
            source 0
            (varyLorentzConnection configuration variation parameter)) =
        fun parameter =>
          holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
            (varyLorentzConnection configuration variation parameter) := by
      funext parameter
      exact
        holonomicIIPlusReducedDiracDualFormNativeIntegratedAction_varyLorentzConnection_eq_full
          source 0 configuration simplicity variation parameter
    rw [← actionEquality]
    exact reducedStationary variation

/-! ## Terminal four-leg correspondence -/

theorem diracDualFormNative_fourLegCriticalLocus_iff_reduced
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration) :
    (DiracDualFormNativeGravityMultiplierActionStationary source 0
        configuration ∧
      DiracDualFormNativeGravityAuxiliaryActionStationary source 0
        configuration ∧
      DiracDualFormNativeGravityCoframeActionStationary source configuration ∧
      DiracDualFormNativeLorentzConnectionActionStationary source
        configuration) ↔
    (FormNativeGravitySimplicityEquation configuration ∧
      configuration.gravitySimplicityMultiplier =
        formNativeGravityReactionField configuration ∧
      DiracDualFormNativeIIPlusReducedCoframeActionStationary source
        configuration ∧
      DiracDualFormNativeIIPlusReducedLorentzConnectionActionStationary source
        configuration) := by
  constructor
  · rintro ⟨multiplierStationary, auxiliaryStationary, coframeStationary,
      connectionStationary⟩
    have algebraic :=
      (diracDualFormNativeGravityMultiplierAndAuxiliaryActionStationary_iff
        source 0 configuration smooth densityIntegrable).1
        ⟨multiplierStationary, auxiliaryStationary⟩
    have auxiliaryEquation : FormNativeGravityAuxiliaryEquation configuration :=
      (formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
        configuration).2 algebraic.2
    have reducedCoframeStationary :=
      (diracDualFormNativeGravityCoframeActionStationary_iff_reduced source
        configuration smooth nondegenerate densityIntegrable algebraic.1
          auxiliaryEquation).1 coframeStationary
    have reducedConnectionStationary :=
      (diracDualFormNativeLorentzConnectionActionStationary_iff_reduced source
        configuration algebraic.1).1 connectionStationary
    exact ⟨algebraic.1, algebraic.2, reducedCoframeStationary,
      reducedConnectionStationary⟩
  · rintro ⟨simplicity, reaction, reducedCoframeStationary,
      reducedConnectionStationary⟩
    have algebraic :=
      (diracDualFormNativeGravityMultiplierAndAuxiliaryActionStationary_iff
        source 0 configuration smooth densityIntegrable).2
        ⟨simplicity, reaction⟩
    have auxiliaryEquation : FormNativeGravityAuxiliaryEquation configuration :=
      (formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
        configuration).2 reaction
    have coframeStationary :=
      (diracDualFormNativeGravityCoframeActionStationary_iff_reduced source
        configuration smooth nondegenerate densityIntegrable simplicity
          auxiliaryEquation).2 reducedCoframeStationary
    have connectionStationary :=
      (diracDualFormNativeLorentzConnectionActionStationary_iff_reduced source
        configuration simplicity).2 reducedConnectionStationary
    exact ⟨algebraic.1, algebraic.2, coframeStationary,
      connectionStationary⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
