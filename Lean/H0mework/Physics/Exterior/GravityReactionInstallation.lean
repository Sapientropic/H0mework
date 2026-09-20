import H0mework.Physics.Exterior.GravityMultiplierAuxiliaryIntegratedVariation

/-!
# Form-native live gravity-reaction installation

The `B`-Euler reaction is uniquely read from the live primitive curvature and
gravity auxiliary field.  This dependency-light operator installs that
reaction in the multiplier slot and exposes its exact self-generation law.
It accepts no residual, target field, branch, or zero-fiber receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeGravityReactionInstallation

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization

open scoped ContDiff

noncomputable section

set_option autoImplicit false

/-! ## Regularity of the live reaction -/

theorem gravityConnectionDerivative_contDiff_of_connectionComponents
    (configuration : StageNineHolonomicConfiguration)
    (connectionSmooth : ∀ direction internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        configuration.gravityConnection point direction internalOut internalIn)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      gravityConnectionDerivative configuration point derivativeDirection
        formDirection internalOut internalIn := by
  let connectionCoordinate : BasePoint → ℝ := fun point =>
    configuration.gravityConnection point formDirection internalOut internalIn
  have coordinateSmooth : ContDiff ℝ ∞ connectionCoordinate :=
    connectionSmooth formDirection internalOut internalIn
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry (fun _ : BasePoint => connectionCoordinate)) :=
    coordinateSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ connectionCoordinate point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  unfold gravityConnectionDerivative
  change ContDiff ℝ ∞ fun point =>
    fderiv ℝ connectionCoordinate point
      (coordinateDirection derivativeDirection)
  exact derivativeSmooth.clm_apply contDiff_const

theorem holonomicGravityCurvature_component_contDiff_of_connectionComponents
    (configuration : StageNineHolonomicConfiguration)
    (connectionSmooth : ∀ direction internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        configuration.gravityConnection point direction internalOut internalIn)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      holonomicGravityCurvature configuration point
        internalPair spacetimePair := by
  unfold holonomicGravityCurvature
  dsimp only
  apply contDiff_const.mul
  apply ContDiff.add
  · apply ContDiff.sub
    · exact gravityConnectionDerivative_contDiff_of_connectionComponents
        configuration connectionSmooth
        (pairFirst spacetimePair) (pairSecond spacetimePair)
        (pairFirst internalPair) (pairSecond internalPair)
    · exact gravityConnectionDerivative_contDiff_of_connectionComponents
        configuration connectionSmooth
        (pairSecond spacetimePair) (pairFirst spacetimePair)
        (pairFirst internalPair) (pairSecond internalPair)
  · apply ContDiff.sum
    intro middle _
    exact
      ((connectionSmooth (pairFirst spacetimePair)
          (pairFirst internalPair) middle).mul
        (connectionSmooth (pairSecond spacetimePair)
          middle (pairSecond internalPair))).sub
      ((connectionSmooth (pairSecond spacetimePair)
          (pairFirst internalPair) middle).mul
        (connectionSmooth (pairFirst spacetimePair)
          middle (pairSecond internalPair)))

/-- Smooth primitive connection and auxiliary fields give a smooth live
reaction.  The reaction is a readout of those two fields, not a new input. -/
theorem formNativeGravityReactionField_component_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (connectionSmooth : ∀ direction internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        configuration.gravityConnection point direction internalOut internalIn)
    (auxiliarySmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        configuration.gravityAuxiliary point internalPair spacetimePair)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      formNativeGravityReactionField configuration point
        internalPair spacetimePair := by
  unfold formNativeGravityReactionField
  have dualSmooth : ContDiff ℝ ∞ fun point =>
      gravityInternalDualEquiv (configuration.gravityAuxiliary point) := by
    change ContDiff ℝ ∞ fun point =>
      gravityInternalDualLinear (configuration.gravityAuxiliary point)
    apply gravityInternalDualLinear.toContinuousLinearMap.contDiff.comp
    apply contDiff_pi'
    intro first
    apply contDiff_pi'
    intro second
    exact auxiliarySmooth first second
  have curvatureSmooth : ContDiff ℝ ∞ fun point =>
      holonomicContravariantGravityCurvature configuration point
        internalPair spacetimePair :=
    contDiff_const.mul
      (holonomicGravityCurvature_component_contDiff_of_connectionComponents
        configuration connectionSmooth internalPair spacetimePair)
  exact
    (contDiff_pi.mp (contDiff_pi.mp dualSmooth internalPair)
      spacetimePair).sub curvatureSmooth

/-- Install the unique live gravity reaction while retaining every primitive
field other than the multiplier slot. -/
def installFormNativeGravityReaction
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gravitySimplicityMultiplier :=
      formNativeGravityReactionField configuration }

@[simp] theorem installFormNativeGravityReaction_multiplier
    (configuration : StageNineHolonomicConfiguration) :
    (installFormNativeGravityReaction configuration
      ).gravitySimplicityMultiplier =
      formNativeGravityReactionField configuration :=
  rfl

@[simp] theorem installFormNativeGravityReaction_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (installFormNativeGravityReaction configuration).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem installFormNativeGravityReaction_gravityConnection
    (configuration : StageNineHolonomicConfiguration) :
    (installFormNativeGravityReaction configuration).gravityConnection =
      configuration.gravityConnection :=
  rfl

@[simp] theorem installFormNativeGravityReaction_gravityAuxiliary
    (configuration : StageNineHolonomicConfiguration) :
    (installFormNativeGravityReaction configuration).gravityAuxiliary =
      configuration.gravityAuxiliary :=
  rfl

theorem formNativeGravityReactionField_installFormNativeGravityReaction
    (configuration : StageNineHolonomicConfiguration) :
    formNativeGravityReactionField
        (installFormNativeGravityReaction configuration) =
      formNativeGravityReactionField configuration :=
  rfl

/-- The installed multiplier is the reaction of the output actual itself,
not a stale read from a sibling state. -/
theorem installFormNativeGravityReaction_reactionSelfGenerated
    (configuration : StageNineHolonomicConfiguration) :
    (installFormNativeGravityReaction configuration
      ).gravitySimplicityMultiplier =
      formNativeGravityReactionField
        (installFormNativeGravityReaction configuration) := by
  rw [installFormNativeGravityReaction_multiplier,
    formNativeGravityReactionField_installFormNativeGravityReaction]

/-- Producer soundness for the unique live reaction installation. -/
theorem installFormNativeGravityReaction_auxiliaryEquation
    (configuration : StageNineHolonomicConfiguration) :
    FormNativeGravityAuxiliaryEquation
      (installFormNativeGravityReaction configuration) := by
  exact
    (formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
      (installFormNativeGravityReaction configuration)).2
      (installFormNativeGravityReaction_reactionSelfGenerated configuration)

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeGravityReactionInstallation
