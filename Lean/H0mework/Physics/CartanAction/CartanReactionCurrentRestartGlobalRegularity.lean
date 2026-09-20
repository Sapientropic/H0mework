import H0mework.Physics.JointVariation.MatterTemporalLocalRegularity
import H0mework.Physics.Exterior.GravityReactionInstallation

/-!
# Global regularity of the Cartan/reaction restart

A smooth globally nondegenerate current gives a smooth action-owned Cartan
connection.  The computed `II+` preparation is then smooth, and the live
gravity reaction is a smooth readout of that prepared connection and
auxiliary field.  This is an acceptance theorem for the existing restart;
neither regularity nor nondegeneracy is an input of its constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanReactionCurrentRestartGlobalRegularity

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

private theorem cartanConnectionWrittenCurrent_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    (diracDualFormNativeCartanConnectionWrittenCurrent source current).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, _connectionSmooth, auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  refine
    ⟨coframeSmooth, ?_, auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  intro formDirection internalOut internalIn
  apply contDiff_iff_contDiffAt.mpr
  intro point
  change ContDiffAt ℝ ∞
    (fun candidate : BasePoint =>
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current).gravityConnection candidate
        formDirection internalOut internalIn) point
  exact cartanReactionRestart_connection_component_contDiffAt
    source current
    ⟨coframeSmooth, _connectionSmooth, auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
    point (nondegenerate point) formDirection internalOut internalIn

/-- The source/current-only Cartan and live-reaction restart preserves global
smoothness whenever its supplied current is smooth and nondegenerate. -/
theorem sourceActionGeneratedDiracDualCartanReactionCurrentRestart_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      source current).Smooth := by
  let written :=
    diracDualFormNativeCartanConnectionWrittenCurrent source current
  let prepared :=
    diracDualFormNativeCartanSimplicityPreparedCurrent source current
  have writtenSmooth : written.Smooth := by
    exact cartanConnectionWrittenCurrent_smooth
      source current smooth nondegenerate
  have preparedSmooth : prepared.Smooth := by
    exact restrictHolonomicConfigurationToIIPlus_smooth written writtenSmooth
  rcases preparedSmooth with
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, _multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  refine
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, ?_,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  intro internalPair spacetimePair
  change ContDiff ℝ ∞
    (fun point =>
      formNativeGravityReactionField prepared point
        internalPair spacetimePair)
  exact formNativeGravityReactionField_component_contDiff
    prepared connectionSmooth auxiliarySmooth internalPair spacetimePair

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanReactionCurrentRestartGlobalRegularity
