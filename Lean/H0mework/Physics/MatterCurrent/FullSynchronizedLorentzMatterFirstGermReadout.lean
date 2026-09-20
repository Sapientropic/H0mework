import H0mework.Physics.MatterCurrent.FullSynchronizedLorentzContactReadout

/-!
# C3h207b: latest-current matter first-germ readout

This module follows the primal and adjoint matter fields of the C3h203 judged
actual back to the synchronized Cauchy state that generated them.  The two
later primal installers preserve the already generated first jet, while the
P286 and Lorentz auxiliary installers leave the relevant matter field
unchanged.

The result is an exact same-actual first-germ interface for the forthcoming
Lorentz matter-spin derivative.  It is a readout/transporter of an already
generated action germ, not a new Euler--Lagrange closure or a supplied
derivative certificate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMatterFirstGermReadout

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineCurrentFullSynchronizedLorentzMatterReadout
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineHolonomicField
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterActionTimeVelocity
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzContactReadout
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzResponse

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

private abbrev SynchronizedActual : StageNineHolonomicConfiguration :=
  fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual

private abbrev P286Actual : StageNineHolonomicConfiguration :=
  currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
    SynchronizedActual

private abbrev TemporalActual : StageNineHolonomicConfiguration :=
  actionGeneratedMatterTemporalFirstGermActual positiveSmoothUnifiedSource
    P286Actual

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_matter_completeFirstGerm
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            (positiveP506MatterCurrentFullSynchronizedLorentzActual.matter
              point))
        0 direction =
      actionGeneratedMatterLocalJetCoordinate
        positiveP506MatterCurrentFullSynchronizedMatterCauchyState
        0 direction := by
  have synchronizedSmooth : SynchronizedActual.Smooth := by
    exact fullSynchronizedActionResponseOperator_smooth
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedLorentzBaseActual
      positiveP506MatterCurrentFullSynchronizedLorentzBaseActual_smooth
  have p286Smooth : P286Actual.Smooth := by
    exact currentP286CompleteActionResponseOperator_smooth
      positiveSmoothUnifiedSource SynchronizedActual synchronizedSmooth
  have temporalSmooth : TemporalActual.Smooth := by
    exact actionGeneratedMatterTemporalFirstGermActual_smooth
      positiveSmoothUnifiedSource P286Actual p286Smooth
  unfold
    positiveP506MatterCurrentFullSynchronizedLorentzActual
  rw [
    currentFullSynchronizedLorentzActualFirstJetLift_matter,
    currentCanonicalFullActionActual_matter_eq_complete]
  change
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            ((actionGeneratedMatterCompleteFirstGermActual
              positiveSmoothUnifiedSource TemporalActual).matter point))
        0 direction =
      _
  rw [actionGeneratedMatterCompleteFirstGermActual_matter_firstJet_origin
    positiveSmoothUnifiedSource TemporalActual temporalSmooth direction]
  change
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            ((actionGeneratedMatterTemporalFirstGermActual
              positiveSmoothUnifiedSource P286Actual).matter point))
        0 direction =
      _
  rw [actionGeneratedMatterTemporalFirstGermActual_matter_firstJet_origin
    positiveSmoothUnifiedSource P286Actual p286Smooth direction]
  rw [currentP286CompleteActionResponseOperator_matter,
    fullSynchronizedActionResponseOperator_matter_eq_localField]
  simpa [actionGeneratedMatterLocalField] using
    actionGeneratedMatterLocalCoordinate_derivative
      positiveP506MatterCurrentFullSynchronizedMatterCauchyState 0 direction

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_conjugateMatter_completeFirstGerm
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (fun point =>
          positiveP506MatterCurrentFullSynchronizedLorentzActual.conjugateMatter
            point matter)
        0 direction =
      actionGeneratedConjugateMatterLocalJet
        positiveP506MatterCurrentFullSynchronizedMatterCauchyState
        0 direction matter := by
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzActual_conjugateMatter_eq_localField]
  exact actionGeneratedConjugateMatterLocalField_derivative
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState
    0 matter direction

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMatterFirstGermReadout
