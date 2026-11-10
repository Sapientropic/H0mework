import H0mework.Physics.CoframeVariation.IIPlusCoframePointwiseEquation

/-!
# Regressions for the reduced coframe pointwise equation

The positive controls expose the action-stationarity and terminal four-leg
interfaces.  The negative control preserves a witnessed failure of the
explicit same-configuration balance; the localization theorem cannot turn it
into a stationary actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusCoframePointwiseEquationRegression

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCoframePointwiseEquation
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeGravityMultiplierAuxiliaryVariation
open StageNineDiracDualFormNativeIIPlusCoframePointwiseEquation
open StageNineDiracDualFormNativeIIPlusTorsionSpinCriticalLocus
open StageNineDiracDualFormNativeLorentzConnectionVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzTorsionSpinEquation
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineIIPlusRestriction

noncomputable section

set_option autoImplicit false

theorem reducedCoframeECBalance_api_regression
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        (restrictHolonomicConfigurationToIIPlus configuration)) :
    DiracDualFormNativeIIPlusReducedCoframeActionStationary source
        configuration ↔
      DiracDualFormNativeIIPlusCoframeECBalanceEquation source
        configuration :=
  diracDualFormNativeIIPlusReducedCoframeActionStationary_iff_EC_balance
    source configuration smooth nondegenerate densityIntegrable

theorem reducedCoframeStationarity_rejected_of_EC_balance_failure
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        (restrictHolonomicConfigurationToIIPlus configuration))
    (balanceFailure :
      ¬ DiracDualFormNativeIIPlusCoframeECBalanceEquation source
        configuration) :
    ¬ DiracDualFormNativeIIPlusReducedCoframeActionStationary source
        configuration :=
  fun stationary => balanceFailure
    ((diracDualFormNativeIIPlusReducedCoframeActionStationary_iff_EC_balance
      source configuration smooth nondegenerate densityIntegrable).1
      stationary)

theorem fourLegECBalanceTorsionSpin_api_regression
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration)
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
      DiracDualFormNativeIIPlusCoframeECBalanceEquation source configuration ∧
      FormNativeIIPlusTorsionSpinEquation source configuration) :=
  diracDualFormNative_fourLegCriticalLocus_iff_EC_coframeBalance_and_torsionSpin
    source configuration smooth admissible nondegenerate densityIntegrable

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusCoframePointwiseEquationRegression
