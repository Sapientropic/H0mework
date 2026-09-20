import H0mework.Physics.DualVariation.FourLegCriticalLocusCorrespondence
import H0mework.Physics.DualVariation.LorentzTorsionSpinEquation

/-!
# Computed-II+ connection critical locus for the Dirac-dual root

The reduced functional is the authoritative repaired root evaluated on the
computed `B := II+(e)` restriction.  This module proves that its actual
Lorentz-connection path is exactly the full-root path on that same
restriction, without assuming simplicity of the input configuration.  The
resulting reduced Euler locus is therefore precisely the existing
matter-coupled torsion--spin equation.

The terminal theorem replaces the reduced connection-stationarity field in
the four-leg correspondence by that equation.  It does not define a parallel
Palatini action, solve the connection, produce a stationary configuration, or
claim second-order Einstein--Hilbert/boundary-term equivalence.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusTorsionSpinCriticalLocus

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCoframeIntegratedVariation
open StageNineDiracDualFormNativeCoframePointwiseEquation
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeGravityMultiplierAuxiliaryVariation
open StageNineDiracDualFormNativeIIPlusReductionIntegratedVariation
open StageNineDiracDualFormNativeLorentzConnectionVariation
open StageNineDiracDualFormNativeLorentzTorsionSpinEquation
open StageNineDiracDualFormNativeMotherAction
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzTorsionSpinEquation
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## The actual reduced connection path -/

/-- The reduced connection path is the full repaired-root path evaluated on
the computed `II+` restriction.  No simplicity premise is needed: the target
configuration is explicitly the restricted actual. -/
theorem
    holonomicIIPlusReducedDiracDualFormNativeIntegratedAction_varyLorentzConnection_eq_full_restrictToIIPlus
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm)
    (parameter : ℝ) :
    holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction source
        chart (varyLorentzConnection configuration variation parameter) =
      holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        (varyLorentzConnection
          (restrictHolonomicConfigurationToIIPlus configuration)
          variation parameter) := by
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

/-- Stationarity of the computed-`II+` reduced functional is exactly full-root
stationarity on the computed restriction.  This is an action-path equality,
not an equation or solution supplied as a premise. -/
theorem
    diracDualFormNativeIIPlusReducedLorentzConnectionActionStationary_iff_restrictToIIPlus
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    DiracDualFormNativeIIPlusReducedLorentzConnectionActionStationary source
        configuration ↔
      DiracDualFormNativeLorentzConnectionActionStationary source
        (restrictHolonomicConfigurationToIIPlus configuration) := by
  constructor
  · intro reducedStationary variation
    have actionEquality :
        (fun parameter =>
          holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction
            source 0
            (varyLorentzConnection configuration variation parameter)) =
          fun parameter =>
            holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
              (varyLorentzConnection
                (restrictHolonomicConfigurationToIIPlus configuration)
                variation parameter) := by
      funext parameter
      exact
        holonomicIIPlusReducedDiracDualFormNativeIntegratedAction_varyLorentzConnection_eq_full_restrictToIIPlus
          source 0 configuration variation parameter
    rw [← actionEquality]
    exact reducedStationary variation
  · intro fullStationary variation
    have actionEquality :
        (fun parameter =>
          holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction
            source 0
            (varyLorentzConnection configuration variation parameter)) =
          fun parameter =>
            holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
              (varyLorentzConnection
                (restrictHolonomicConfigurationToIIPlus configuration)
                variation parameter) := by
      funext parameter
      exact
        holonomicIIPlusReducedDiracDualFormNativeIntegratedAction_varyLorentzConnection_eq_full_restrictToIIPlus
          source 0 configuration variation parameter
    rw [actionEquality]
    exact fullStationary variation

/-! ## Matter-coupled first-order connection equation -/

/-- The Lorentz-connection Euler locus of the actual computed-`II+` reduced
functional is exactly the torsion--spin balance generated by the repaired
root. -/
theorem
    diracDualFormNativeIIPlusReducedLorentzConnectionActionStationary_iff_torsionSpinEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        (restrictHolonomicConfigurationToIIPlus configuration)) :
    DiracDualFormNativeIIPlusReducedLorentzConnectionActionStationary source
        configuration ↔
      FormNativeIIPlusTorsionSpinEquation source configuration := by
  rw [
    diracDualFormNativeIIPlusReducedLorentzConnectionActionStationary_iff_restrictToIIPlus]
  exact
    diracDualFormNativeLorentzConnectionActionStationary_restrictToIIPlus_iff_torsionSpinEquation
      source configuration smooth admissible nondegenerate densityIntegrable

/-! ## Four-leg critical locus with the connection equation exposed -/

/-- The repaired full four-leg gravity locus reduces to simplicity, the
unique auxiliary reaction, reduced coframe stationarity, and the actual
matter-coupled torsion--spin equation.  This is a conditional critical-locus
equivalence; it does not assert that the locus is inhabited. -/
theorem
    diracDualFormNative_fourLegCriticalLocus_iff_reducedCoframeStationary_and_torsionSpin
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
      DiracDualFormNativeIIPlusReducedCoframeActionStationary source
        configuration ∧
      FormNativeIIPlusTorsionSpinEquation source configuration) := by
  constructor
  · intro fullLocus
    obtain ⟨simplicity, reaction, reducedCoframe, reducedConnection⟩ :=
      (diracDualFormNative_fourLegCriticalLocus_iff_reduced source
        configuration smooth nondegenerate densityIntegrable).1 fullLocus
    have fixedPoint :=
      (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
        configuration).2 simplicity
    have restrictedIntegrable :
        DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
          (restrictHolonomicConfigurationToIIPlus configuration) := by
      simpa only [fixedPoint] using densityIntegrable
    have torsionSpin :=
      (diracDualFormNativeIIPlusReducedLorentzConnectionActionStationary_iff_torsionSpinEquation
        source configuration smooth admissible nondegenerate
          restrictedIntegrable).1 reducedConnection
    exact ⟨simplicity, reaction, reducedCoframe, torsionSpin⟩
  · rintro ⟨simplicity, reaction, reducedCoframe, torsionSpin⟩
    have fixedPoint :=
      (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
        configuration).2 simplicity
    have restrictedIntegrable :
        DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
          (restrictHolonomicConfigurationToIIPlus configuration) := by
      simpa only [fixedPoint] using densityIntegrable
    have reducedConnection :=
      (diracDualFormNativeIIPlusReducedLorentzConnectionActionStationary_iff_torsionSpinEquation
        source configuration smooth admissible nondegenerate
          restrictedIntegrable).2 torsionSpin
    exact
      (diracDualFormNative_fourLegCriticalLocus_iff_reduced source
        configuration smooth nondegenerate densityIntegrable).2
          ⟨simplicity, reaction, reducedCoframe, reducedConnection⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusTorsionSpinCriticalLocus
