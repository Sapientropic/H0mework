import H0mework.Physics.Jets.IIPlusJetKinematics
import H0mework.Physics.Lorentz.LorentzPointwiseEquation

/-!
# Form-native Lorentz equation on the computed `II+` actual

The form-native action has already generated and faithfully localized its
Lorentz equation as `D_omega B = J_spin`.  This module specializes that
equation to the same computed restricted actual `B := II+(e)` and uses the
actual whole-field jet/KIN-1 transporter to obtain

```text
star_internal (T(omega,e) wedge e) = J_spin.
```

This is an action-derived equation characterization.  It neither asserts
that an arbitrary configuration is stationary nor constructs a torsion or
contorsion solution.  The restriction remains a derived actual, so the result
does not retroactively prove simplicity of the unreduced input and does not
select a root formulation.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeLorentzTorsionSpinEquation

open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineEnrichedProofFreeSource
open StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeLorentzConnectionIntegratedVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzPointwiseEquation
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineResidualLinearPlebanskiTorsionReduction

noncomputable section

set_option autoImplicit false

/-- Torsion--spin balance on the same actual obtained by computing
`B := II+(e)`.  The current is still read from that restricted point field;
no matter or current coordinate is copied from an unrelated configuration. -/
def FormNativeIIPlusTorsionSpinEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point : BasePoint,
    internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm (configuration.coframe point)
          (pointwiseCartanTorsion
            (holonomicCoframeFirstJetAt configuration.coframe point)
            (configuration.gravityConnection point))) =
      formNativePhysicalSpinCurrentThreeForm source 0 point
        (toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus configuration) point)

/-- Faithful pointwise specialization of the action-derived connection
equation to the computed `II+` actual.  KIN-1 changes only the geometric
representation of the left-hand side. -/
theorem
    formNativeLorentzConnectionPointwiseEquation_restrictToIIPlus_iff_torsionSpinEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration) :
    FormNativeLorentzConnectionPointwiseEquation source
        (restrictHolonomicConfigurationToIIPlus configuration) ↔
      FormNativeIIPlusTorsionSpinEquation source configuration := by
  constructor
  · intro pointwiseEquation point
    rw [←
      holonomicGravityAuxiliaryExteriorCovariantDerivative_restrictToIIPlus_eq_torsionCoframe
        configuration smooth admissible point]
    exact pointwiseEquation point
  · intro torsionSpinEquation point
    rw [
      holonomicGravityAuxiliaryExteriorCovariantDerivative_restrictToIIPlus_eq_torsionCoframe
        configuration smooth admissible point]
    exact torsionSpinEquation point

/-- Final thin action consumer for this checkpoint.  It states what
stationarity of the form-native action means on the computed restricted
actual; it does not supply stationarity or a solution as a premise. -/
theorem
    formNativeLorentzConnectionActionStationary_restrictToIIPlus_iff_torsionSpinEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      FormNativeHolonomicLocalDensityIntegrable source 0
        (restrictHolonomicConfigurationToIIPlus configuration)) :
    FormNativeLorentzConnectionActionStationary source
        (restrictHolonomicConfigurationToIIPlus configuration) ↔
      FormNativeIIPlusTorsionSpinEquation source configuration := by
  have restrictedSmooth :
      (restrictHolonomicConfigurationToIIPlus configuration).Smooth :=
    restrictHolonomicConfigurationToIIPlus_smooth configuration smooth
  have restrictedAdmissible :
      GravityConnectionLorentzAdmissible
        (restrictHolonomicConfigurationToIIPlus configuration) :=
    (restrictHolonomicConfigurationToIIPlus_lorentzAdmissible_iff
      configuration).2 admissible
  have restrictedNondegenerate :
      (restrictHolonomicConfigurationToIIPlus
        configuration).Nondegenerate :=
    (restrictHolonomicConfigurationToIIPlus_nondegenerate_iff
      configuration).2 nondegenerate
  rw [formNativeLorentzConnectionActionStationary_iff_pointwiseEquation
    source (restrictHolonomicConfigurationToIIPlus configuration)
    restrictedSmooth restrictedAdmissible restrictedNondegenerate
    densityIntegrable]
  exact
    formNativeLorentzConnectionPointwiseEquation_restrictToIIPlus_iff_torsionSpinEquation
      source configuration smooth admissible

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeLorentzTorsionSpinEquation
