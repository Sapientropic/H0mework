import H0mework.Physics.Geometry.JointShellZeroFiber
import H0mework.Physics.Coframe.CoframeEquation
import H0mework.Physics.GaugeAction.P286Bianchi
import H0mework.Physics.Geometry.GravityBianchi

/-!
# S9-C3g3: domain layers and stationarity-to-zero transport

This module keeps four logically different layers separate:

1. the data-only joint residual carrier;
2. smooth/holonomic and Bianchi readouts;
3. nondegenerate Lorentz-admissible and integrable action domains;
4. stationarity of all nine primitive variation channels.

Full stationarity implies that the generated residual section lies in its zero
fiber.  The converse is deliberately not claimed.  None of these predicates
is inserted into the source or residual carrier.
-/

namespace SaturationMonoid.PhysicsCore.StageNineJointShellStationarity

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNinePlebanskiMultiplierVariation
open StageNineGravityAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionWeakEquation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineLorentzConnectionWeakEquation
open StageNineLorentzConnectionPointwiseEquation
open StageNineConjugateMatterVariation
open StageNineMatterVariation
open StageNineMatterPointwiseEquation
open StageNineScalarVariation
open StageNineScalarPointwiseEquation
open StageNineCoframeIntegratedVariation
open StageNineCoframePointwiseEquation
open StageNineCoframeEquation
open StageNineP286Bianchi
open StageNineGravityBianchi
open StageNineJointShellResidualCarrier
open StageNineJointShellZeroFiber

noncomputable section

set_option autoImplicit false

/-- Smooth local-holonomic zero-fiber layer.  Holonomicity is already carried
by the configuration type; smoothness is kept as an external predicate. -/
structure CurrentSmoothJointShellZeroFiber
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop where
  smooth : configuration.Smooth
  zeroFiber : CurrentJointShellZeroFiber source configuration

/-- Interpretation layer for Lorentzian gravity.  Neither field is a residual
slot: nondegeneracy controls faithful pairings, while Lorentz admissibility
controls the `so(1,3)` interpretation of the primitive mixed connection. -/
structure CurrentLorentzAdmissibleJointShellZeroFiber
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop where
  smooth : configuration.Smooth
  nondegenerate : configuration.Nondegenerate
  gravityConnectionLorentzAdmissible :
    GravityConnectionLorentzAdmissible configuration
  zeroFiber : CurrentJointShellZeroFiber source configuration

/-- Absolute-action analytic domain layer.  It records the current raw
Bochner integrability predicate; it does not rename it as relative,
renormalized, finite-energy, or finite-action data. -/
structure CurrentIntegrableJointShellZeroFiber
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop where
  smooth : configuration.Smooth
  nondegenerate : configuration.Nondegenerate
  gravityConnectionLorentzAdmissible :
    GravityConnectionLorentzAdmissible configuration
  densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration
  zeroFiber : CurrentJointShellZeroFiber source configuration

/-- Stationarity under exactly the nine primitive variation channels used by
the joint carrier.  Hypercharge is not repeated beside the full P286 auxiliary
variation. -/
structure CurrentFullActionStationary
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop where
  gravitySimplicityMultiplier :
    GravitySimplicityMultiplierActionStationary source 0 configuration
  gravityAuxiliary : GravityAuxiliaryActionStationary source 0 configuration
  p286GaugeAuxiliary :
    P286GaugeAuxiliaryActionStationary source 0 configuration
  lorentzConnection :
    CanonicalLorentzConnectionActionStationary source configuration
  p286GaugeConnection :
    CanonicalP286GaugeConnectionActionStationary source configuration
  scalar : CanonicalScalarActionStationary source configuration
  matter : CanonicalMatterActionStationary source configuration
  conjugateMatter :
    CanonicalConjugateMatterActionStationary source configuration
  coframe : CanonicalCoframeActionStationaryF source configuration

/-- The gravity Bianchi identity is an off-shell readout of smooth holonomic
curvature.  Joint-shell zero is intentionally not consumed. -/
theorem smooth_implies_gravityBianchi
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantMixedCurvatureDerivative configuration point first second third +
        covariantMixedCurvatureDerivative configuration point second third
          first +
        covariantMixedCurvatureDerivative configuration point third first
          second = 0 :=
  holonomicGravityGL4Curvature_bianchi configuration smooth point first second
    third

/-- The full P286 Bianchi identity is likewise off shell. -/
theorem smooth_implies_p286GaugeBianchi
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantCurvatureDerivative configuration point first second third +
        covariantCurvatureDerivative configuration point second third first +
        covariantCurvatureDerivative configuration point third first second =
      0 :=
  holonomicP286GaugeCurvature_bianchi configuration smooth point first second
    third

theorem currentFullActionStationary_implies_strongEquation
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CurrentFullActionStationary source configuration) :
    CurrentStrongJointShellEquation source configuration := by
  have gravitySimplicity : GravitySimplicityEquation configuration :=
    gravitySimplicityMultiplierActionStationary_implies_simplicity source 0
      configuration smooth nondegenerate densityIntegrable
        stationary.gravitySimplicityMultiplier
  constructor
  · exact gravitySimplicity
  · exact gravityAuxiliaryActionStationary_implies_equation source 0
      configuration smooth nondegenerate densityIntegrable gravitySimplicity
        stationary.gravityAuxiliary
  · exact p286GaugeAuxiliaryActionStationary_implies_equation source 0
      configuration smooth nondegenerate densityIntegrable
        stationary.p286GaugeAuxiliary
  · apply canonicalLorentzConnectionWeakEquation_implies_pointwiseEquation
      source configuration smooth nondegenerate
    exact canonicalLorentzConnectionActionStationary_implies_weakEquation
      source configuration smooth nondegenerate densityIntegrable
        stationary.lorentzConnection
  · apply canonicalP286GaugeConnectionWeakEquation_implies_pointwiseEquation
      source configuration smooth nondegenerate
    exact canonicalP286GaugeConnectionActionStationary_implies_weakEquation
      source configuration smooth nondegenerate densityIntegrable
        stationary.p286GaugeConnection
  · exact canonicalScalarActionStationary_implies_pointwiseEquation source
      configuration smooth nondegenerate densityIntegrable stationary.scalar
  · exact canonicalMatterActionStationary_implies_pointwiseEquation source
      configuration smooth nondegenerate densityIntegrable stationary.matter
  · apply canonicalConjugateMatterWeakEquation_implies_pointwiseEquation source
      configuration smooth nondegenerate
    exact canonicalConjugateMatterActionStationary_implies_weakEquation source
      configuration smooth nondegenerate densityIntegrable
        stationary.conjugateMatter
  · exact canonicalCoframeActionStationaryF_implies_pointwiseEquation source
      configuration smooth nondegenerate densityIntegrable stationary.coframe

/-- The main C3g3 transport: actual stationarity of all nine channels sends
the generated residual section to zero.  This theorem has no converse. -/
theorem currentFullActionStationary_implies_jointShellZeroFiber
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CurrentFullActionStationary source configuration) :
    CurrentJointShellZeroFiber source configuration :=
  (currentJointShellZeroFiber_iff_strongEquation source configuration).mpr
    (currentFullActionStationary_implies_strongEquation source configuration
      smooth nondegenerate densityIntegrable stationary)

end

end SaturationMonoid.PhysicsCore.StageNineJointShellStationarity
