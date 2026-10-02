import H0mework.Versions.R2.Physics.CompositeSpectrum.Acceptance
import H0mework.Versions.R2.Physics.Helicity.Color
import H0mework.Versions.R2.Physics.Helicity.GaugeAction
import H0mework.Versions.R2.Physics.Helicity.Rotation
import H0mework.Versions.R2.Physics.Helicity.Spectrum
import H0mework.Versions.R2.Physics.Helicity.PhysicalSpectrum

/-! The nonzero P-odd / pure-gauge C-even helicity producer keeps the mother
trace, the ordered matter action, and its independent-dual response distinct.
The current-based operator is the readout of the same physical gauge trace. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity

open Matrix MeasureTheory
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineP286GaugeAuxiliaryVariation SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation Stage9C.Material.SpinPair Stage9DEF

noncomputable section

structure SourceHelicityClosure : Prop extends SourceFieldCompositeClosure where
  source_value : ∀ point, value point = (3 * gaugeScale ^ 5 : ℝ)
  source_nonzero : ∀ point, value point ≠ 0
  color_alignment : ∀ point, value point = colorValue point
  gauge_trace : ∀ element point,
    homogeneousHelicity (fun i => gaugeMap element (connectionMatrix point i))
      (fun i => gaugeMap element (motherMagnetic point i)) = value point
  parity_trace : ∀ point,
    homogeneousHelicity (parityConnection point) (parityMagnetic point) = -value point
  charge_trace : ∀ point,
    homogeneousHelicity (fun i => charge (connectionMatrix point i))
      (fun i => charge (motherMagnetic point i)) = value point
  rotation_trace : ∀ rotation point,
    homogeneousHelicity (mixComponents (spatialRotationMatrix rotation) (connectionMatrix point))
      (mixComponents (spatialRotationMatrix rotation) (motherMagnetic point)) = value point
  actual_current : ∀ point axis probe,
    p286LiePairing (covariantCurl point axis) probe =
      sourceCoupling * lapse ^ 2 * currentRead point axis probe
  current_trace_identity : ∀ point,
    value point = (-sourceCoupling * lapse ^ 2 *
      ∑ axis : Fin 3, currentRead point axis (magnetic point axis) : ℝ)
  same_quantity_operator : ∀ point, State.evaluation point (physicalObservable point) = value point
  same_quantity_stationary : ∀ point displacement,
    evolvedPhysical point displacement = physicalObservable point
  same_quantity_connected : ∀ point first second,
    connected point (evolvedPhysical point first) (evolvedPhysical point second) = 0
  ordered_action_response : ∀ point,
    Runtime.configuration.conjugateMatter point (action point (Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Runtime.tick.answer point) (observable point)
  ordered_action_gauge : ∀ element point, movedObservable element point = observable point
  distinct_readouts : observable 0 ≠ physicalObservable 0
  ordered_response_spectrum : ∀ point first second,
    vacuumConnected (evolved point first) (evolved point second) =
      ∫ rate : ℝ, phase rate (second - first) ∂spectralMeasure
  ordered_response_atom : spectralMeasure {spectralFrequency} ≠ 0
  ordered_response_support : spectralMeasure {spectralFrequency}ᶜ = 0
  ordered_response_excitation : ∀ point, observable point * groundProjector ≠ 0
  ordered_response_gap : ∀ point,
    (phaseHamiltonian + (frequency : ℂ) • 1) * (observable point * groundProjector) =
      (spectralFrequency : ℂ) • (observable point * groundProjector)

theorem sourceHelicityClosure : SourceHelicityClosure where
  toSourceFieldCompositeClosure := sourceFieldCompositeClosure
  source_value := value_eq
  source_nonzero := value_nonzero
  color_alignment := fullMother_eq_color
  gauge_trace := actual_fullGauge_invariant
  parity_trace := actual_parity_odd
  charge_trace := actual_charge_even
  rotation_trace := actual_rotation_invariant
  actual_current := covariantCurl_current
  current_trace_identity := value_from_actual_current
  same_quantity_operator := physicalObservable_value
  same_quantity_stationary := evolvedPhysical_stationary
  same_quantity_connected := physical_connected_zero
  ordered_action_response := actual_quantum_response
  ordered_action_gauge := movedObservable_eq
  distinct_readouts := ordered_response_ne_physical
  ordered_response_spectrum := connected_spectralIntegral
  ordered_response_atom := spectral_atom_nonzero
  ordered_response_support := spectral_outside
  ordered_response_excitation := excitation_nonzero
  ordered_response_gap := positive_gap

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity
