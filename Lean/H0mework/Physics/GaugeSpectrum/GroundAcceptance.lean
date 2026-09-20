import H0mework.Physics.GaugeSpectrum.Acceptance
import H0mework.Physics.GaugeSpectrum.Vacuum
import H0mework.Physics.GaugeSpectrum.Singlet

/-! The source phase Hamiltonian generates its own ground preparation and
the source magnetic triad generates a singlet composite with positive gap. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracExteriorMatterAction MeasureTheory
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF SU7MotherLieAlgebra SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation SU7ExteriorMatterGaugeCovariantJet
open scoped ComplexOrder

noncomputable section

structure SourceGroundSingletClosure : Prop extends SourceCurvatureSpectralClosure where
  root_configuration : Runtime.configuration = actual
  root_read : Runtime.tick.answer = Source.vector
  connection_transport : ∀ element point pair,
    motherCurvature (constantGaugeTransformMotherConnection element (actualMotherConnection point)) pair =
      motherGaugeConjugate element (p286LieBlockEmbed (holonomicGaugeCurvature actual point pair))
  actual_phase_derivative : ∀ point time,
    HasDerivAt (fun t : ℝ => Source.vector (point + Dynamics.timeDisplacement t))
      (fun index => -Complex.I *
        (phaseHamiltonian *ᵥ Source.vector (point + Dynamics.timeDisplacement time)) index) time
  lower_bound : (phaseHamiltonian + (frequency : ℂ) • 1).PosSemidef
  bottom_projector : phaseHamiltonian * groundProjector = -(frequency : ℂ) • groundProjector
  ground_positive : groundDensity.PosSemidef
  ground_normalized : groundDensity.trace = 1
  ground_stationary : ∀ displacement,
    star (Dynamics.unitary displacement : State.Observable) * groundDensity *
      (Dynamics.unitary displacement : State.Observable) = groundDensity
  ground_functional_positive : ∀ observable : State.Observable,
    observable.PosSemidef → 0 ≤ groundEvaluation observable
  singlet_recovers : ∀ point, Compatibility.compression (singletAction point) = cubic point
  full_singlet : ∀ point element matter,
    singletAction point (diracExteriorMatterGaugeRepresentation element matter) =
      diracExteriorMatterGaugeRepresentation element (singletAction point matter)
  composite_evolution : ∀ point displacement,
    evolvedCubic point displacement = orientedCubic (evolvedDualCurvature point displacement)
  excitation_nonzero : ∀ point, cubic point * groundProjector ≠ 0
  excitation_gap : ∀ point,
    (phaseHamiltonian + (frequency : ℂ) • 1) * (cubic point * groundProjector) =
      (spectralFrequency : ℂ) • (cubic point * groundProjector)
  gap_positive : 0 < spectralFrequency
  vacuum_spectrum : ∀ point first second,
    vacuumConnected (evolvedCubic point first) (evolvedCubic point second) =
      ∫ rate : ℝ, phase rate (second - first) ∂vacuumSpectralMeasure
  vacuum_atom_nonzero : vacuumSpectralMeasure {spectralFrequency} ≠ 0
  vacuum_exact_support : vacuumSpectralMeasure {spectralFrequency}ᶜ = 0

theorem sourceGroundSingletClosure : SourceGroundSingletClosure where
  toSourceCurvatureSpectralClosure := sourceCurvatureSpectralClosure
  root_configuration := Runtime.configuration_eq
  root_read := Runtime.tick_vector
  connection_transport := actualMotherConnection_fullGauge
  actual_phase_derivative := actual_vector_schrodinger
  lower_bound := phaseHamiltonian_lowerBound
  bottom_projector := groundProjector_ground
  ground_positive := groundDensity_positive
  ground_normalized := groundDensity_trace
  ground_stationary := groundDensity_stationary
  ground_functional_positive := groundEvaluation_positive
  singlet_recovers := singletAction_recovers_cubic
  full_singlet := singletAction_fullSU7
  composite_evolution := evolvedCubic_from_evolved_curvature
  excitation_nonzero := cubic_excitation_nonzero
  excitation_gap := cubic_positive_gap
  gap_positive := spectralFrequency_pos
  vacuum_spectrum := vacuumConnected_spectralIntegral
  vacuum_atom_nonzero := vacuumSpectralMeasure_atom_nonzero
  vacuum_exact_support := vacuumSpectralMeasure_outside

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
