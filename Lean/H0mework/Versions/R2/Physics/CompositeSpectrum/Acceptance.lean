import H0mework.Versions.R2.Physics.CompositeSpectrum.Complement
import H0mework.Versions.R2.Physics.CompositeSpectrum.Parity
import H0mework.Versions.R2.Physics.CompositeSpectrum.Rotation

/-! Complete incoming-field provenance for the cubic spectrum and its
separate field, trace, and phase-Hamiltonian transformation laws. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracExteriorMatterAction MeasureTheory
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineGlobalBundle StageNineSpinMatterBundle
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open SU7ExteriorMatterRepresentation

noncomputable section

def evolvedFieldComposite (point displacement : BasePoint) : State.Observable :=
  star (Dynamics.unitary displacement : State.Observable) * responseMatrix (compositeAction point) *
    (Dynamics.unitary displacement : State.Observable)

theorem evolvedFieldComposite_eq (point displacement : BasePoint) :
    evolvedFieldComposite point displacement = evolvedCubic point displacement := by
  rw [evolvedFieldComposite, compositeAction_responseMatrix]
  rfl

theorem fieldComposite_vacuum_spectrum (point first second : BasePoint) :
    vacuumConnected (evolvedFieldComposite point first) (evolvedFieldComposite point second) =
      ∫ rate : ℝ, phase rate (second - first) ∂vacuumSpectralMeasure := by
  rw [evolvedFieldComposite_eq, evolvedFieldComposite_eq, vacuumConnected_spectralIntegral]

structure SourceFieldCompositeClosure : Prop extends SourceGroundSingletClosure where
  full_response : ∀ point, responseMatrix (compositeAction point) = cubic point
  runtime_dual : ∀ point,
    Runtime.configuration.conjugateMatter point (compositeAction point (Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Runtime.tick.answer point) (cubic point)
  gauge_ordered_action : ∀ element point matter,
    fullGaugeCompositeAction element point (Source.Frame.gaugeFrame element matter) =
      Source.Frame.gaugeFrame element (compositeAction point matter)
  spin_action : ∀ element point matter,
    compositeAction point (spinDiracMatterRepresentation element matter) =
      spinDiracMatterRepresentation element (compositeAction point matter)
  rotation_action : ∀ rotation point,
    rotatedCompositeAction (spatialRotationMatrix rotation) point = compositeAction point
  parity_action : ∀ point matter,
    parityCompositeAction point (parityFrame matter) = parityFrame (compositeAction point matter)
  trace_split : ∀ point,
    fullCompositeTrace point = 8 * (curvatureScale : ℂ) ^ 3 +
      LinearMap.trace ℂ DiracExteriorMatterCarrier (complementaryComposite point)
  not_scalar_full_action : ∀ point,
    compositeAction point ≠ (curvatureScale : ℂ) ^ 3 • (1 : Module.End ℂ DiracExteriorMatterCarrier)
  parity_changes_phase_H : occupiedParity * phaseHamiltonian * occupiedParity = -phaseHamiltonian
  parity_changes_ground : occupiedParity * groundProjector * occupiedParity = 1 - groundProjector
  incoming_spectrum : ∀ point first second,
    vacuumConnected (evolvedFieldComposite point first) (evolvedFieldComposite point second) =
      ∫ rate : ℝ, phase rate (second - first) ∂vacuumSpectralMeasure

theorem sourceFieldCompositeClosure : SourceFieldCompositeClosure where
  toSourceGroundSingletClosure := sourceGroundSingletClosure
  full_response := compositeAction_responseMatrix
  runtime_dual := compositeAction_quantum_response
  gauge_ordered_action := fullGaugeCompositeAction_intertwines
  spin_action := compositeAction_spin
  rotation_action := compositeAction_spatialRotation
  parity_action := compositeAction_parity
  trace_split := fullCompositeTrace_decomposition
  not_scalar_full_action := compositeAction_not_full_scalar
  parity_changes_phase_H := phaseHamiltonian_parity
  parity_changes_ground := groundProjector_parity
  incoming_spectrum := fieldComposite_vacuum_spectrum

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
