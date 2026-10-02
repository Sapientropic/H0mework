import H0mework.Versions.R2.Physics.GaugeSpectrum.Hilbert
import H0mework.Versions.R2.Physics.RootRuntime.RuntimeOccurrence

/-! The new response is a dependent read of the existing Stage-10 occurrence.
Promotion into the living root's next inquiry is owned by its controller. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracExteriorMatterAction MeasureTheory
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation
open scoped ComplexOrder

noncomputable section

theorem occurrence_curvature_response (point : BasePoint) (axis : Fin 3) :
    Runtime.configuration.conjugateMatter point
      (Complex.I • diracExteriorMotherLieAction
        (p286LieBlockEmbed (holonomicGaugeCurvature Runtime.configuration point (magneticPair axis)))
        (Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) *
        State.vectorEvaluation (Runtime.tick.answer point) (dualCurvature point axis) := by
  rw [Runtime.configuration_eq, Runtime.tick_vector]
  exact dualCurvature_actual_response point axis

structure SourceCurvatureSpectralClosure : Prop where
  source_response : ∀ point axis,
    actual.conjugateMatter point (curvatureAction point axis (actual.matter point)) =
      4 * (spinScale : ℂ) * State.evaluation point (dualCurvature point axis)
  nonzero_connected : ∀ point axis,
    connected point (dualCurvature point axis) (dualCurvature point axis) ≠ 0
  spectral_integral : ∀ point first second axis,
    connected point (evolvedDualCurvature point first axis)
      (evolvedDualCurvature point second axis) =
      ∫ rate : ℝ, phase rate (second - first) ∂spectralMeasure
  positive_atom : spectralMeasure {spectralFrequency} ≠ 0
  negative_atom : spectralMeasure {-spectralFrequency} ≠ 0
  exact_support : spectralMeasure ({spectralFrequency, -spectralFrequency}ᶜ) = 0
  nonconstant : ∀ point axis,
    (fun displacement => connected point (evolvedDualCurvature point 0 axis)
      (evolvedDualCurvature point displacement axis)) ≠ (fun _ => (curvatureScale : ℂ) ^ 2)
  full_gauge : ∀ element point first second axis,
    State.vectorEvaluation
      (Source.Frame.prepare (Source.Frame.gaugeFrame element)
        (diracExteriorMatterGaugeRepresentation element (actual.matter point)))
      (star (movedEvolvedCurvature element point first axis) *
        movedEvolvedCurvature element point second axis) =
      ∫ rate : ℝ, phase rate (second - first) ∂spectralMeasure
  positive_gram : ∀ {ι : Type} [Fintype ι] point (samples : ι → BasePoint) axis,
    (correlationMatrix point samples axis).PosSemidef
  phase_flow : AffineRelaxation.BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate
    (EuclideanSpace ℂ Source.Index) phaseHamiltonianOperator

theorem sourceCurvatureSpectralClosure : SourceCurvatureSpectralClosure where
  source_response := dualCurvature_actual_response
  nonzero_connected := dualCurvature_connected_nonzero
  spectral_integral := connected_eq_spectralIntegral
  positive_atom := spectralMeasure_positive_atom_nonzero
  negative_atom := spectralMeasure_negative_atom_nonzero
  exact_support := spectralMeasure_outside
  nonconstant := temporal_connected_nonconstant
  full_gauge := fullGauge_connected_spectrum
  positive_gram := correlationMatrix_posSemidef
  phase_flow := phaseHamiltonian_flow

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
