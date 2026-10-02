import H0mework.Versions.R2.Physics.NonlinearOrbit.Baseline

/-! Exact nonlinear source-action gauge–Dirac local flow, its full-field Q,
energy confinement, uniqueness and reached-state continuation. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeMatterVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation StageNineFormNativeChargedGaugeCurrentThreeForm

noncomputable section

structure SourceNonlinearDynamicsClosure : Prop extends SourceRadialDynamicsClosure where
  canonical_generator : ∀ state : PhaseSpace,
    generator state = (state.2.1/inertia, -restoring state.1, 3*lapse/2*(spinScale-state.1))
  generated_orbit : ∀ impulse, Nonempty (LocalOrbit (seed impulse) 0)
  nonlinear_initial : ∀ impulse, (orbit impulse).curve 0 = (gaugeScale, impulse, 0)
  nonlinear_initial_velocity : ∀ impulse, HasDerivAt (orbit impulse).amplitude (impulse/inertia) 0
  nonlinear_evolves : ∀ impulse time, time ∈ (orbit impulse).window →
    HasDerivAt (orbit impulse).curve (generator ((orbit impulse).curve time)) time
  nonlinear_auxiliary : ∀ impulse point, point 0 ∈ (orbit impulse).window →
    (orbit impulse).configuration.gaugeAuxiliary point =
      radialAuxiliary ((orbit impulse).amplitude (point 0)) ((orbit impulse).velocity (point 0))
  whole_current : ∀ impulse point,
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (orbit impulse).configuration point) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
        (toContinuumPointField Runtime.configuration point)
  whole_gauge : ∀ impulse point, point 0 ∈ (orbit impulse).window →
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0 (orbit impulse).configuration point = 0
  whole_primal : ∀ impulse point, point 0 ∈ (orbit impulse).window →
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (orbit impulse).configuration point) = 0
  whole_adjoint : ∀ impulse point, point 0 ∈ (orbit impulse).window → ∀ variation,
    diracDualMatterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      (orbit impulse).configuration variation point = 0
  nonlinear_quantity : ∀ impulse point, point 0 ∈ (orbit impulse).window →
    (orbit impulse).fieldValue point = (orbit impulse).helicity (point 0)
  nonlinear_Q_velocity : ∀ impulse,
    HasDerivAt (orbit impulse).helicity (15*gaugeScale^4*impulse/inertia) 0
  nonlinear_Q_changes : ∀ impulse, impulse ≠ 0 → ∃ point : BasePoint,
    point 0 ∈ (orbit impulse).window ∧ (orbit impulse).fieldValue point ≠ (orbit impulse).fieldValue 0
  nonlinear_energy : ∀ impulse time, time ∈ (orbit impulse).window →
    hamiltonian ((orbit impulse).curve time) = hamiltonian (seed impulse)
  momentum_bound : ∀ impulse time, time ∈ (orbit impulse).window →
    ((orbit impulse).momentum time)^2 ≤ impulse^2
  amplitude_bound : ∀ impulse time, time ∈ (orbit impulse).window →
    (3*gaugeScale^2/(2*sourceCoupling*lapse))*((orbit impulse).amplitude time-gaugeScale)^2 ≤ impulse^2/(2*inertia)
  nonlinear_unique : ∀ initial initialTime (first second : LocalOrbit initial initialTime),
    Set.EqOn first.curve second.curve (first.window ∩ second.window)
  reached_continuation : ∀ impulse time, time ∈ (orbit impulse).window →
    Nonempty (Continuation (orbit impulse) time)
  zero_recovers_source : ∀ time, time ∈ (orbit 0).window → (orbit 0).curve time = (gaugeScale, 0, frequency*time)

theorem sourceNonlinearDynamicsClosure : SourceNonlinearDynamicsClosure where
  toSourceRadialDynamicsClosure := sourceRadialDynamicsClosure
  canonical_generator := generator_eq
  generated_orbit := fun impulse => localOrbit_exists (seed impulse) 0
  nonlinear_initial := orbit_source
  nonlinear_initial_velocity := orbit_initial_velocity
  nonlinear_evolves := fun impulse time inside => (orbit impulse).evolves time inside
  nonlinear_auxiliary := fun impulse point inside => (orbit impulse).auxiliary point inside
  whole_current := fun impulse point => (orbit impulse).chargedThreeForm point
  whole_gauge := fun impulse point inside => (orbit impulse).gaugeEuler_zero point inside
  whole_primal := fun impulse point inside => (orbit impulse).primalEuler_zero point inside
  whole_adjoint := fun impulse point inside variation => (orbit impulse).adjointEuler_zero point inside variation
  nonlinear_quantity := fun impulse point inside => (orbit impulse).fieldValue_helicity point inside
  nonlinear_Q_velocity := orbit_helicity_derivative
  nonlinear_Q_changes := orbit_field_changes
  nonlinear_energy := fun impulse time inside => (orbit impulse).energy_conserved time inside
  momentum_bound := orbit_momentum_bound
  amplitude_bound := orbit_amplitude_bound
  nonlinear_unique := fun _ _ => LocalOrbit.unique_on
  reached_continuation := fun impulse time inside => (orbit impulse).continuation_exists time inside
  zero_recovers_source := orbit_zero_recovers

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
