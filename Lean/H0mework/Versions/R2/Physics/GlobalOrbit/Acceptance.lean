import H0mework.Versions.R2.Physics.GlobalOrbit.Observable

/-! Source-generated global completion of the exact nonlinear gauge–Dirac
trajectory, consuming the prior local closure without changing its source. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeMatterVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation Stage9C.Material.SpinPair

noncomputable section

structure SourceGlobalDynamicsClosure : Prop extends SourceNonlinearDynamicsClosure where
  global_generated : ∀ impulse, Nonempty (CompleteOrbit impulse)
  global_initial : ∀ impulse, (completeOrbit impulse).curve 0 = Nonlinear.seed impulse
  global_evolves : ∀ impulse time,
    HasDerivAt (completeOrbit impulse).curve (generator ((completeOrbit impulse).curve time)) time
  global_unique : ∀ impulse (first second : CompleteOrbit impulse), first.curve = second.curve
  global_extends_local : ∀ impulse time, time ∈ (Nonlinear.orbit impulse).window →
    (completeOrbit impulse).curve time = (Nonlinear.orbit impulse).curve time
  global_zero_source : ∀ time, (completeOrbit 0).curve time = (gaugeScale, 0, frequency*time)
  global_gauge : ∀ impulse point,
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0 (completeOrbit impulse).configuration point = 0
  global_primal : ∀ impulse point,
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (completeOrbit impulse).configuration point) = 0
  global_adjoint : ∀ impulse point variation,
    diracDualMatterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      (completeOrbit impulse).configuration variation point = 0
  global_quantity : ∀ impulse point,
    (completeOrbit impulse).fieldValue point = (completeOrbit impulse).helicity (point 0)
  global_Q_velocity : ∀ impulse,
    HasDerivAt (completeOrbit impulse).helicity (15*gaugeScale^4*impulse/inertia) 0
  global_Q_changes : ∀ impulse, impulse ≠ 0 → ∃ point : BasePoint,
    (completeOrbit impulse).fieldValue point ≠ (completeOrbit impulse).fieldValue 0
  global_energy : ∀ impulse time,
    hamiltonian ((completeOrbit impulse).curve time) = hamiltonian (Nonlinear.seed impulse)
  global_momentum_bound : ∀ impulse time, ((completeOrbit impulse).curve time).2.1^2 ≤ impulse^2
  global_amplitude_bound : ∀ impulse time,
    coercivity*(((completeOrbit impulse).curve time).1-gaugeScale)^2 ≤ excess impulse

theorem sourceGlobalDynamicsClosure : SourceGlobalDynamicsClosure where
  toSourceNonlinearDynamicsClosure := sourceNonlinearDynamicsClosure
  global_generated := completeOrbit_exists
  global_initial := fun impulse => (completeOrbit impulse).starts
  global_evolves := fun impulse time => (completeOrbit impulse).evolves time
  global_unique := fun _ => CompleteOrbit.unique
  global_extends_local := fun impulse time inside => (completeOrbit impulse).extends_local time inside
  global_zero_source := fun time => (completeOrbit 0).zero_recovers time
  global_gauge := fun impulse point => (completeOrbit impulse).gaugeEuler_zero point
  global_primal := fun impulse point => (completeOrbit impulse).primalEuler_zero point
  global_adjoint := fun impulse point variation => (completeOrbit impulse).adjointEuler_zero point variation
  global_quantity := fun impulse point => (completeOrbit impulse).fieldValue_helicity point
  global_Q_velocity := fun impulse => (completeOrbit impulse).initialQ_derivative
  global_Q_changes := fun impulse nonzero => (completeOrbit impulse).field_changes nonzero
  global_energy := fun impulse time => (completeOrbit impulse).energy_conserved time
  global_momentum_bound := fun impulse time => (completeOrbit impulse).momentum_bound time
  global_amplitude_bound := fun impulse time => (completeOrbit impulse).amplitude_bound time

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global
