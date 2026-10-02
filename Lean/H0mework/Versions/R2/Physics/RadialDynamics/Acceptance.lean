import H0mework.Versions.R2.Physics.RadialDynamics.Equation
import H0mework.Versions.R2.Physics.RadialDynamics.Dual
import H0mework.Versions.R2.Physics.MatrixResponse.Acceptance

/-! Source-action radial Jacobi dynamics with a nonzero response of the
same full-mother Q. The original coframe and Cartan spin are fixed backgrounds. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineDiracKineticLocalSpinDensity Stage9C.Material.SpinPair
open StageNineP286GaugeAuxiliaryVariation SU7MotherLieAlgebra
open StageNineP286GaugeConnectionVariation

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

structure SourceRadialDynamicsClosure : Prop extends MatrixResponse.SourceMatrixHelicityClosure where
  original_primitive : radialWrite (fun _ => gaugeScale) = Runtime.configuration
  original_constitutive : radialReadout (fun _ => gaugeScale) = Runtime.configuration
  profile_curvature : ∀ parameter point,
    holonomicGaugeCurvature (radialWrite (responseProfile parameter)) point =
      radialCurvature (responseProfile parameter (point 0)) (responseVelocity parameter (point 0))
  actual_auxiliary : ∀ parameter point,
    (radialReadout (responseProfile parameter)).gaugeAuxiliary point =
      radialAuxiliary (responseProfile parameter (point 0)) (responseVelocity parameter (point 0))
  native_density : ∀ amplitude velocity,
    gaugeLagrangian amplitude velocity =
      3*lapse/(4*sourceCoupling)*velocity^2 - 3/(4*sourceCoupling*lapse)*amplitude^4
  actual_load : sourceLoad = 6*lapse*spinScale
  joint_action : ∀ amplitude velocity rate angle,
    gaugeLagrangian amplitude velocity + generatedDensitizedContinuumMatterKineticDensity
      positiveSmoothUnifiedSource 0 0 (matterJet amplitude rate angle) =
      lagrangian amplitude velocity + 4*spinScale*rate - 6*lapse*spinScale^2
  phase_derivative : ∀ parameter time,
    HasDerivAt (responseAngle parameter) (3*lapse/2*(spinScale-responseProfile parameter time)) time
  matter_derivative : ∀ parameter time,
    HasDerivAt (fun t => matterCoordinateEquiv (movingMatter (responseAngle parameter t)))
      (matterCoordinateEquiv (temporalMatter (deriv (responseAngle parameter) time)
        (responseAngle parameter time))) time
  dual_derivative : ∀ parameter time variation,
    HasDerivAt (fun t => movingDual (responseAngle parameter t) variation)
      (temporalDual (deriv (responseAngle parameter) time) (responseAngle parameter time) variation) time
  primal_kinetic : ∀ parameter time,
    generatedContinuumMatterKineticVector positiveSmoothUnifiedSource 0 0
      (matterJet (responseProfile parameter time) (deriv (responseAngle parameter) time)
        (responseAngle parameter time)) = 0
  adjoint_kinetic : ∀ parameter time variation,
    adjointJet (responseProfile parameter time) (deriv (responseAngle parameter) time)
      (responseAngle parameter time) variation = 0
  current_preserved : ∀ angle axis probe,
    (spinPairCurrentComplex axis.succ probe ((spinScale : ℂ)*unitPhase angle)
      ((spinScale : ℂ)*unitPhase (-angle)) (unitPhase angle) (unitPhase (-angle))).re =
      4*spinScale*p286LiePairing (sourceColorP286Generator axis) probe
  original_equilibrium : restoring gaugeScale = 0
  action_euler : ∀ amplitude acceleration,
    inertia*acceleration + restoring amplitude = (3/2:ℝ)*force amplitude acceleration
  positive_hessian : 0 < inertia ∧ 0 < stiffness
  source_frequency : 0 < responseFrequency ∧ responseFrequency^2 = 10
  legendre : ∀ amplitude canonicalMomentum,
    energy amplitude canonicalMomentum = canonicalMomentum^2/(2*inertia) + potential amplitude
  exact_hessian : ∀ parameter displacement canonicalMomentum,
    energy (gaugeScale+parameter*displacement) (parameter*canonicalMomentum) = energy gaugeScale 0 +
      parameter^2*quadraticEnergy displacement canonicalMomentum +
      3*gaugeScale/(sourceCoupling*lapse)*parameter^3*displacement^3 +
      3/(4*sourceCoupling*lapse)*parameter^4*displacement^4
  canonical_flow : ∀ time,
    HasDerivAt impulse (deriv (quadraticEnergy (impulse time)) (impulseMomentum time)) time ∧
    HasDerivAt impulseMomentum (-deriv (fun q => quadraticEnergy q (impulseMomentum time)) (impulse time)) time
  native_euler_response : ∀ point, HasDerivAt (fun parameter => nativeGaugeJet parameter point) 0 0
  nonlinear_remainder : ∀ parameter time,
    force (responseProfile parameter time) (parameter*impulseAcceleration time) =
      (6*gaugeScale*parameter^2*(impulse time)^2 + 2*parameter^3*(impulse time)^3)/(sourceCoupling*lapse)
  same_quantity : ∀ parameter point, fieldValue parameter point = physicalValue parameter (point 0)
  physical_response : ∀ point,
    HasDerivAt (fun parameter => fieldValue parameter point) (helicityResponse (point 0)) 0
  radial_response : ∀ time, helicityResponse time = 15*gaugeScale^4*impulse time
  nonzero_velocity : 0 < deriv helicityResponse 0
  physical_nonconstant : ¬ ∃ value : ℝ, helicityResponse = fun _ => value
  physical_frequency : ∀ time,
    deriv (deriv helicityResponse) time + responseFrequency^2*helicityResponse time = 0
  positive_quarter : 0 < helicityResponse (Real.pi/(2*responseFrequency))

theorem sourceRadialDynamicsClosure : SourceRadialDynamicsClosure where
  toSourceMatrixHelicityClosure := MatrixResponse.sourceMatrixHelicityClosure
  original_primitive := radialWrite_source
  original_constitutive := radialReadout_source
  profile_curvature := fun parameter point => radialWrite_curvature _ _ _ (responseProfile_hasDerivAt parameter (point 0))
  actual_auxiliary := fun parameter point => radialReadout_auxiliary _ _ _ (responseProfile_hasDerivAt parameter (point 0))
  native_density := gaugeLagrangian_eq
  actual_load := sourceLoad_eq
  joint_action := jointDensity_eq
  phase_derivative := responseAngle_hasDerivAt
  matter_derivative := fun parameter time => movingMatterCoordinates_hasDerivAt _ _ _
    (responseAngle_hasDerivAt parameter time).differentiableAt.hasDerivAt
  dual_derivative := fun parameter time variation => movingDual_hasDerivAt _ _ _
    (responseAngle_hasDerivAt parameter time).differentiableAt.hasDerivAt variation
  primal_kinetic := responseMatter_kinetic_zero
  adjoint_kinetic := responseAdjoint_zero
  current_preserved := movingCurrent
  original_equilibrium := equilibrium
  action_euler := euler_action
  positive_hessian := ⟨inertia_pos, stiffness_pos⟩
  source_frequency := ⟨responseFrequency_pos, responseFrequency_source_value⟩
  legendre := energy_eq
  exact_hessian := energy_expansion
  canonical_flow := canonical_response
  native_euler_response := nativeGaugeJet_linearized_zero
  nonlinear_remainder := nonlinear_residual
  same_quantity := fieldValue_eq
  physical_response := fieldValue_response
  radial_response := helicityResponse_eq
  nonzero_velocity := helicityResponse_initial_velocity
  physical_nonconstant := helicityResponse_nonconstant
  physical_frequency := helicityResponse_oscillator
  positive_quarter := helicityResponse_quarter

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
