import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Plane.Action
import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Plane.Momentum

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility YangMills.FullPairing
open StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource
open StageNineMatterPointwiseEquation StageNineDiracDualFormNativeMotherAction
open Stage10.StaticHamiltonian LowEnergy.FiniteKernel
noncomputable section
attribute [local irreducible] Stage10.Runtime.source Stage10.Runtime.configuration

theorem reference_momentum_zero (point : BasePoint) (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentum Stage10.Runtime.source reference direction 0 point = 0 := by
  simp [matterDifferentialMomentum, reference, configuration, dualProfile]

theorem ordinary_time_difference (momentum : Fin 3 → ℝ) (point : BasePoint) :
    ordinaryTimePairing Stage10.Runtime.source (fields momentum) point -
      ordinaryTimePairing Stage10.Runtime.source reference point = 4*spinScale*energy momentum := by
  unfold ordinaryTimePairing
  rw [actual_time_momentum, reference_momentum_zero]
  have gravity : gravityVelocityCurvature (fields momentum) point = gravityVelocityCurvature reference point := rfl
  have gauge : gaugeVelocityCurvature (fields momentum) point = gaugeVelocityCurvature reference point := rfl
  have scalar : StageNineScalarPointwiseEquation.scalarDifferentialMomentum Stage10.Runtime.source (fields momentum)
      (fieldDirectionalDerivative (fields momentum).scalar point 0) 0 point =
    StageNineScalarPointwiseEquation.scalarDifferentialMomentum Stage10.Runtime.source reference
      (fieldDirectionalDerivative reference.scalar point 0) 0 point := rfl
  rw [gravity, gauge, scalar]
  have gravityAux : (fields momentum).gravityAuxiliary point = reference.gravityAuxiliary point := rfl
  have gaugeAux : (fields momentum).gaugeAuxiliary point = reference.gaugeAuxiliary point := rfl
  rw [gravityAux, gaugeAux]
  ring

theorem complete_hamiltonian_difference (momentum : Fin 3 → ℝ) (point : BasePoint) :
    hamiltonianDensity Stage10.Runtime.source (fields momentum) point -
      hamiltonianDensity Stage10.Runtime.source reference point =
        Stage10.ActionNormalization.phaseMomentum*energy momentum := by
  unfold hamiltonianDensity
  rw [complete_density_equal, Stage10.ActionNormalization.phaseMomentum_source]
  have native := ordinary_time_difference momentum point
  linarith

theorem normalized_hamiltonian_difference (momentum : Fin 3 → ℝ) (point : BasePoint) :
    Stage10.ActionNormalization.hamiltonian (fields momentum) point -
      Stage10.ActionNormalization.hamiltonian reference point = energy momentum := by
  rw [Stage10.ActionNormalization.source_hamiltonian _ (fields_smooth momentum),
    Stage10.ActionNormalization.source_hamiltonian _ reference_smooth,
    ← mul_sub, complete_hamiltonian_difference, Stage10.ActionNormalization.actionScale,
    ← mul_assoc, inv_mul_cancel₀ Stage10.ActionNormalization.phaseMomentum_positive.ne', one_mul]

theorem original_action_rate_difference (momentum : Fin 3 → ℝ) (point : BasePoint) :
    HasDerivAt (fun rate : ℝ =>
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
        (toContinuumPointField (timeStretch (fields momentum) point rate) point) -
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
        (toContinuumPointField (timeStretch reference point rate) point))
      (Stage10.ActionNormalization.phaseMomentum*energy momentum) 0 := by
  have result := (source_time_legendre Stage10.Runtime.source (fields momentum) (fields_smooth momentum) point).sub
    (source_time_legendre Stage10.Runtime.source reference reference_smooth point)
  rw [ordinary_time_difference] at result
  convert result using 1 <;> first | rfl | simp only [Stage10.ActionNormalization.phaseMomentum_source]

theorem rejects_discarding_rest_energy (point : BasePoint) :
    hamiltonianDensity Stage10.Runtime.source (fields 0) point -
      hamiltonianDensity Stage10.Runtime.source reference point ≠ 0 := by
  rw [complete_hamiltonian_difference, energy_zero]
  exact mul_ne_zero Stage10.ActionNormalization.phaseMomentum_positive.ne'
    (neg_ne_zero.mpr Dispersion.frequency_pos.ne')

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
