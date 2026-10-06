import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Plane.Fields

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility YangMills.FullPairing
open LowEnergy.FullQuantum ChargedPreparation.Dynamics
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
noncomputable section

theorem full_hamiltonian_point (point first : BasePoint) (momentum : Fin 3 → ℝ) (values : Source.Index → ℂ) :
    hamiltonian Stage10.Runtime.configuration point momentum (embed values) =
      hamiltonian Stage10.Runtime.configuration first momentum (embed values) := by
  simp only [Stage10.Runtime.configuration_eq, physical_hamiltonian_embed, physical_free_embed]

theorem source_matter_twice (point : BasePoint) : actual.matter point = (2 : ℂ) • embed (Source.vector point) := by
  apply naturalCoordinates.injective
  rw [actual_eq_twice_prepared]
  simp only [YangMills.FullPairing.prepared, map_smul]

theorem seed_hamiltonian (point : BasePoint) (momentum : Fin 3 → ℝ) :
    hamiltonian Stage10.Runtime.configuration point momentum (seed momentum) =
      (energy momentum : ℂ) • seed momentum := by
  have original := normalized_full_hamiltonian 0 momentum
  rw [normalized_source] at original
  rw [seed, source_matter_twice, map_smul, map_smul, normalized_source,
    full_hamiltonian_point point 0 momentum, original]
  exact smul_comm _ _ _

theorem fields_hamiltonian (point : BasePoint) (momentum : Fin 3 → ℝ) :
    hamiltonian (fields momentum) point momentum ((fields momentum).matter point) =
      (energy momentum : ℂ) • (fields momentum).matter point := by
  have background : hamiltonian (fields momentum) point momentum =
      hamiltonian Stage10.Runtime.configuration point momentum := rfl
  rw [background, matter_value, map_smul, seed_hamiltonian]
  exact smul_comm _ _ _

theorem actual_time_drift (point : BasePoint) (momentum : Fin 3 → ℝ) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun candidate => matterCoordinateEquiv ((fields momentum).matter candidate)) point 0) =
        drift (fields momentum) point momentum ((fields momentum).matter point) := by
  rw [← hamiltonian_drift]
  simp only [LinearMap.smul_apply, fields_hamiltonian, smul_smul, matter_time]

theorem original_action_time_velocity (point : BasePoint) (momentum : Fin 3 → ℝ) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun candidate => matterCoordinateEquiv ((fields momentum).matter candidate)) point 0) =
        actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity (fields momentum) point := by
  rw [actual_time_drift]
  exact drift_original (fields momentum) point momentum (spatial_jet momentum point)

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
