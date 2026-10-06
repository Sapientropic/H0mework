import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Plane.Phase

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility YangMills.FullPairing
open LowEnergy.FiniteKernel Stage10.CanonicalMatter
noncomputable section

def seed (momentum : Fin 3 → ℝ) : DiracExteriorMatterCarrier :=
  normalizedPreparation momentum (actual.matter 0)

def seedDual (momentum : Fin 3 → ℝ) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (actual.conjugateMatter 0).comp (canonicalDual (normalizedPreparation momentum))

def fields (momentum : Fin 3 → ℝ) : StageNineHolonomicConfiguration :=
  configuration Stage10.Runtime.configuration (modes momentum) (fun _ : Unit => seed momentum)
    (fun _ : Unit => seedDual momentum)

theorem matter_value (momentum : Fin 3 → ℝ) (point : BasePoint) :
    (fields momentum).matter point = phase momentum point • seed momentum := by
  simp [fields, configuration, profile, modes]

theorem dual_value (momentum : Fin 3 → ℝ) (point : BasePoint) :
    (fields momentum).conjugateMatter point = star (phase momentum point) • seedDual momentum := by
  simp [fields, configuration, dualProfile, modes]

theorem fields_smooth (momentum : Fin 3 → ℝ) : (fields momentum).Smooth := by
  rcases actual_smooth with ⟨coframe,gravity,gravityAux,multiplier,gauge,gaugeAux,scalar,_,_⟩
  rw [fields, Stage10.Runtime.configuration_eq]
  refine ⟨coframe,gravity,gravityAux,multiplier,gauge,gaugeAux,scalar,?_,?_⟩
  · exact profile_smooth (modes momentum) _
  · intro index
    exact dualProfile_smooth (modes momentum) _ _

theorem matter_time (momentum : Fin 3 → ℝ) (point : BasePoint) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun candidate => matterCoordinateEquiv ((fields momentum).matter candidate)) point 0) =
        (-Complex.I*(energy momentum : ℂ)) • (fields momentum).matter point := by
  change matterCoordinateEquiv.symm (fieldDirectionalDerivative
    (fun candidate => matterCoordinateEquiv (profile (modes momentum) (fun _ : Unit => seed momentum) candidate)) point 0) = _
  rw [profile_directional, matter_value]
  simp [modes, phase_time, smul_smul]

theorem matter_space (momentum : Fin 3 → ℝ) (point : BasePoint) (axis : Fin 3) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun candidate => matterCoordinateEquiv ((fields momentum).matter candidate)) point axis.succ) =
        (Complex.I*(momentum axis : ℂ)) • (fields momentum).matter point := by
  change matterCoordinateEquiv.symm (fieldDirectionalDerivative
    (fun candidate => matterCoordinateEquiv (profile (modes momentum) (fun _ : Unit => seed momentum) candidate)) point axis.succ) = _
  rw [profile_directional, matter_value]
  simp [modes, phase_space, smul_smul]

theorem spatial_jet (momentum : Fin 3 → ℝ) (point : BasePoint) (axis : Fin 3) :
    holonomicMatterCovariantDerivative (fields momentum) point axis.succ =
      (Complex.I*(momentum axis : ℂ)) • (fields momentum).matter point +
        LowEnergy.FullQuantum.connection (fields momentum) point axis.succ ((fields momentum).matter point) := by
  change holonomicMatterCovariantDerivative (configuration Stage10.Runtime.configuration
    (modes momentum) (fun _ : Unit => seed momentum) (fun _ : Unit => seedDual momentum)) point axis.succ = _
  rw [profile_covariant, matter_value]
  simp only [modes, phase_space, fields, configuration, LowEnergy.FullQuantum.connection,
    map_smul, smul_smul]
  simp

theorem current_source (momentum : Fin 3 → ℝ) (point : BasePoint) :
    (fields momentum).conjugateMatter point
      (currentAction 0 HyperchargeResponse.chargeDirection ((fields momentum).matter point)) = -4*(spinScale : ℂ) := by
  rw [dual_value, matter_value]
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
  have source := original_current 0 momentum
  change seedDual momentum (currentAction 0 HyperchargeResponse.chargeDirection (seed momentum)) = _ at source
  rw [source, ← mul_assoc, mul_comm (phase momentum point) (star (phase momentum point)), phase_unit, one_mul]

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
