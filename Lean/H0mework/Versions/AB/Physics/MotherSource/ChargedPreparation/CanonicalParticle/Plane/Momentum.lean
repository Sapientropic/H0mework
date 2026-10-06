import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Plane.Dynamics

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility YangMills.FullPairing
open LowEnergy.FullQuantum Stage10.CanonicalMatter StageNineMatterPointwiseEquation
open StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource
noncomputable section

theorem time_pair (momentum : Fin 3 → ℝ) (point : BasePoint) :
    normalizedMomentum (fields momentum) point ((fields momentum).conjugateMatter point)
      ((fields momentum).matter point) = 4*(spinScale : ℂ) := by
  have background (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (matter : DiracExteriorMatterCarrier) :
      normalizedMomentum (fields momentum) point dual matter = normalizedMomentum actual point dual matter := by
    unfold normalizedMomentum
    rw [fields, LowEnergy.FiniteKernel.configuration, Stage10.Runtime.configuration_eq]
  rw [background, native_time_pair, dual_value, matter_value]
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
  have source := prepared_time_pair 0 momentum
  rw [native_time_pair] at source
  change seedDual momentum (diracMatrixMatterAction
    DiracCliffordRepresentation.diracGammaZero (seed momentum)) = _ at source
  rw [source, ← mul_assoc, mul_comm (phase momentum point) (star (phase momentum point)),
    phase_unit, one_mul]

theorem phase_momentum (momentum : Fin 3 → ℝ) (point : BasePoint) (coefficient : ℝ) :
    matterDifferentialMomentum Stage10.Runtime.source (fields momentum)
      (matterCoordinateEquiv ((-Complex.I*(coefficient : ℂ)) • (fields momentum).matter point)) 0 point =
        4*spinScale*coefficient := by
  rw [Stage10.Runtime.source_eq]
  rw [mul_smul, action_time_momentum]
  have scaling : normalizedMomentum (fields momentum) point ((fields momentum).conjugateMatter point)
      ((coefficient : ℂ) • (fields momentum).matter point) =
        (coefficient : ℂ)*normalizedMomentum (fields momentum) point
          ((fields momentum).conjugateMatter point) ((fields momentum).matter point) := by
    simp only [normalizedMomentum, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [scaling, time_pair]
  simp
  ring

theorem actual_time_momentum (momentum : Fin 3 → ℝ) (point : BasePoint) :
    matterDifferentialMomentum Stage10.Runtime.source (fields momentum)
      (fieldDirectionalDerivative (fun candidate => matterCoordinateEquiv ((fields momentum).matter candidate)) point 0)
      0 point = 4*spinScale*energy momentum := by
  have derivative := congrArg matterCoordinateEquiv (matter_time momentum point)
  rw [LinearEquiv.apply_symm_apply] at derivative
  rw [derivative, phase_momentum]

theorem actual_translation_momentum (momentum : Fin 3 → ℝ) (point : BasePoint) (axis : Fin 3) :
    matterDifferentialMomentum Stage10.Runtime.source (fields momentum)
      (-fieldDirectionalDerivative (fun candidate => matterCoordinateEquiv ((fields momentum).matter candidate)) point axis.succ)
      0 point = 4*spinScale*momentum axis := by
  have derivative := congrArg matterCoordinateEquiv (matter_space momentum point axis)
  rw [LinearEquiv.apply_symm_apply] at derivative
  have direction :
      -fieldDirectionalDerivative (fun candidate => matterCoordinateEquiv ((fields momentum).matter candidate)) point axis.succ =
      matterCoordinateEquiv ((-Complex.I*(momentum axis : ℂ)) • (fields momentum).matter point) := by
    rw [derivative, ← map_neg]
    congr 1
    module
  rw [direction, phase_momentum]

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
