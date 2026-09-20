import H0mework.Physics.LowEnergySpacetime.Jacobi
import H0mework.Physics.LowEnergySpacetime.Propagation

/-! Every source spatial momentum has a nonzero unit-velocity nine-channel Jacobi mode. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativeCoframeLocalVariation
open Response.Radial
noncomputable section

theorem fundamentalWave_residual (momentum : Fin 3 → ℝ) (parameter : ℝ) (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      (configuration (fundamentalWave momentum) parameter) point =
      { (0 : DiracDualFormNativePointwiseJointResidualCarrier) with
        coframe := parameter^2 • diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
          (toContinuumPointField (configuration (fundamentalWave momentum) 1) point) } :=
  radial_residual _ parameter point ((fundamentalWave_smooth momentum).differentiable (by norm_num))
    (fun mu => fundamentalWave_twice momentum mu point) (fundamentalWave_operator momentum point)

theorem fundamentalWave_nine_channels (momentum : Fin 3 → ℝ) (point : BasePoint) :
    (∀ parameter,
      let residual := diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        (configuration (fundamentalWave momentum) parameter) point
      residual.gravityMultiplier = 0 ∧ residual.gravityAuxiliary = 0 ∧
        residual.p286GaugeAuxiliary = 0 ∧ residual.lorentzConnection = 0 ∧
        residual.p286GaugeConnection = 0 ∧ residual.scalar = 0 ∧
        residual.matter = 0 ∧ residual.conjugateMatter = 0) ∧
    (∀ variation : LorentzianCoframe,
      HasDerivAt (fun parameter => (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        (configuration (fundamentalWave momentum) parameter) point).coframe variation) 0 0) := by
  constructor
  · intro parameter
    rw [fundamentalWave_residual]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · intro variation
    exact coframe_first_zero _ point ((fundamentalWave_smooth momentum).differentiable (by norm_num) point) variation

theorem fundamentalWave_scalar_initial (momentum : Fin 3 → ℝ) (parameter : ℝ)
    (point : BasePoint) (initial : point 0 = 0) :
    (configuration (fundamentalWave momentum) parameter).scalar point = actual.scalar point := by
  simp [configuration, fundamentalWave_initial momentum point initial, actual_scalar, direction]

theorem fundamentalWave_scalar_speed (momentum : Fin 3 → ℝ) (parameter : ℝ)
    (point : BasePoint) (initial : point 0 = 0) :
    fieldDirectionalDerivative (configuration (fundamentalWave momentum) parameter).scalar point 0 =
      (parameter*Real.cos (spatialPhase momentum point)) • direction := by
  rw [scalar_derivative _ parameter point
    ((fundamentalWave_smooth momentum).differentiable (by norm_num) point),
    fundamentalWave_initial_speed momentum point initial]

theorem fundamentalWave_actual_nonzero_speed (momentum : Fin 3 → ℝ) :
    fieldDirectionalDerivative (configuration (fundamentalWave momentum) 1).scalar 0 0 = direction ∧
      fieldDirectionalDerivative (configuration (fundamentalWave momentum) 1).scalar 0 0 ≠ 0 := by
  have speed := fundamentalWave_scalar_speed momentum 1 0 rfl
  simp only [map_zero, Real.cos_zero, mul_one, one_smul] at speed
  exact ⟨speed, speed ▸ direction_nonzero⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
