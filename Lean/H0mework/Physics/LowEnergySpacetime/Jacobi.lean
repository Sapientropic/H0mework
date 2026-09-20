import H0mework.Physics.LowEnergySpacetime.Dispersion
import H0mework.Physics.LowEnergySpacetime.Channels
import H0mework.Physics.LowEnergySpacetime.Stress

/-! Complete nine-channel radial first variation on the original spacetime background. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeCoframeLocalVariation Stage9C.Dynamics.Homogeneous Response.Radial
open scoped Matrix.Norms.Elementwise
noncomputable section

theorem radial_residual (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : Differentiable ℝ profile)
    (twice : ∀ mu, DifferentiableAt ℝ (coordinateDerivative profile mu) point)
    (equation : radialOperator profile point = 0) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      (configuration profile parameter) point =
      { (0 : DiracDualFormNativePointwiseJointResidualCarrier) with
        coframe := parameter^2 • diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
          (toContinuumPointField (configuration profile 1) point) } := by
  obtain ⟨multiplier,gravityAuxiliary,gaugeAuxiliary,lorentz,gauge,matter,dual⟩ :=
    seven_channels_zero profile parameter point (differentiable point)
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact multiplier
  · exact gravityAuxiliary
  · exact gaugeAuxiliary
  · exact lorentz
  · exact gauge
  · funext test
    change diracDualScalarEulerLagrangeDirectionalCoefficient _ _ _ _ = 0
    rw [scalar_euler profile parameter point differentiable twice, equation]
    ring
  · exact matter
  · exact dual
  · ext variation
    exact coframe_euler_quadratic profile parameter point (differentiable point) variation

theorem growingWave_residual (momentum : Fin 3 → ℝ) (inside : momentumSquared momentum ≤ 2)
    (parameter : ℝ) (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      (configuration (growingWave momentum) parameter) point =
      { (0 : DiracDualFormNativePointwiseJointResidualCarrier) with
        coframe := parameter^2 • diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
          (toContinuumPointField (configuration (growingWave momentum) 1) point) } :=
  radial_residual _ parameter point ((radialWave_smooth _ _).differentiable (by norm_num))
    (fun mu => radialWave_twice _ _ mu point) (growingWave_operator momentum inside point)

theorem growingWave_nine_channels (momentum : Fin 3 → ℝ) (inside : momentumSquared momentum ≤ 2)
    (point : BasePoint) :
    (∀ parameter,
      let residual := diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        (configuration (growingWave momentum) parameter) point
      residual.gravityMultiplier = 0 ∧ residual.gravityAuxiliary = 0 ∧
        residual.p286GaugeAuxiliary = 0 ∧ residual.lorentzConnection = 0 ∧
        residual.p286GaugeConnection = 0 ∧ residual.scalar = 0 ∧
        residual.matter = 0 ∧ residual.conjugateMatter = 0) ∧
    (∀ variation : LorentzianCoframe,
      HasDerivAt (fun parameter => (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        (configuration (growingWave momentum) parameter) point).coframe variation) 0 0) := by
  constructor
  · intro parameter
    rw [growingWave_residual momentum inside parameter point]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · intro variation
    exact coframe_first_zero _ point ((radialWave_smooth _ _).differentiable (by norm_num) point) variation

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
