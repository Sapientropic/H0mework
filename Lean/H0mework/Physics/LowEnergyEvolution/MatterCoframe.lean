import H0mework.Physics.LowEnergyEvolution.MatterStress
import H0mework.Physics.LowEnergyEvolution.ScalarStress

/-! The original coframe matter covector consumes both the scalar and
Dirac density derivatives on the same actual field. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineCoframeVariation StageNineScalarLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeCoframeLocalVariation
open Stage9C.Dynamics.Homogeneous Stage9C.Material.SpinPair
open scoped Matrix.Norms.Elementwise
noncomputable section

def diracCoframeForce (x : State) (variation : LorentzianCoframe) : ℝ :=
  -6*spinScale*(contorsion x-x 2)/x 0*variation 0 0 +
    2*clock x*spinScale*(contorsion x-x 2)/(x 0)^2*(variation 1 1+variation 2 2+variation 3 3)

theorem Solution.frozen_matter_density {initial : State} (flow : Solution initial)
    (point : BasePoint) (candidate : LorentzianCoframe) :
    diracDualFormNativeCoframeMatterDensity positiveSmoothUnifiedSource point
      (toContinuumPointField flow.configuration point) candidate =
      generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 point
        (withCoframe (toContinuumPointField flow.configuration point) candidate) +
      generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
        (withCoframe (toContinuumPointField flow.configuration point) candidate) := by
  unfold diracDualFormNativeCoframeMatterDensity generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  rw [flow.frozen_yukawa_zero, add_zero]

theorem Solution.matter_coframe {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (variation : LorentzianCoframe) :
    diracDualFormNativeCoframeMatterEulerCovector positiveSmoothUnifiedSource point
      (toContinuumPointField flow.configuration point) variation =
      scalarCoframeForce (flow.pointState point) variation + diracCoframeForce (flow.pointState point) variation := by
  have computed : HasDerivAt
      (fun t : ℝ => diracDualFormNativeCoframeMatterDensity positiveSmoothUnifiedSource point
        (toContinuumPointField flow.configuration point) (flow.configuration.coframe point+t • variation))
      (scalarCoframeForce (flow.pointState point) variation + diracCoframeForce (flow.pointState point) variation) 0 := by
    simp_rw [flow.frozen_matter_density]
    exact (flow.scalar_density_coframe_derivative point inside variation).add
      (flow.kinetic_coframe_derivative point inside variation)
  have evaluated := (diracDualFormNativeCoframeMatterDensity_hasFDerivAt positiveSmoothUnifiedSource point
    (toContinuumPointField flow.configuration point) (flow.nondegenerate_at point inside)).comp_hasDerivAt_of_eq
      0 (coframe_line_hasDerivAt (flow.configuration.coframe point) variation) (by simp [toContinuumPointField])
  exact evaluated.unique computed

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
