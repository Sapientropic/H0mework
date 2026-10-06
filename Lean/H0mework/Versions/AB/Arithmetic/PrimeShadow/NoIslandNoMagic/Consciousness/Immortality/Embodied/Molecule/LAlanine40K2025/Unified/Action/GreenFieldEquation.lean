import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenPointwise

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineCoframeLocalDifferentiability
open StageNineCanonicalCauchyState Stage10.CanonicalGauss
open BasinRefinement SourceGaussianModel ContinuousGradient
open scoped ContDiff
noncomputable section

theorem spatial_pullback_derivative (f : Point → ℝ) (regular : Differentiable ℝ f)
    (point : BasePoint) (index : Fin 3) :
    fieldDirectionalDerivative (fun p => f (spatialPoint 1 p)) point index.succ =
      spatialFirst f index (spatialPoint 1 point) := by
  have generated := (regular (sourceSpatialMap 1 point)).hasFDerivAt.comp point (sourceSpatialMap 1).hasFDerivAt
  unfold fieldDirectionalDerivative
  change (fderiv ℝ (f ∘ sourceSpatialMap 1) point) _ = _
  rw [generated.fderiv]
  simp only [ContinuousLinearMap.comp_apply, sourceSpatialMap_direction, one_smul]
  rfl

theorem fieldPotential_laplacian (point : BasePoint) :
    spatialLaplacian fieldPotential point = spatialLap sourcePotential (spatialPoint 1 point) := by
  unfold spatialLaplacian fieldPotential
  simp only [spatial_pullback_derivative _ (sourcePotential_smooth.differentiable (by simp))]
  unfold spatialLap
  apply Finset.sum_congr rfl
  intro index _
  exact spatial_pullback_derivative _ ((spatialFirst_smooth sourcePotential_smooth index).differentiable (by simp)) point index

/-- The potential generated from the original D3 source annihilates its full original U Euler projection. -/
theorem original_D3_euler_zero (space : StageNineSpatialPoint) :
    CanonicalSource.D3Euler (abelianPotential fieldPotential) 1 space
      Stage10.HyperchargeResponse.chargeDirection = 0 := by
  rw [CanonicalSource.original_D3_poisson _ fieldPotential_regular, fieldPotential_laplacian]
  have gauss := original_D3_pointwise_gauss (spatialPoint 1 (canonicalCauchySlicePoint 0 space))
  rw [sourceCurrent_value] at gauss
  linarith

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
