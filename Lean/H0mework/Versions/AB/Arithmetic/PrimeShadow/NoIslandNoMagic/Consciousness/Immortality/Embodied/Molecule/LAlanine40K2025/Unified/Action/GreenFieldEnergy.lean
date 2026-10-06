import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.LinearCutoffEnergy

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory Filter BasinRefinement SourceGaussianModel
open scoped Topology
noncomputable section

theorem laplacian_boundary_tendsto_zero :
    Tendsto (fun radius : ℝ => ∫ point : Point, laplacianBoundary radius point) atTop (𝓝 0) := by
  have upper : Tendsto (fun radius : ℝ => laplacianBoundaryConstant/radius) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul laplacianBoundaryConstant
  have lower : Tendsto (fun radius : ℝ => -(laplacianBoundaryConstant/radius)) atTop (𝓝 0) := by
    simpa only [neg_zero] using upper.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower upper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with radius positive
    exact (abs_le.mp (laplacian_boundary_bound radius positive)).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with radius positive
    exact (abs_le.mp (laplacian_boundary_bound radius positive)).2

theorem original_D3_field_energy :
    lapse*(∫ point : Point, gradientSquare sourcePotential point) =
      -(1/2)*(∫ point : Point, sourceCurrent point*sourcePotential point) := by
  have left := (cutoff_mul_tendsto _ source_gradient_integrable).const_mul lapse
  have right : Tendsto (fun radius : ℝ => (lapse/2)*(∫ point : Point, laplacianBoundary radius point)-
      (1/2)*(∫ point : Point, cutoff radius point*(sourceCurrent point*sourcePotential point))) atTop
      (𝓝 (-(1/2)*(∫ point : Point, sourceCurrent point*sourcePotential point))) := by
    simpa only [mul_zero, zero_sub, neg_mul] using
      (laplacian_boundary_tendsto_zero.const_mul (lapse/2)).sub
        ((cutoff_mul_tendsto _ source_current_potential_integrable).const_mul (1/2))
  have same : (fun radius : ℝ => lapse*(∫ point : Point, cutoff radius point*gradientSquare sourcePotential point)) =ᶠ[atTop]
      (fun radius : ℝ => (lapse/2)*(∫ point : Point, laplacianBoundary radius point)-
        (1/2)*(∫ point : Point, cutoff radius point*(sourceCurrent point*sourcePotential point))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with radius positive
    exact original_D3_linear_cutoff_energy radius positive
  exact tendsto_nhds_unique left (right.congr' same.symm)

theorem original_D3_field_energy_hartree :
    lapse*(∫ point : Point, gradientSquare sourcePotential point) =
      (4*spinScale)^2/(8*Real.pi*lapse)*
        UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.d3HartreeEnergy := by
  rw [original_D3_field_energy, original_D3_potential_energy]

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
