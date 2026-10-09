import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Weak.ZeroFlux
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Normal

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Flux
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource GlobalSource.Differential MeasureTheory
open _root_.LAlanineTrueFlowDifferential
noncomputable section

structure FluxMaterial where
  transport : ℝ → Point ≃ₜ Point
  spatialStep : ℝ
  paths : Point → Path
  response : Point → Space →L[ℝ] Path
  jacobian : Point → Time → Space →L[ℝ] Space
  matrices : Point → ℝ → Matrix (Fin 3) (Fin 3) ℝ
  cutoffs : ℕ → Weak.Test
  laplacianIntegral : ℝ

def material : FluxMaterial where
  transport := flowHomeomorph
  spatialStep := Differential.spatialStep
  paths := actualPath
  response := Differential.response
  jacobian := flowDerivative
  matrices := responseMatrix
  cutoffs := Weak.cutoff
  laplacianIntegral := ∫ x in basin, laplacian sourceTerms densityMatrix x

structure FluxClosure : Prop where
  original_transport : ∀ t x, material.transport t x = flow x t
  original_step : 0 < material.spatialStep
  initial_derivative : type_of% original_flow_strictDerivative
  original_variation : type_of% original_variational
  original_jacobian : type_of% responseMatrix_actual
  inverse_derivative : type_of% flowDerivative_left_inverse
  positive_jacobian : type_of% actual_determinant_positive
  determinant_evolution : type_of% response_determinant_evolution
  derivative_bound : type_of% flowDerivative_bound
  original_frontier : type_of% flow_image_frontier
  original_tangent : type_of% original_gradient_tangent
  reverse_tangent : type_of% original_negative_gradient_tangent
  normal_readout : type_of% source_normal_derivative_zero
  actual_change_variables : type_of% basin_original_change_variables
  actual_weak_divergence : type_of% Weak.original_weak_divergence
  actual_cutoff_limit : type_of% Weak.cutoff_tends_one
  actual_zero_flux : material.laplacianIntegral = 0

theorem sourceGeneratedZeroFlux : FluxClosure :=
  ⟨fun _ _ => rfl,spatialStep_positive,original_flow_strictDerivative,original_variational,responseMatrix_actual,
    flowDerivative_left_inverse,actual_determinant_positive,response_determinant_evolution,flowDerivative_bound,
    flow_image_frontier,original_gradient_tangent,original_negative_gradient_tangent,source_normal_derivative_zero,
    basin_original_change_variables,Weak.original_weak_divergence,Weak.cutoff_tends_one,Weak.actual_basin_zero_flux⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Flux
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
