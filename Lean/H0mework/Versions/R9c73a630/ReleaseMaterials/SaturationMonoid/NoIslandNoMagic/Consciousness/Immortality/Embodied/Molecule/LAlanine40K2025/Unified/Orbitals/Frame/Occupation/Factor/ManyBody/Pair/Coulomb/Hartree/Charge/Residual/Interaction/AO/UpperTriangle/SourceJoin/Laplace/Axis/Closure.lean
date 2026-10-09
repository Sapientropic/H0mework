import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Target

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals
open MeasureTheory Set
noncomputable section

def originalSOuter : ℝ :=
  ∫ t in Ioi (0 : ℝ),
    originalWeight^4 * (2 / Real.sqrt Real.pi) *
      (Real.pi / Real.sqrt
        ((2*originalAlpha)*(2*originalAlpha) +
          ((2*originalAlpha)+(2*originalAlpha))*t^2))^3

structure Material where
  parent : Laplace.Material
  originalS : BasinRefinement.SourceGaussianModel.Term
  analyticQuartet : ℝ
  targetJ22Rest : ℝ

def material : Material where
  parent := Laplace.material
  originalS := originalS
  analyticQuartet := originalSOuter
  targetJ22Rest := targetHeatJ22Rest

theorem parent_identity : material.parent = Laplace.material := rfl
theorem original_s_identity : material.originalS = originalS := rfl

theorem analytic_quartet_exact :
    material.analyticQuartet = material.parent.heatQuartet 2 2 2 2 :=
  heat_quartet_2222_outer.symm

theorem target_J22_analytic_component :
    material.parent.heatTargetJ 2 2 =
      (SourceJoin.sourceCoefficientAt 195 : ℝ) * material.analyticQuartet +
        material.targetJ22Rest :=
  target_heat_J22_decomposition

structure Closure : Prop where
  parent : Laplace.Closure
  sourceSingleton : type_of% original_s_singleton
  sourcePowers : type_of% original_s_powers
  sourceExponent : type_of% original_s_exponent
  axisGaussian : type_of% coupled_axis_pair_closed
  spatialGaussian : type_of% spatial_s_factor
  sourceInner : type_of% original_s_heat_inner_simple
  sourceQuartet : type_of% original_s_ERI_outer_closed
  targetAddress : type_of% target_s_address
  targetDecomposition : type_of% target_heat_J22_decomposition
  parentIdentity : type_of% parent_identity
  sourceIdentity : type_of% original_s_identity
  quartet : type_of% analytic_quartet_exact
  targetJ : type_of% target_J22_analytic_component

theorem sourceGeneratedClosure : Closure :=
  ⟨Laplace.sourceGeneratedClosure,original_s_singleton,original_s_powers,
    original_s_exponent,coupled_axis_pair_closed,spatial_s_factor,
    original_s_heat_inner_simple,original_s_ERI_outer_closed,
    target_s_address,target_heat_J22_decomposition,
    parent_identity,original_s_identity,analytic_quartet_exact,
    target_J22_analytic_component⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
