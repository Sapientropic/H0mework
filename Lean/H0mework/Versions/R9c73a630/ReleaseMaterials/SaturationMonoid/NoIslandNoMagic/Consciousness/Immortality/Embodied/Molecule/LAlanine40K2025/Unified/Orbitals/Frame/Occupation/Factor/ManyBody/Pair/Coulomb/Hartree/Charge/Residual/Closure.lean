import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient MeasureTheory
noncomputable section

structure Material where
  parent : Charge.Material
  coefficient : Basis → Basis → ℝ

def material : Material where
  parent := Charge.material
  coefficient := residualMatrix

theorem parent_identity : material.parent = Charge.material := rfl
theorem actual_coefficient (i k : Basis) :
    material.coefficient i k =
      normalizedDensityMatrix i k - 2 * (projector24 i k).re := rfl
theorem actual_spatial_source (x : Point) :
    material.parent.residual x = ∑ i : Basis, ∑ k : Basis,
      material.coefficient i k * normalizedOrbital i x * normalizedOrbital k x :=
  original_D3_spatial_residual x
theorem original_D3_from_matrix (x : Point) :
    sourceDensity x = material.parent.projected x +
      ∑ i : Basis, ∑ k : Basis,
        material.coefficient i k * normalizedOrbital i x * normalizedOrbital k x := by
  rw [← actual_spatial_source]
  exact Charge.original_D3_decomposition x

structure Closure : Prop where
  parent : Charge.Closure
  parentIdentity : type_of% parent_identity
  coefficient : type_of% actual_coefficient
  spatialResidual : type_of% actual_spatial_source
  originalD3 : type_of% original_D3_from_matrix

theorem sourceGeneratedClosure : Closure :=
  ⟨Charge.sourceGeneratedClosure,parent_identity,actual_coefficient,
    actual_spatial_source,original_D3_from_matrix⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
