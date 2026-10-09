import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Integral
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Closure

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb MeasureTheory
open scoped Matrix BigOperators
noncomputable section

structure Material where
  parent : Pair.Material
  pairDensity : Point × Point → ℂ
  pairIntegrand : Point × Point → ℂ
  energy : ℂ
  direct : ℂ
  exchange : ℂ

def material : Material where
  parent := Pair.material
  pairDensity := pairDensity
  pairIntegrand := pairCoulombIntegrand
  energy := pairCoulombEnergy
  direct := directEnergy
  exchange := exchangeEnergy

theorem parent_identity : material.parent = Pair.material := rfl
theorem density_from_parent (z : Point × Point) : material.pairDensity z =
    ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
      material.parent.spinSummed i j k l *
        (normalizedOrbital i z.1 * normalizedOrbital k z.1 *
          (normalizedOrbital j z.2 * normalizedOrbital l z.2) : ℝ) := rfl
theorem density_from_full_U (time : ℝ) (z : Point × Point) :
    material.pairDensity z =
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        material.parent.spinSummed i j k l *
          inner ℂ (normalizedSection i time z.1) (normalizedSection k time z.1) *
          inner ℂ (normalizedSection j time z.2) (normalizedSection l time z.2) :=
  pair_density_full_U time z
theorem material_integrable : Integrable material.pairIntegrand := pair_integrable
theorem material_energy_source : material.energy = sourceRepulsionSum :=
  pair_coulomb_energy_source
theorem material_energy_ao : type_of% pair_coulomb_energy_original_ao :=
  pair_coulomb_energy_original_ao
theorem material_direct_exchange : material.energy = material.direct - material.exchange :=
  pair_coulomb_direct_exchange

structure Closure : Prop where
  parent : Pair.Closure
  parentIdentity : type_of% parent_identity
  densitySource : type_of% density_from_parent
  densityU : type_of% density_from_full_U
  integrable : Integrable material.pairIntegrand
  sourceSum : material.energy = sourceRepulsionSum
  originalAO : type_of% material_energy_ao
  directExchange : material.energy = material.direct - material.exchange

theorem sourceGeneratedClosure : Closure :=
  ⟨Pair.sourceGeneratedClosure,parent_identity,density_from_parent,
    density_from_full_U,material_integrable,material_energy_source,
    material_energy_ao,material_direct_exchange⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
