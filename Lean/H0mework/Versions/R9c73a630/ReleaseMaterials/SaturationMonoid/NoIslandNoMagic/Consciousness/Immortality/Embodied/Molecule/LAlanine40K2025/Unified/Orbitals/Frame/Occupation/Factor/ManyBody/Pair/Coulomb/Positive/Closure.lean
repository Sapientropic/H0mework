import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Positive
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Positive
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb MeasureTheory
noncomputable section

structure Material where
  parent : Coulomb.Material
  density : Point × Point → ℝ
  integrand : Point × Point → ℝ
  energy : ℝ

def material : Material where
  parent := Coulomb.material
  density := realPairDensity
  integrand := realPairIntegrand
  energy := pairCoulombEnergy.re

theorem parent_identity : material.parent = Coulomb.material := rfl
theorem density_cast (z : Point × Point) :
    material.parent.pairDensity z = (material.density z : ℂ) := pair_density_real z
theorem integrand_cast (z : Point × Point) :
    material.parent.pairIntegrand z = (material.integrand z : ℂ) := pair_integrand_real z
theorem density_nonnegative (z : Point × Point) :
    0 ≤ material.density z := real_pair_density_nonnegative z
theorem integrand_nonnegative (z : Point × Point) :
    0 ≤ material.integrand z := real_pair_integrand_nonnegative z
theorem integrand_integrable : Integrable material.integrand := real_pair_integrable
theorem energy_real_nonnegative :
    material.parent.energy.im = 0 ∧ 0 ≤ material.energy := pair_energy_real_nonnegative
theorem energy_identity : material.energy = material.parent.energy.re := rfl

structure Closure : Prop where
  parent : Coulomb.Closure
  parentIdentity : type_of% parent_identity
  densityCast : type_of% density_cast
  integrandCast : type_of% integrand_cast
  densityPositive : type_of% density_nonnegative
  integrandPositive : type_of% integrand_nonnegative
  integrable : Integrable material.integrand
  energyPositive : type_of% energy_real_nonnegative
  energyIdentity : type_of% energy_identity

theorem sourceGeneratedClosure : Closure :=
  ⟨Coulomb.sourceGeneratedClosure,parent_identity,density_cast,integrand_cast,
    density_nonnegative,integrand_nonnegative,integrand_integrable,
    energy_real_nonnegative,energy_identity⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Positive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
