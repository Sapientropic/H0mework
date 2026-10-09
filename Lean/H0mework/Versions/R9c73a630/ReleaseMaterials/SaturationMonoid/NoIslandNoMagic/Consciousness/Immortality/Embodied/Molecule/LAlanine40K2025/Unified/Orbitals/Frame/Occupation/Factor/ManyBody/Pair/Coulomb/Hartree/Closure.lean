import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Integral
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Positive.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb MeasureTheory
noncomputable section

structure Material where
  parent : Positive.Material
  directIntegrand : Point × Point → ℂ
  exchangeIntegrand : Point × Point → ℂ
  realDirectIntegrand : Point × Point → ℝ
  realExchangeIntegrand : Point × Point → ℝ
  direct : ℂ
  exchange : ℂ

def material : Material where
  parent := Positive.material
  directIntegrand := hartreeIntegrand
  exchangeIntegrand := exchangeIntegrand
  realDirectIntegrand := realHartreeIntegrand
  realExchangeIntegrand := realExchangeIntegrand
  direct := directEnergy
  exchange := exchangeEnergy

theorem parent_identity : material.parent = Positive.material := rfl
theorem direct_source_integral :
    material.direct = ∫ z : Point × Point, material.directIntegrand z :=
  hartree_integral_source.symm
theorem exchange_source_integral :
    material.exchange = ∫ z : Point × Point, material.exchangeIntegrand z :=
  exchange_integral_source.symm
theorem direct_cast (z : Point × Point) :
    material.directIntegrand z = (material.realDirectIntegrand z : ℂ) :=
  hartree_integrand_real z
theorem exchange_cast (z : Point × Point) :
    material.exchangeIntegrand z = (material.realExchangeIntegrand z : ℂ) :=
  exchange_integrand_real z
theorem direct_integrable : Integrable material.directIntegrand := hartree_integrable
theorem exchange_integrable' : Integrable material.exchangeIntegrand := exchange_integrable
theorem direct_positive : material.direct.im = 0 ∧ 0 ≤ material.direct.re :=
  direct_energy_real_nonnegative
theorem exchange_positive : material.exchange.im = 0 ∧ 0 ≤ material.exchange.re :=
  exchange_energy_real_nonnegative
theorem exchange_bounded : 2 * material.exchange.re ≤ material.direct.re :=
  exchange_energy_bounded
theorem parent_energy : material.parent.parent.energy = material.direct - material.exchange :=
  pair_coulomb_direct_exchange

structure Closure : Prop where
  parent : Positive.Closure
  parentIdentity : type_of% parent_identity
  directIntegral : type_of% direct_source_integral
  exchangeIntegral : type_of% exchange_source_integral
  directCast : type_of% direct_cast
  exchangeCast : type_of% exchange_cast
  directIntegrable : Integrable material.directIntegrand
  exchangeIntegrable : Integrable material.exchangeIntegrand
  directPositive : type_of% direct_positive
  exchangePositive : type_of% exchange_positive
  exchangeBound : type_of% exchange_bounded
  energy : type_of% parent_energy

theorem sourceGeneratedClosure : Closure :=
  ⟨Positive.sourceGeneratedClosure,parent_identity,direct_source_integral,
    exchange_source_integral,direct_cast,exchange_cast,direct_integrable,
    exchange_integrable',direct_positive,exchange_positive,exchange_bounded,
    parent_energy⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
