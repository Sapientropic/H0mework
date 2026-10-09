import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.D3Residual.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater.D3Residual
open SourceGaussianModel GlobalSource WholeBandBasin Set MeasureTheory
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
noncomputable section

structure Material where
  parent : Slater.Material
  d3Intra : ℝ
  leftDelta : ℝ
  rightDelta : ℝ
  exchangeIntra : ℝ

def material : Material where
  parent := Slater.material
  d3Intra := (1/2 : ℝ)*(∫ z in Slater.intraRegion,
    pairIntegrand d3Matrix d3Matrix z)
  leftDelta := (1/2 : ℝ)*(∫ z in Slater.intraRegion,
    pairIntegrand deltaMatrix d3Matrix z)
  rightDelta := (1/2 : ℝ)*(∫ z in Slater.intraRegion,
    pairIntegrand occupationMatrix deltaMatrix z)
  exchangeIntra := ∫ z in Slater.intraRegion, realExchangeIntegrand z

theorem parent_same_source : material.parent=Slater.material := rfl

theorem local_d3_slater_account :
    material.d3Intra-material.parent.intra =
      material.leftDelta+material.rightDelta+material.exchangeIntra := by
  have h := atom7_intra_d3_slater_residual
  change (1/2 : ℝ)*(∫ z in Slater.intraRegion,
      pairIntegrand d3Matrix d3Matrix z)-Slater.intraEnergy =
    (1/2 : ℝ)*(∫ z in Slater.intraRegion,
      pairIntegrand deltaMatrix d3Matrix z)+
    (1/2 : ℝ)*(∫ z in Slater.intraRegion,
      pairIntegrand occupationMatrix deltaMatrix z)+
    (∫ z in Slater.intraRegion, realExchangeIntegrand z)
  linarith only [h]

theorem local_exchange_nonnegative : 0 ≤ material.exchangeIntra :=
  setIntegral_nonneg Slater.regions_measurable.1
    (fun z _ => exchange_integrand_nonnegative z)

structure Closure : Prop where
  parent : Slater.Closure
  parentIdentity : type_of% parent_same_source
  sourceResidual : type_of% regional_d3_slater_residual
  actualResidual : type_of% local_d3_slater_account
  exchangePositive : type_of% local_exchange_nonnegative
  globalResidual : type_of% d3_occupation_hartree_residual

theorem sourceGeneratedClosure : Closure :=
  ⟨Slater.sourceGeneratedClosure,parent_same_source,
    regional_d3_slater_residual,local_d3_slater_account,
    local_exchange_nonnegative,d3_occupation_hartree_residual⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater.D3Residual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
