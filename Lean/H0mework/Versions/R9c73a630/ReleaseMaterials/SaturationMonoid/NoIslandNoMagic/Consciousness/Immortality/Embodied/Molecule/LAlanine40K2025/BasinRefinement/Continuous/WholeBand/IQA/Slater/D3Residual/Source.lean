import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.Additivity
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Bridge

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater.D3Residual
open SourceGaussianModel GlobalSource WholeBandBasin Set MeasureTheory
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree
open scoped Matrix BigOperators
noncomputable section

theorem density_from_add (A B : Matrix SourceFiniteData.Basis SourceFiniteData.Basis ℝ)
    (x : Point) : densityFrom (A+B) x = densityFrom A x+densityFrom B x := by
  simp only [densityFrom,Matrix.add_apply,add_mul,Finset.sum_add_distrib]

theorem regional_residual_pointwise (z : Point × Point) :
    pairIntegrand d3Matrix d3Matrix z-
      pairIntegrand occupationMatrix occupationMatrix z =
      pairIntegrand deltaMatrix d3Matrix z+
        pairIntegrand occupationMatrix deltaMatrix z := by
  have split (x : Point) :
      densityFrom d3Matrix x = densityFrom occupationMatrix x+
        densityFrom deltaMatrix x := by
    rw [matrix_split,density_from_add]
  simp only [pairIntegrand]
  rw [split z.1,split z.2]
  ring

theorem regional_d3_hartree_residual (region : Set (Point × Point)) :
    (1/2 : ℝ)*(∫ z in region, pairIntegrand d3Matrix d3Matrix z)-
      (1/2 : ℝ)*(∫ z in region, pairIntegrand occupationMatrix occupationMatrix z) =
    (1/2 : ℝ)*((∫ z in region, pairIntegrand deltaMatrix d3Matrix z)+
      (∫ z in region, pairIntegrand occupationMatrix deltaMatrix z)) := by
  have hDD := (pair_integrable d3Matrix d3Matrix).integrableOn (s := region)
  have hOO := (pair_integrable occupationMatrix occupationMatrix).integrableOn (s := region)
  have hδD := (pair_integrable deltaMatrix d3Matrix).integrableOn (s := region)
  have hOδ := (pair_integrable occupationMatrix deltaMatrix).integrableOn (s := region)
  calc
    _ = (1/2 : ℝ)*((∫ z in region, pairIntegrand d3Matrix d3Matrix z)-
        (∫ z in region, pairIntegrand occupationMatrix occupationMatrix z)) := by ring_nf
    _ = (1/2 : ℝ)*(∫ z in region,
        (pairIntegrand d3Matrix d3Matrix z-
          pairIntegrand occupationMatrix occupationMatrix z)) := by
      rw [integral_sub hDD hOO]
    _ = (1/2 : ℝ)*(∫ z in region,
        (pairIntegrand deltaMatrix d3Matrix z+
          pairIntegrand occupationMatrix deltaMatrix z)) := by
      simp_rw [regional_residual_pointwise]
    _ = _ := by rw [integral_add hδD hOδ]

theorem occupation_pair_half_eq_hartree (z : Point × Point) :
    (1/2 : ℝ)*pairIntegrand occupationMatrix occupationMatrix z =
      realHartreeIntegrand z := by
  simp only [pairIntegrand,density_from_occupation,realHartreeIntegrand,
    projected_density_norm]
  ring

theorem slater_pair_half_eq_direct_minus_exchange (z : Point × Point) :
    (1/2 : ℝ)*realPairIntegrand z =
      realHartreeIntegrand z-realExchangeIntegrand z := by
  simp only [realPairIntegrand,realPairDensity,realHartreeIntegrand,
    realExchangeIntegrand]
  ring

theorem regional_d3_slater_residual (region : Set (Point × Point)) :
    (1/2 : ℝ)*(∫ z in region, pairIntegrand d3Matrix d3Matrix z)-
      (1/2 : ℝ)*(∫ z in region, realPairIntegrand z) =
    (1/2 : ℝ)*((∫ z in region, pairIntegrand deltaMatrix d3Matrix z)+
      (∫ z in region, pairIntegrand occupationMatrix deltaMatrix z))+
      (∫ z in region, realExchangeIntegrand z) := by
  have hOcc : (1/2 : ℝ)*(∫ z in region,
      pairIntegrand occupationMatrix occupationMatrix z) =
      ∫ z in region, realHartreeIntegrand z := by
    rw [← integral_const_mul]
    simp_rw [occupation_pair_half_eq_hartree]
  have hSlater : (1/2 : ℝ)*(∫ z in region, realPairIntegrand z) =
      (∫ z in region, realHartreeIntegrand z)-
      (∫ z in region, realExchangeIntegrand z) := by
    rw [← integral_const_mul]
    simp_rw [slater_pair_half_eq_direct_minus_exchange]
    exact integral_sub real_hartree_integrable.integrableOn
      real_exchange_integrable.integrableOn
  have hResidual := regional_d3_hartree_residual region
  linarith only [hOcc,hSlater,hResidual]

theorem atom7_intra_d3_slater_residual :
    (1/2 : ℝ)*(∫ z in Slater.intraRegion,
      pairIntegrand d3Matrix d3Matrix z)-Slater.intraEnergy =
    (1/2 : ℝ)*((∫ z in Slater.intraRegion,
      pairIntegrand deltaMatrix d3Matrix z)+
      (∫ z in Slater.intraRegion,
        pairIntegrand occupationMatrix deltaMatrix z))+
      (∫ z in Slater.intraRegion, realExchangeIntegrand z) := by
  exact regional_d3_slater_residual Slater.intraRegion

end
end LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater.D3Residual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
