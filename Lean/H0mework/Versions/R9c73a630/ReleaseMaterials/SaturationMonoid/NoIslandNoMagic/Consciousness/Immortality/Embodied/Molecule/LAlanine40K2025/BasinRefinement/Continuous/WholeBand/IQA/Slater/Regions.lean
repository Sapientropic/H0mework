import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Integrals
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Positive

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater
open SourceGaussianModel GlobalSource WholeBandBasin Set MeasureTheory
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
noncomputable section

def insideFirst : Set (Point × Point) := Prod.fst ⁻¹' basin
def insideSecond : Set (Point × Point) := Prod.snd ⁻¹' basin
def intraRegion : Set (Point × Point) := basin ×ˢ basin
def firstCrossRegion : Set (Point × Point) := basin ×ˢ basinᶜ
def secondCrossRegion : Set (Point × Point) := basinᶜ ×ˢ basin
def exteriorRegion : Set (Point × Point) := basinᶜ ×ˢ basinᶜ

theorem inside_first_measurable : MeasurableSet insideFirst :=
  basin_measurable.preimage measurable_fst

theorem inside_second_measurable : MeasurableSet insideSecond :=
  basin_measurable.preimage measurable_snd

theorem regions_measurable :
    MeasurableSet intraRegion ∧ MeasurableSet firstCrossRegion ∧
      MeasurableSet secondCrossRegion ∧ MeasurableSet exteriorRegion := by
  exact ⟨basin_measurable.prod basin_measurable,
    basin_measurable.prod basin_measurable.compl,
    basin_measurable.compl.prod basin_measurable,
    basin_measurable.compl.prod basin_measurable.compl⟩

theorem intra_region_eq : intraRegion = insideFirst ∩ insideSecond :=
  Set.prod_eq basin basin
theorem first_cross_region_eq : firstCrossRegion = insideFirst ∩ insideSecondᶜ := by
  ext z
  simp [firstCrossRegion,insideFirst,insideSecond]
theorem second_cross_region_eq : secondCrossRegion = insideFirstᶜ ∩ insideSecond := by
  ext z
  simp [secondCrossRegion,insideFirst,insideSecond]
theorem exterior_region_eq : exteriorRegion = insideFirstᶜ ∩ insideSecondᶜ := by
  ext z
  simp [exteriorRegion,insideFirst,insideSecond]

def intraEnergy : ℝ := (1/2 : ℝ) * ∫ z in intraRegion, realPairIntegrand z
def firstCrossEnergy : ℝ := (1/2 : ℝ) * ∫ z in firstCrossRegion, realPairIntegrand z
def secondCrossEnergy : ℝ := (1/2 : ℝ) * ∫ z in secondCrossRegion, realPairIntegrand z
def exteriorEnergy : ℝ := (1/2 : ℝ) * ∫ z in exteriorRegion, realPairIntegrand z

theorem regional_integrable :
    IntegrableOn realPairIntegrand intraRegion ∧
      IntegrableOn realPairIntegrand firstCrossRegion ∧
      IntegrableOn realPairIntegrand secondCrossRegion ∧
      IntegrableOn realPairIntegrand exteriorRegion :=
  ⟨real_pair_integrable.integrableOn,real_pair_integrable.integrableOn,
    real_pair_integrable.integrableOn,real_pair_integrable.integrableOn⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandIQA.Slater
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
