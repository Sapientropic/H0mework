import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Fifth.Cells

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Fifth
open SourceGaussianModel GlobalSource Set MeasureTheory
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
noncomputable section

theorem cell_energy_nonnegative (i : Fin 5 × Fin 5) : 0 ≤ cellEnergy i :=
  Partition.Finite.cell_energy_nonnegative zoneIndex zone_measurable i

theorem cell_energy_symmetric (i j : Fin 5) : cellEnergy (i,j)=cellEnergy (j,i) :=
  Partition.Finite.cell_energy_symmetric zoneIndex i j

theorem full_energy_twenty_five_cells :
    (∑ i : Fin 5 × Fin 5, cellEnergy i)=pairCoulombEnergy.re :=
  Partition.Finite.full_energy zoneIndex zone_measurable

theorem original_ao_energy_twenty_five_cells :
    ((∑ i : Fin 5 × Fin 5, cellEnergy i : ℝ) : ℂ) =
      (1 / 2 : ℂ) *
      ∑ a : SourceFiniteData.Basis, ∑ b : SourceFiniteData.Basis,
        ∑ c : SourceFiniteData.Basis, ∑ d : SourceFiniteData.Basis,
          spinSummedTwoBody a b c d *
            ((∑ i : SourceFiniteData.Basis, ∑ j : SourceFiniteData.Basis,
              ∑ k : SourceFiniteData.Basis, ∑ l : SourceFiniteData.Basis,
                (normalizedSourceFrame i a * normalizedSourceFrame j c *
                  normalizedSourceFrame k b * normalizedSourceFrame l d) *
                    electronRepulsion i j k l) : ℝ) :=
  Partition.Finite.original_ao_energy zoneIndex zone_measurable

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Fifth
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
