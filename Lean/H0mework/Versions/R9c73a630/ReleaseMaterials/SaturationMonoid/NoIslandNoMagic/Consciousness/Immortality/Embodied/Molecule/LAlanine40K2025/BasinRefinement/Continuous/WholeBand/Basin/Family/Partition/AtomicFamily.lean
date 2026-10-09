import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Partition.UniqueIndex
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Interaction

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition.AtomicFamily
open SourceGaussianModel GlobalSource Set MeasureTheory Function Filter
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open scoped Topology
noncomputable section

variable {ι : Type*} [Fintype ι] (seeds : ι → Family.AttractingSeed)

def atomRegion (i : ι) : Set Point := Family.basin (seeds i)
def locate : Point → Option ι := UniqueIndex.locate (atomRegion seeds)
def cellEnergy (pair : Option ι × Option ι) : ℝ :=
  Finite.cellEnergy (locate seeds) pair

omit [Fintype ι] in
theorem atom_region_measurable (i : ι) : MeasurableSet (atomRegion seeds i) :=
  Family.basin_measurable (seeds i)

theorem fibers_measurable
    (disjoint : Pairwise (Disjoint on atomRegion seeds)) (label : Option ι) :
    MeasurableSet (Finite.region (locate seeds) label) :=
  UniqueIndex.fibers_measurable (atomRegion seeds) disjoint
    (atom_region_measurable seeds) label

theorem original_atom_region
    (disjoint : Pairwise (Disjoint on atomRegion seeds)) (i : ι) :
    Finite.region (locate seeds) (some i)=Family.basin (seeds i) :=
  UniqueIndex.some_region (atomRegion seeds) disjoint i

theorem actual_residual_region :
    Finite.region (locate seeds) none=(⋃ i, Family.basin (seeds i))ᶜ :=
  UniqueIndex.residual_region (atomRegion seeds)

theorem full_energy (disjoint : Pairwise (Disjoint on atomRegion seeds)) :
    (∑ pair : Option ι × Option ι, cellEnergy seeds pair)=pairCoulombEnergy.re :=
  Finite.full_energy (locate seeds) (fibers_measurable seeds disjoint)

theorem original_ao_energy (disjoint : Pairwise (Disjoint on atomRegion seeds)) :
    ((∑ pair : Option ι × Option ι, cellEnergy seeds pair : ℝ) : ℂ) =
      (1 / 2 : ℂ) *
      ∑ a : SourceFiniteData.Basis, ∑ b : SourceFiniteData.Basis,
        ∑ c : SourceFiniteData.Basis, ∑ d : SourceFiniteData.Basis,
          spinSummedTwoBody a b c d *
            ((∑ i : SourceFiniteData.Basis, ∑ j : SourceFiniteData.Basis,
              ∑ k : SourceFiniteData.Basis, ∑ l : SourceFiniteData.Basis,
                (normalizedSourceFrame i a * normalizedSourceFrame j c *
                  normalizedSourceFrame k b * normalizedSourceFrame l d) *
                    electronRepulsion i j k l) : ℝ) :=
  Finite.original_ao_energy (locate seeds) (fibers_measurable seeds disjoint)

theorem cell_energy_nonnegative
    (disjoint : Pairwise (Disjoint on atomRegion seeds)) (pair : Option ι × Option ι) :
    0 ≤ cellEnergy seeds pair :=
  Finite.cell_energy_nonnegative (locate seeds) (fibers_measurable seeds disjoint) pair

theorem cell_energy_symmetric (i j : Option ι) :
    cellEnergy seeds (i,j)=cellEnergy seeds (j,i) :=
  Finite.cell_energy_symmetric (locate seeds) i j

theorem atom_cell_energy
    (disjoint : Pairwise (Disjoint on atomRegion seeds)) (i j : ι) :
    cellEnergy seeds (some i,some j)=
      Family.halfPairEnergy (seeds i) (seeds j) := by
  dsimp [cellEnergy,Finite.cellEnergy]
  rw [Finite.pairCell_prod]
  change (1/2 : ℝ) * ∫ z in
    Finite.region (locate seeds) (some i) ×ˢ
      Finite.region (locate seeds) (some j), realPairIntegrand z = _
  rw [original_atom_region seeds disjoint i,
    original_atom_region seeds disjoint j]
  rfl

theorem atom_pair_energy
    (disjoint : Pairwise (Disjoint on atomRegion seeds)) (i j : ι) :
    cellEnergy seeds (some i,some j)+cellEnergy seeds (some j,some i)=
      Family.interatomicPairEnergy (seeds i) (seeds j) := by
  calc
    _ = 2*cellEnergy seeds (some i,some j) := by
      rw [← cell_energy_symmetric seeds (some i) (some j)]
      ring
    _ = 2*Family.halfPairEnergy (seeds i) (seeds j) := by
      rw [atom_cell_energy seeds disjoint i j]
    _ = Family.interatomicPairEnergy (seeds i) (seeds j) :=
      (Family.interatomic_pair_energy_twice _ _).symm

omit [Fintype ι] in
theorem atom_pair_patch_limit (i j : ι) :
    Tendsto (fun n : ℕ => (1/2 : ℝ) * ∫ z in
      Family.pairPatch (seeds i) (seeds j) n, realPairIntegrand z) atTop
      (𝓝 (Family.halfPairEnergy (seeds i) (seeds j))) :=
  Family.half_pair_energy_patch_limit _ _

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition.AtomicFamily
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
