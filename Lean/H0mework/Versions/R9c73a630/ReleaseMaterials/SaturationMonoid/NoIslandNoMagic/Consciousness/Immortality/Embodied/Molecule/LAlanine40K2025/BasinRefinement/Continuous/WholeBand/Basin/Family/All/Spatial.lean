import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Separation
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Partition.AtomicFamily

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceGaussianModel GlobalSource Set MeasureTheory Function Filter
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open scoped Topology
noncomputable section

def sourceBasin (i : Fin 13) : Set Point := Family.basin (sourceSeed i)
def label : Point → Option (Fin 13) := Partition.AtomicFamily.locate sourceSeed
def region (i : Option (Fin 13)) : Set Point := Partition.Finite.region label i
def pairCell (ij : Option (Fin 13) × Option (Fin 13)) : Set (Point × Point) :=
  Partition.Finite.pairCell label ij
def cellEnergy (ij : Option (Fin 13) × Option (Fin 13)) : ℝ :=
  Partition.AtomicFamily.cellEnergy sourceSeed ij

theorem all_basins_open (i : Fin 13) : IsOpen (sourceBasin i) :=
  Family.basin_open (sourceSeed i)
theorem all_basins_positive (i : Fin 13) : 0 < volume (sourceBasin i) :=
  Family.basin_positive_volume (sourceSeed i)
theorem all_basins_patch_cover (i : Fin 13) :
    sourceBasin i = ⋃ n : ℕ, Family.entryPatch (sourceSeed i) n :=
  Family.basin_eq_union (sourceSeed i)

theorem original_region (i : Fin 13) : region (some i)=sourceBasin i :=
  Partition.AtomicFamily.original_atom_region sourceSeed source_basins_disjoint i

theorem original_residual : region none=(⋃ i : Fin 13, sourceBasin i)ᶜ :=
  Partition.AtomicFamily.actual_residual_region sourceSeed

theorem all_regions_measurable (i : Option (Fin 13)) : MeasurableSet (region i) :=
  Partition.AtomicFamily.fibers_measurable sourceSeed source_basins_disjoint i

theorem all_pair_cells_measurable (ij : Option (Fin 13) × Option (Fin 13)) :
    MeasurableSet (pairCell ij) :=
  Partition.Finite.pairCell_measurable label all_regions_measurable ij

theorem all_pair_cells_disjoint : Pairwise (Disjoint on pairCell) :=
  Partition.Finite.pairCells_disjoint label

theorem all_pair_cells_cover :
    (⋃ ij : Option (Fin 13) × Option (Fin 13), pairCell ij)=Set.univ :=
  Partition.Finite.pairCells_cover label

theorem all_cell_energy_nonnegative (ij : Option (Fin 13) × Option (Fin 13)) :
    0 ≤ cellEnergy ij :=
  Partition.AtomicFamily.cell_energy_nonnegative sourceSeed source_basins_disjoint ij

theorem all_cell_energy_symmetric (i j : Option (Fin 13)) :
    cellEnergy (i,j)=cellEnergy (j,i) :=
  Partition.AtomicFamily.cell_energy_symmetric sourceSeed i j

theorem all_energy_exact :
    (∑ ij : Option (Fin 13) × Option (Fin 13), cellEnergy ij)=pairCoulombEnergy.re :=
  Partition.AtomicFamily.full_energy sourceSeed source_basins_disjoint

theorem all_original_ao_energy :
    ((∑ ij : Option (Fin 13) × Option (Fin 13), cellEnergy ij : ℝ) : ℂ) =
      (1 / 2 : ℂ) *
      ∑ a : SourceFiniteData.Basis, ∑ b : SourceFiniteData.Basis,
        ∑ c : SourceFiniteData.Basis, ∑ d : SourceFiniteData.Basis,
          spinSummedTwoBody a b c d *
            ((∑ i : SourceFiniteData.Basis, ∑ j : SourceFiniteData.Basis,
              ∑ k : SourceFiniteData.Basis, ∑ l : SourceFiniteData.Basis,
                (normalizedSourceFrame i a * normalizedSourceFrame j c *
                  normalizedSourceFrame k b * normalizedSourceFrame l d) *
                    electronRepulsion i j k l) : ℝ) :=
  Partition.AtomicFamily.original_ao_energy sourceSeed source_basins_disjoint

theorem every_original_intra_energy (i : Fin 13) :
    cellEnergy (some i,some i)=
      Family.halfPairEnergy (sourceSeed i) (sourceSeed i) :=
  Partition.AtomicFamily.atom_cell_energy sourceSeed source_basins_disjoint i i

theorem every_original_pair_energy (i j : Fin 13) :
    cellEnergy (some i,some j)+cellEnergy (some j,some i)=
      Family.interatomicPairEnergy (sourceSeed i) (sourceSeed j) :=
  Partition.AtomicFamily.atom_pair_energy sourceSeed source_basins_disjoint i j

theorem every_original_pair_patch_limit (i j : Fin 13) :
    Tendsto (fun n : ℕ => (1/2 : ℝ) * ∫ z in
      Family.pairPatch (sourceSeed i) (sourceSeed j) n, realPairIntegrand z) atTop
      (𝓝 (Family.halfPairEnergy (sourceSeed i) (sourceSeed j))) :=
  Partition.AtomicFamily.atom_pair_patch_limit sourceSeed i j


theorem every_original_pair_cell_nonempty (i j : Fin 13) :
    (pairCell (some i,some j)).Nonempty := by
  have hi : (sourceSeed i).criticalPoint ∈ region (some i) := by
    rw [original_region]
    exact Family.neighborhood_subset_basin (sourceSeed i) (sourceSeed i).criticalInside
  have hj : (sourceSeed j).criticalPoint ∈ region (some j) := by
    rw [original_region]
    exact Family.neighborhood_subset_basin (sourceSeed j) (sourceSeed j).criticalInside
  refine ⟨((sourceSeed i).criticalPoint,(sourceSeed j).criticalPoint),?_⟩
  change ((sourceSeed i).criticalPoint,(sourceSeed j).criticalPoint) ∈
    Partition.Finite.pairCell label (some i,some j)
  rw [Partition.Finite.pairCell_prod]
  exact ⟨hi,hj⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
