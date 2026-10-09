import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Third
import Mathlib.Data.Set.Pairwise.Basic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition
open SourceGaussianModel WholeBandBasin Set MeasureTheory Function
noncomputable section

def zoneIndex (x : Point) : Fin 4 := by
  classical
  exact if x ∈ Family.atom006Basin then 0 else
    if x ∈ WholeBandBasin.basin then 1 else
    if x ∈ Family.atom009Basin then 2 else 3

def zone (i : Fin 4) : Set Point := zoneIndex ⁻¹' {i}
def pairIndex (z : Point × Point) : Fin 4 × Fin 4 := (zoneIndex z.1,zoneIndex z.2)
def pairCell (i : Fin 4 × Fin 4) : Set (Point × Point) := pairIndex ⁻¹' {i}

theorem zoneIndex_measurable : Measurable zoneIndex := by
  classical
  unfold zoneIndex
  exact Measurable.ite Family.atom006_basin_open.measurableSet measurable_const
    (Measurable.ite WholeBandBasin.basin_measurable measurable_const
      (Measurable.ite Family.atom009_basin_open.measurableSet measurable_const measurable_const))

theorem zone_measurable (i : Fin 4) : MeasurableSet (zone i) :=
  zoneIndex_measurable (measurableSet_singleton i)

theorem pairCell_prod (i : Fin 4 × Fin 4) :
    pairCell i=zone i.1 ×ˢ zone i.2 := by
  rcases i with ⟨a,b⟩
  ext z
  simp [pairCell,pairIndex,zone,Prod.mk.injEq]

theorem pairCell_measurable (i : Fin 4 × Fin 4) : MeasurableSet (pairCell i) := by
  rw [pairCell_prod]
  exact (zone_measurable i.1).prod (zone_measurable i.2)

theorem pairCells_disjoint : Pairwise (Disjoint on pairCell) :=
  pairwise_disjoint_fiber pairIndex

theorem pairCells_cover : (⋃ i : Fin 4 × Fin 4, pairCell i)=Set.univ := by
  ext z
  simp only [Set.mem_iUnion,Set.mem_univ,iff_true,pairCell,Set.mem_preimage,Set.mem_singleton_iff]
  exact ⟨pairIndex z,rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
