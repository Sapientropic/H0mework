import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandSpatial.AtlasImages

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuation Set
noncomputable section

def bandDomain : Set Point := ⋃ c : FullBandCell, cellDomain c

/-- Chart selection reads one original parameter occurrence; restrictions agree at actual seams. -/
def bandMap (p : Point) : Point := by
  classical
  exact if inside : ∃ c : FullBandCell, p ∈ cellDomain c then
    sourceParameterMap (Classical.choose inside) p else 0

theorem bandMap_on_cell (c : FullBandCell) (p : Point) (inside : p ∈ cellDomain c) :
    bandMap p = sourceParameterMap c p := by
  have h : ∃ c : FullBandCell, p ∈ cellDomain c := ⟨c,inside⟩
  rw [bandMap,dif_pos h]
  unfold sourceParameterMap
  rw [seam_seed_agrees (Classical.choose h) c p (Classical.choose_spec h) inside]

theorem bandMap_image : bandMap '' bandDomain = bandImage := by
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨c,hc⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨c,p,hc,(bandMap_on_cell c p hc).symm⟩
  · intro hx
    obtain ⟨c,p,hp,hx⟩ := mem_iUnion.mp hx
    exact ⟨p,mem_iUnion.mpr ⟨c,hp⟩,(bandMap_on_cell c p hp).trans hx⟩

theorem bandMap_injOn (fields : Fields) (positive : Normals) : InjOn bandMap bandDomain := by
  intro p hp q hq same
  obtain ⟨c,hc⟩ := mem_iUnion.mp hp
  obtain ⟨d,hd⟩ := mem_iUnion.mp hq
  rw [bandMap_on_cell c p hc,bandMap_on_cell d q hd] at same
  exact (actual_parameter_meeting c d (fields c) (fields d) (positive c) (positive d) p q hc hd).mp same

theorem bandMap_continuousOn_cell (fields : Fields) (bounds : Bounds) (c : FullBandCell) :
    ContinuousOn bandMap (cellDomain c) :=
  (cellMap_continuousOn fields bounds c).congr (fun p hp => bandMap_on_cell c p hp)

private theorem continuousOn_source_union (fields : Fields) (bounds : Bounds) (s : Finset FullBandCell) :
    ContinuousOn bandMap (⋃ c ∈ s, cellDomain c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert c s hc ih =>
      rw [Finset.set_biUnion_insert]
      exact (bandMap_continuousOn_cell fields bounds c).union_of_isClosed ih
        (domain_compact c).isClosed (isClosed_biUnion_finset (fun d _ => (domain_compact d).isClosed))

theorem bandMap_continuousOn (fields : Fields) (bounds : Bounds) : ContinuousOn bandMap bandDomain := by
  simpa only [Finset.mem_univ,iUnion_true,bandDomain] using continuousOn_source_union fields bounds Finset.univ

theorem bandDomain_compact : IsCompact bandDomain := isCompact_iUnion domain_compact

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
