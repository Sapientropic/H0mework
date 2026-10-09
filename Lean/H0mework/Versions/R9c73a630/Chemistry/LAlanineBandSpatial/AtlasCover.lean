import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandSpatial.AtlasCarrier

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuationParameter Set
noncomputable section

theorem outer_source_bounds : ∀ c : FullBandCell,
    cellV 0 0 ≤ cellV c 0 ∧ cellV c 1 ≤ cellV 31 1 := by decide +kernel

private theorem source_cover_through (n : Nat) (hn : n < 32) (v : ℝ)
    (lower : (cellV 0 0 : ℝ) ≤ v) (upper : v ≤ (cellV ⟨n,hn⟩ 1 : ℝ)) :
    ∃ c : FullBandCell, c.val ≤ n ∧ v ∈ Icc (cellV c 0 : ℝ) (cellV c 1) := by
  induction n with
  | zero => exact ⟨0,le_rfl,lower,upper⟩
  | succ n ih =>
      have hn' : n < 32 := by omega
      by_cases h : v ≤ (cellV ⟨n,hn'⟩ 1 : ℝ)
      · obtain ⟨c,hc,inside⟩ := ih hn' h
        exact ⟨c,by omega,inside⟩
      · have sourceSeam := consecutive_source_intervals ⟨n,by omega⟩
        have seam : (cellV ⟨n,hn'⟩ 1 : ℝ) = (cellV ⟨n+1,hn⟩ 0 : ℝ) :=
          congrArg (fun r : ℚ => (r : ℝ)) sourceSeam
        exact ⟨⟨n+1,hn⟩,le_rfl,seam ▸ (lt_of_not_ge h).le,upper⟩

theorem original_v_covered (v : ℝ) (inside : v ∈ Icc (cellV 0 0 : ℝ) (cellV 31 1)) :
    ∃ c : FullBandCell, v ∈ Icc (cellV c 0 : ℝ) (cellV c 1) := by
  obtain ⟨c,_,hc⟩ := source_cover_through 31 (by decide) v inside.1 inside.2
  exact ⟨c,hc⟩

/-- The common parameter carrier is the complete original closed band, including all31 seams. -/
theorem bandDomain_eq_Icc : bandDomain = Icc (cellLower 0) (cellUpper 31) := by
  ext p
  constructor
  · intro hp
    obtain ⟨c,hc⟩ := mem_iUnion.mp hp
    have outer := outer_source_bounds c
    constructor <;> intro i <;> fin_cases i
    · exact hc.1.1
    · exact (Rat.cast_le.mpr outer.1).trans hc.2.1.1
    · exact hc.2.2.1
    · exact hc.1.2
    · exact hc.2.1.2.trans (Rat.cast_le.mpr outer.2)
    · exact hc.2.2.2
  · intro hp
    obtain ⟨c,hc⟩ := original_v_covered (p 1) ⟨hp.1 1,hp.2 1⟩
    exact mem_iUnion.mpr ⟨c,⟨hp.1 0,hp.2 0⟩,hc,⟨hp.1 2,hp.2 2⟩⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
