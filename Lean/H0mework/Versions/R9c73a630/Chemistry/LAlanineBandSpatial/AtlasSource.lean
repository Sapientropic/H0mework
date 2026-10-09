import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.ParameterDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuationParameter Set MeasureTheory
noncomputable section

theorem ordered_source_intervals : ∀ c d : FullBandCell, c < d → cellV c 1 ≤ cellV d 0 := by
  decide +kernel

theorem consecutive_source_intervals : ∀ c : Fin 31,
    cellV ⟨c.val,by omega⟩ 1 = cellV ⟨c.val+1,by omega⟩ 0 := by
  decide +kernel

theorem domain_compact (c : FullBandCell) : IsCompact (cellDomain c) := by
  rw [domain_eq_Icc]
  exact isCompact_Icc

theorem domain_measurable (c : FullBandCell) : MeasurableSet (cellDomain c) :=
  (domain_compact c).isClosed.measurableSet

theorem overlap_on_original_face (c d : FullBandCell) (ordered : c < d)
    (p : Point) (inside : p ∈ cellDomain c ∩ cellDomain d) : p 1 = (cellV c 1 : ℝ) := by
  exact le_antisymm inside.1.2.1.2
    ((Rat.cast_le.mpr (ordered_source_intervals c d ordered)).trans inside.2.2.1.1)

theorem ordered_overlap_volume_zero (c d : FullBandCell) (ordered : c < d) :
    volume (cellDomain c ∩ cellDomain d) = 0 := by
  have subset : cellDomain c ∩ cellDomain d ⊆
      Icc (![0,(cellV c 1 : ℝ),-(1/2 : ℝ)] : Point) ![1,(cellV c 1 : ℝ),(1/2 : ℝ)] := by
    intro p hp
    have v := overlap_on_original_face c d ordered p hp
    constructor <;> intro i <;> fin_cases i
    · exact hp.1.1.1
    · exact v.ge
    · exact hp.1.2.2.1
    · exact hp.1.1.2
    · exact v.le
    · exact hp.1.2.2.2
  apply measure_mono_null subset
  rw [Real.volume_Icc_pi]
  exact Finset.prod_eq_zero_iff.mpr ⟨(1 : Fin 3),Finset.mem_univ _,by simp⟩

theorem source_overlap_volume_zero (c d : FullBandCell) (different : c ≠ d) :
    volume (cellDomain c ∩ cellDomain d) = 0 := by
  rcases lt_or_gt_of_ne different with h | h
  · exact ordered_overlap_volume_zero c d h
  · rw [inter_comm]
    exact ordered_overlap_volume_zero d c h

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
