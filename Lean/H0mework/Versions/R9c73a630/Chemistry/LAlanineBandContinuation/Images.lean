import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.Separation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel WholeBandSource WholeBandGeometry TrueFlowDifferential Set
noncomputable section

def sourceParameterMap (c : FullBandCell) (p : Point) : Point := rawFlow (cellSeed c p) (p 2)

theorem actual_parameter_meeting (c d : FullBandCell)
    (leftFields : ∀ side, DirectionFields c side) (rightFields : ∀ side, DirectionFields d side)
    (leftPositive : PositiveNormalReports c) (rightPositive : PositiveNormalReports d)
    (p q : Point) (hp : p ∈ cellDomain c) (hq : q ∈ cellDomain d) :
    sourceParameterMap c p = sourceParameterMap d q ↔ p = q := by
  have kernel := actual_meeting_classification c d leftFields rightFields leftPositive rightPositive
    p q hp hq ⟨p 2, hp.2.2⟩ ⟨q 2, hq.2.2⟩
  constructor
  · intro meeting
    have coordinates := kernel.mp meeting
    funext i
    fin_cases i
    · exact coordinates.1
    · exact coordinates.2.1
    · exact coordinates.2.2
  · intro same
    subst q
    exact kernel.mpr ⟨rfl, rfl, rfl⟩

theorem sourceParameterMap_injOn (c : FullBandCell) (fields : ∀ side, DirectionFields c side)
    (positive : PositiveNormalReports c) : InjOn (sourceParameterMap c) (cellDomain c) :=
  fun p hp q hq same => (actual_parameter_meeting c c fields fields positive positive p q hp hq).mp same

/-- Overlap of actual images is precisely the common source-parameter restriction. -/
theorem actual_images_intersection (c d : FullBandCell)
    (leftFields : ∀ side, DirectionFields c side) (rightFields : ∀ side, DirectionFields d side)
    (leftPositive : PositiveNormalReports c) (rightPositive : PositiveNormalReports d) :
    (sourceParameterMap c '' cellDomain c) ∩ (sourceParameterMap d '' cellDomain d) =
      sourceParameterMap c '' (cellDomain c ∩ cellDomain d) := by
  ext x
  constructor
  · rintro ⟨⟨p, hp, left⟩, ⟨q, hq, right⟩⟩
    have same := (actual_parameter_meeting c d leftFields rightFields leftPositive rightPositive p q hp hq).mp
      (left.trans right.symm)
    subst q
    exact ⟨p, ⟨hp, hq⟩, left⟩
  · rintro ⟨p, ⟨hp, hq⟩, rfl⟩
    refine ⟨⟨p, hp, rfl⟩, ⟨p, hq, ?_⟩⟩
    exact ((actual_parameter_meeting c d leftFields rightFields leftPositive rightPositive p p hp hq).mpr rfl).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
