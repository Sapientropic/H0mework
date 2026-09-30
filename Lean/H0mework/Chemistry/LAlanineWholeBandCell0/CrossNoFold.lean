import H0mework.Chemistry.LAlanineWholeBandCell0.CrossMeeting

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCrossGeometry

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel WholeBandGeometry WholeBandActual WholeBandCell0Geometry
open TrueFlowGeometry TrueFlowDifferential TrueTubeActual TrueTubeWholeActual WholeCellPartition Set
noncomputable section

theorem cell0_cell16_parameter_maps_ne (p : Cell0Point) (q : BandPoint) :
    cell0ParameterMap p.val ≠ trueParameterMap q.val :=
  cell0_cell16_actual_ne p q ⟨p.val 2, p.property.2.2⟩ (actualParameterTime q)

theorem cell0_cell16_actual_images_disjoint :
    Disjoint (cell0ParameterMap '' cellDomain 0) truePatch := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, left⟩ ⟨q, hq, right⟩
  exact cell0_cell16_parameter_maps_ne ⟨p, hp⟩ ⟨q, hq⟩ (left.trans right.symm)

def paidPairMap : Cell0Point ⊕ BandPoint → Point :=
  Sum.elim (fun p => cell0ParameterMap p.val) (fun p => trueParameterMap p.val)

theorem paidPairMap_injective : Function.Injective paidPairMap := by
  intro p q meeting
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (cell0ParameterMap_injective meeting)
    | inr q => exact False.elim (cell0_cell16_parameter_maps_ne p q meeting)
  | inr p =>
    cases q with
    | inl q => exact False.elim (cell0_cell16_parameter_maps_ne q p meeting.symm)
    | inr q => exact congrArg Sum.inr (trueParameterMap_injective meeting)

theorem paidPairMap_range :
    range paidPairMap = (cell0ParameterMap '' cellDomain 0) ∪ truePatch := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    cases p with
    | inl p => exact Or.inl ⟨p.val, p.property, rfl⟩
    | inr p => exact Or.inr ⟨p.val, p.property, rfl⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
    · exact ⟨Sum.inr ⟨p, hp⟩, rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCrossGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
