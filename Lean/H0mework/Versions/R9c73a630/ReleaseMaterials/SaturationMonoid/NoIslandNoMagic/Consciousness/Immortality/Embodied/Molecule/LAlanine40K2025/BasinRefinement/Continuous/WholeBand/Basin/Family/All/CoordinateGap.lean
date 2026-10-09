import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.SourceCenters

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceExponential
noncomputable section

def scaledCentreX (i : Fin 13) : ℝ := (((sourceX i : ℚ)/scale) : ℝ)
def scaledRadius : ℝ := (((radiusGrid : ℚ)/scale) : ℝ)

private theorem scaled_gap (a b r : Int) (s : ℚ) (hs : 0 < s)
    (h : a+r < b-r) :
    (((a : ℚ)/s : ℚ) : ℝ)+((((r : ℚ)/s : ℚ)) : ℝ) <
      (((b : ℚ)/s : ℚ) : ℝ)-((((r : ℚ)/s : ℚ)) : ℝ) := by
  have hc : ((a : ℚ)+(r : ℚ)) < ((b : ℚ)-(r : ℚ)) := by exact_mod_cast h
  have hq : ((a : ℚ)+(r : ℚ))/s < ((b : ℚ)-(r : ℚ))/s :=
    (div_lt_div_iff_of_pos_right hs).2 hc
  have hr : ((((a : ℚ)+(r : ℚ))/s : ℚ) : ℝ) <
      ((((b : ℚ)-(r : ℚ))/s : ℚ) : ℝ) := Rat.cast_lt.mpr hq
  simpa only [add_div,sub_div,Rat.cast_add,Rat.cast_sub] using hr

theorem scaled_radius_actual : scaledRadius=(1/1048576 : ℝ) := by
  norm_num [scaledRadius,radiusGrid,scale]

theorem scaled_centres_gap (i j : Fin 13) (different : i ≠ j) :
    scaledCentreX i+scaledRadius < scaledCentreX j-scaledRadius ∨
    scaledCentreX j+scaledRadius < scaledCentreX i-scaledRadius := by
  have scalePositive : (0 : ℚ) < scale := by norm_num [scale]
  rcases source_centres_separated i j different with h | h
  · left
    simpa only [scaledCentreX,scaledRadius,Rat.cast_div,Rat.cast_intCast] using
      scaled_gap (sourceX i) (sourceX j) radiusGrid scale scalePositive h
  · right
    simpa only [scaledCentreX,scaledRadius,Rat.cast_div,Rat.cast_intCast] using
      scaled_gap (sourceX j) (sourceX i) radiusGrid scale scalePositive h

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
