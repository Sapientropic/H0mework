import H0mework.Chemistry.LAlanineBandHighJet.TilesData
import H0mework.Chemistry.LAlanineBandHighJet.TilesGeometry

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open WholeBandSource SourceIntegerGrid SourceSignedEvaluator SourceRectangle SourceExponential

theorem literalHull_original (t : Tile) : literalHull t = tileHull t := by
  funext a
  rw [literal_hull_fold]
  simp only [literalCall_tileCall]
  rfl

theorem literalCenter_original (t : Tile) (a : Fin 3) :
    literalCenter t a = tileCenter t a := by
  rw [literal_center_midpoint, literalHull_original]
  rfl

noncomputable def tileBox (t : Tile) : Rectangle := fun a => integerInterval (literalHull t a)
noncomputable def center (t : Tile) : Fin 3 → ℚ := fun a => (literalCenter t a : ℚ)/scale

theorem tileBox_original (t : Tile) : tileBox t = fun a => integerInterval (tileHull t a) := by
  exact congrArg (fun box : IntegerBox => fun a => integerInterval (box a)) (literalHull_original t)

theorem center_original (t : Tile) (a : Fin 3) : center t a = (tileCenter t a : ℚ)/scale := by
  rw [center, literalCenter_original]

theorem center_inside (t : Tile) : InRectangle (tileBox t) (fun a => (center t a : ℝ)) := by
  intro a
  have bounds := integer_midpoint_bounds (literalHull t a) (literal_hull_ordered t a)
  rw [← literal_center_midpoint] at bounds
  have low : ((literalHull t a).1 : ℚ)/scale ≤ center t a :=
    div_le_div_of_nonneg_right (by exact_mod_cast bounds.1) scale_positive.le
  have high : center t a ≤ ((literalHull t a).2 : ℚ)/scale :=
    div_le_div_of_nonneg_right (by exact_mod_cast bounds.2) scale_positive.le
  change (↑(((literalHull t a).1 : ℚ)/scale) : ℝ) ≤ (center t a : ℝ) ∧
    (center t a : ℝ) ≤ (↑(((literalHull t a).2 : ℚ)/scale) : ℝ)
  constructor
  · exact_mod_cast low
  · exact_mod_cast high

theorem call_inside_hull (f : FullBandCall) (x : SourceGaussianModel.Point)
    (inside : InRectangle (callBox f) x) : InRectangle (tileBox (tileOf f)) x := by
  apply integerContains_holds (literalHull (tileOf f)) (callIntegers f)
  · rw [literalHull_original]
    exact original_call_hull f
  · exact inside

def memberCalls (t : Tile) : List FullBandCall := List.ofFn (tileCall t)

theorem memberCalls_length (t : Tile) : (memberCalls t).length = 32 := by
  simp [memberCalls]

theorem mem_memberCalls (t : Tile) (f : FullBandCall) : f ∈ memberCalls t ↔ tileOf f = t := by
  constructor
  · intro member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact tileOf_tileCall t i
  · intro same
    subst t
    exact List.mem_ofFn.mpr ⟨slotOf f, every_original_call f⟩

theorem original_call_unique_tile (f : FullBandCall) : ∃! t : Tile, f ∈ memberCalls t := by
  refine ⟨tileOf f, (mem_memberCalls _ _).mpr rfl, ?_⟩
  intro t member
  exact ((mem_memberCalls t f).mp member).symm

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
