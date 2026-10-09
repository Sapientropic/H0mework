import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandHighJet.TilesModel

set_option autoImplicit false
set_option maxRecDepth 65536

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open WholeBandSource SourceIntegerGrid SourceSignedEvaluator SourceRectangle SourceExponential

abbrev IntegerBox := Fin 3 → Interval

def IntegerContains (outer inner : IntegerBox) : Prop :=
  ∀ a, (outer a).1 ≤ (inner a).1 ∧ (inner a).2 ≤ (outer a).2

theorem IntegerContains.refl (box : IntegerBox) : IntegerContains box box :=
  fun _ => ⟨le_rfl, le_rfl⟩

theorem IntegerContains.trans {a b c : IntegerBox}
    (ab : IntegerContains a b) (bc : IntegerContains b c) : IntegerContains a c :=
  fun axis => ⟨(ab axis).1.trans (bc axis).1, (bc axis).2.trans (ab axis).2⟩

theorem mergeBox_contains_left (a b : IntegerBox) : IntegerContains (mergeBox a b) a :=
  fun _ => ⟨min_le_left _ _, le_max_left _ _⟩

theorem mergeBox_contains_right (a b : IntegerBox) : IntegerContains (mergeBox a b) b :=
  fun _ => ⟨min_le_right _ _, le_max_right _ _⟩

theorem fold_contains_initial (xs : List IntegerBox) (initial : IntegerBox) :
    IntegerContains (xs.foldl mergeBox initial) initial := by
  induction xs generalizing initial with
  | nil => exact IntegerContains.refl initial
  | cons head tail ih =>
      exact (ih (mergeBox initial head)).trans (mergeBox_contains_left initial head)

theorem fold_contains_member (xs : List IntegerBox) (initial box : IntegerBox)
    (member : box ∈ xs) : IntegerContains (xs.foldl mergeBox initial) box := by
  induction xs generalizing initial with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | rest
      · subst box
        exact (fold_contains_initial tail (mergeBox initial head)).trans
          (mergeBox_contains_right initial head)
      · exact ih (mergeBox initial head) rest

theorem tileHull_contains (t : Tile) (i : Slot) :
    IntegerContains (tileHull t) (callIntegers (tileCall t i)) :=
  fold_contains_member _ _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem original_call_hull (f : FullBandCall) :
    IntegerContains (tileHull (tileOf f)) (callIntegers f) := by
  simpa only [every_original_call] using tileHull_contains (tileOf f) (slotOf f)

theorem integer_midpoint_bounds (p : Interval) (ordered : p.1 ≤ p.2) :
    p.1 ≤ (p.1+p.2)/2 ∧ (p.1+p.2)/2 ≤ p.2 := by omega

theorem integerContains_holds (outer inner : IntegerBox)
    (contains : IntegerContains outer inner) (x : SourceGaussianModel.Point)
    (inside : InRectangle (fun a => integerInterval (inner a)) x) :
    InRectangle (fun a => integerInterval (outer a)) x := by
  intro a
  have low : (integerInterval (outer a)).1 ≤ (integerInterval (inner a)).1 :=
    div_le_div_of_nonneg_right (by exact_mod_cast (contains a).1) scale_positive.le
  have high : (integerInterval (inner a)).2 ≤ (integerInterval (outer a)).2 :=
    div_le_div_of_nonneg_right (by exact_mod_cast (contains a).2) scale_positive.le
  have lowReal : ((integerInterval (outer a)).1 : ℝ) ≤ ((integerInterval (inner a)).1 : ℝ) :=
    by exact_mod_cast low
  have highReal : ((integerInterval (inner a)).2 : ℝ) ≤ ((integerInterval (outer a)).2 : ℝ) :=
    by exact_mod_cast high
  exact ⟨lowReal.trans (inside a).1, (inside a).2.trans highReal⟩

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
