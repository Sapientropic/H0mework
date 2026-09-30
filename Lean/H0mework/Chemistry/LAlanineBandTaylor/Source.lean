import H0mework.Chemistry.LAlanineBandTaylor.Soundness
import H0mework.Chemistry.LAlanineRefinementSource.JetIncidence
import H0mework.Chemistry.LAlanineParametric.IntervalStage
import H0mework.Chemistry.LAlanineSignedEvaluator.Gaussian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor

open SourceGaussianModel SourceFiniteData SourceJetIncidence SourceSignedEvaluator
open ContinuousGradient IntervalParameterMap Set
noncomputable section

def centerPoint (c : Fin 3 → ℚ) : Point := fun i => (c i : ℝ)
def deltaBox (c : Fin 3 → ℚ) (box : Rectangle) : Fin 3 → Pair :=
  fun i => ((box i).1-c i,(box i).2-c i)
def boxRadius (c : Fin 3 → ℚ) (box : Rectangle) : Fin 3 → ℚ :=
  fun i => max |(deltaBox c box i).1| |(deltaBox c box i).2|
def indexedPair (A : JetIndex → Pair) (m : MultiIndex) : Pair := A (sourceJetIndex m)
def absolutePair (p : Pair) : ℚ := max |p.1| |p.2|
def indexedAbs (B : JetIndex → Pair) (m : MultiIndex) : ℚ := absolutePair (B (sourceJetIndex m))

def sourceEnclosure (n : ℕ) (m : MultiIndex) (c : Fin 3 → ℚ) (box : Rectangle)
    (A B : JetIndex → Pair) : Pair :=
  enclosure n (indexedPair A) (indexedAbs B) m (deltaBox c box) (boxRadius c box)

def fieldEnclosure (c : Fin 3 → ℚ) (box : Rectangle) (A B : JetIndex → Pair) : FieldBox where
  gradient a := sourceEnclosure 2 (raise zeroJet a) c box A B
  hessian a b := sourceEnclosure 1 (raise (raise zeroJet a) b) c box A B

def CenterBounds (c : Fin 3 → ℚ) (A : JetIndex → Pair) : Prop :=
  ∀ j, jetOrder (jetMulti j) ≤ 3 → Holds (A j) (sourceJet j (centerPoint c))

def FourthBounds (hull : Rectangle) (B : JetIndex → Pair) : Prop :=
  ∀ j, jetOrder (jetMulti j) = 4 → ∀ x, InRectangle hull x → Holds (B j) (sourceJet j x)

theorem sourceJet_recovered (m : MultiIndex) (hm : jetOrder m ≤ 4) :
    sourceJet (sourceJetIndex m) = densityJet m := by
  rw [sourceJet, SourceJetIncidence.source_jet_recovered m hm]

theorem absolutePair_bound (p : Pair) (x : ℝ) (h : Holds p x) : |x| ≤ (absolutePair p : ℝ) := by
  simp only [absolutePair, Rat.cast_max, Rat.cast_abs]
  apply abs_le.mpr
  exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans h.1),
    h.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩

theorem indexedPair_center (c : Fin 3 → ℚ) (A : JetIndex → Pair) (ha : CenterBounds c A)
    (m : MultiIndex) (hm : jetOrder m ≤ 3) :
    Holds (indexedPair A m) (densityJet m (centerPoint c)) := by
  have recover := SourceJetIncidence.source_jet_recovered m (by omega)
  have h := ha (sourceJetIndex m) (by rw [recover]; exact hm)
  rwa [sourceJet_recovered m (by omega)] at h

theorem indexedAbs_fourth (hull : Rectangle) (B : JetIndex → Pair) (hb : FourthBounds hull B)
    (m : MultiIndex) (hm : jetOrder m = 4) (x : Point) (hx : InRectangle hull x) :
    |densityJet m x| ≤ (indexedAbs B m : ℝ) := by
  have recover := SourceJetIncidence.source_jet_recovered m (by omega)
  have h := hb (sourceJetIndex m) (by rw [recover]; exact hm) x hx
  rw [sourceJet_recovered m (by omega)] at h
  exact absolutePair_bound _ _ h

theorem shift_order (m a : MultiIndex) : jetOrder (shift m a) = jetOrder m + jetOrder a := by
  simp only [jetOrder, shift]
  omega

theorem deltaBox_holds (c : Fin 3 → ℚ) (box : Rectangle) (x : Point)
    (hx : InRectangle box x) (i : Fin 3) : Holds (deltaBox c box i) ((x-centerPoint c) i) := by
  simpa only [Holds, deltaBox, Rat.cast_sub, Pi.sub_apply, centerPoint] using
    And.intro (sub_le_sub_right (hx i).1 (c i : ℝ)) (sub_le_sub_right (hx i).2 (c i : ℝ))

theorem segment_in_rectangle (hull : Rectangle) (c x : Point)
    (hc : InRectangle hull c) (hx : InRectangle hull x) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    InRectangle hull (segment c (x-c) t) := by
  intro i
  have hci := hc i
  have hxi := hx i
  change ((hull i).1 : ℝ) ≤ c i + t*(x i-c i) ∧ c i + t*(x i-c i) ≤ ((hull i).2 : ℝ)
  have lo := add_nonneg
    (mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hci.1))
    (mul_nonneg ht.1 (sub_nonneg.mpr hxi.1))
  have hi := add_nonneg
    (mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hci.2))
    (mul_nonneg ht.1 (sub_nonneg.mpr hxi.2))
  constructor <;> nlinarith

/-- A common hull supplies fourth jets; each original rectangle retains its own restriction. -/
theorem sourceEnclosure_contains (n : Fin 3) (m : MultiIndex) (scope : jetOrder m+n.val = 3)
    (c : Fin 3 → ℚ) (box hull : Rectangle) (A B : JetIndex → Pair)
    (ha : CenterBounds c A) (hb : FourthBounds hull B)
    (hc : InRectangle hull (centerPoint c))
    (subset : ∀ x, InRectangle box x → InRectangle hull x)
    (x : Point) (hx : InRectangle box x) :
    Holds (sourceEnclosure n.val m c box A B) (densityJet m x) := by
  have result := enclosure_contains n m (centerPoint c) (x-centerPoint c)
    (indexedPair A) (indexedAbs B) (deltaBox c box) (boxRadius c box) ?_ ?_
    (deltaBox_holds c box x hx) (fun i => absolutePair_bound _ _ (deltaBox_holds c box x hx i))
  · simpa only [sourceEnclosure, add_sub_cancel] using result
  · intro k hk a hmem
    apply indexedPair_center c A ha
    rw [shift_order, increments_order ⟨k,by omega⟩ a hmem]
    change jetOrder m+k ≤ 3
    omega
  · intro t ht a hmem
    apply indexedAbs_fourth hull B hb
    · rw [shift_order, increments_order ⟨n.val+1,by omega⟩ a hmem]
      change jetOrder m+(n.val+1) = 4
      omega
    · exact segment_in_rectangle hull (centerPoint c) x hc (subset x hx) t ht

/-- The original source g/H are generated from finite center and same-hull fourth-jet materials. -/
theorem fieldEnclosure_contains (c : Fin 3 → ℚ) (box hull : Rectangle) (A B : JetIndex → Pair)
    (ha : CenterBounds c A) (hb : FourthBounds hull B)
    (hc : InRectangle hull (centerPoint c))
    (subset : ∀ x, InRectangle box x → InRectangle hull x)
    (x : Point) (hx : InRectangle box x) : FieldHolds (fieldEnclosure c box A B) x := by
  constructor
  · intro a
    have h := sourceEnclosure_contains 2 (raise zeroJet a)
      (by simp only [jetOrder_raise]; norm_num [zeroJet,jetOrder]) c box hull A B ha hb hc subset x hx
    rwa [densityJet_first] at h
  · intro a b
    have h := sourceEnclosure_contains 1 (raise (raise zeroJet a) b)
      (by simp only [jetOrder_raise]; norm_num [zeroJet,jetOrder]) c box hull A B ha hb hc subset x hx
    rwa [densityJet_second] at h

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
