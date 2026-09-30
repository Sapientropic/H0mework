import H0mework.Chemistry.LAlanineRefinementGeometry.Incidence
import H0mework.Chemistry.LAlanineRefinementSource.FiniteData
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousSeed

open SourceGaussianModel
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Geometry
open Set Metric

noncomputable section

abbrev Segment := Fin 8

def firstKnot (segment : Segment) : Data.Knot := ⟨segment.val, by omega⟩
def lastKnot (segment : Segment) : Data.Knot := ⟨segment.val + 1, by omega⟩
def knotCoordinate (knot : Data.Knot) : ℚ := Inertia.SourceParsing.rationalRead (Source.curveKnots[knot.val]!)
def centre : Point := fun axis => (SourceFiniteData.boxCentre axis : ℝ)
def basisVector (direction : Fin 2) : Point := fun axis => (Source.basis axis direction : ℝ)

def knotFraction (segment : Segment) (v : ℝ) : ℝ :=
  (v - knotCoordinate (firstKnot segment)) /
    ((knotCoordinate (lastKnot segment) : ℝ) - knotCoordinate (firstKnot segment))

def interpolate (values : Data.Knot → ℚ) (segment : Segment) (v : ℝ) : ℝ :=
  (1 - knotFraction segment v) * values (firstKnot segment) +
    knotFraction segment v * values (lastKnot segment)

def bandWidth (segment : Segment) (epsilon v : ℝ) : ℝ :=
  interpolate Source.upper segment v - interpolate Source.lower segment v + 2 * epsilon

def bandU (segment : Segment) (epsilon : ℝ) (parameters : Point) : ℝ :=
  interpolate Source.lower segment (parameters 1) - epsilon +
    parameters 0 * bandWidth segment epsilon (parameters 1)

def bandSeed (segment : Segment) (epsilon : ℝ) (parameters : Point) : Point :=
  centre + bandU segment epsilon parameters • basisVector 0 + parameters 1 • basisVector 1

theorem source_knot_geometry :
    (∀ segment : Segment, knotCoordinate (firstKnot segment) < knotCoordinate (lastKnot segment)) ∧
    (∀ knot : Data.Knot, |knotCoordinate knot| ≤ 1 / 24 ∧
      |Source.lower knot| ≤ 1 / 8000 ∧ |Source.upper knot| ≤ 1 / 8000) ∧
    (∀ axis : Fin 3, |Source.basis axis 0| ≤ 1 ∧ |Source.basis axis 1| ≤ 3 / 4) ∧
    (∀ run : Data.RunIndex, |Source.epsilon run| ≤ 1 / 8000) ∧
    (63 / 2000 : ℚ) < SourceFiniteData.boxRadius / 2 := by
  decide +kernel

theorem knotFraction_mem (segment : Segment) (v : ℝ)
    (inside : v ∈ Icc (knotCoordinate (firstKnot segment) : ℝ) (knotCoordinate (lastKnot segment))) :
    knotFraction segment v ∈ Icc (0 : ℝ) 1 := by
  have ordered : (knotCoordinate (firstKnot segment) : ℝ) < knotCoordinate (lastKnot segment) := by
    exact_mod_cast source_knot_geometry.1 segment
  constructor
  · exact div_nonneg (sub_nonneg.mpr inside.1) (sub_nonneg.mpr ordered.le)
  · exact (div_le_one (sub_pos.mpr ordered)).mpr (by linarith [inside.2])

theorem interpolate_abs_le (values : Data.Knot → ℚ) (bound : ℝ)
    (bounded : ∀ knot, |(values knot : ℝ)| ≤ bound) (segment : Segment) (v : ℝ)
    (inside : v ∈ Icc (knotCoordinate (firstKnot segment) : ℝ) (knotCoordinate (lastKnot segment))) :
    |interpolate values segment v| ≤ bound := by
  have fraction := knotFraction_mem segment v inside
  have one : 0 ≤ 1 - knotFraction segment v := by linarith [fraction.2]
  calc
    |interpolate values segment v| ≤
        |(1 - knotFraction segment v) * (values (firstKnot segment) : ℝ)| +
        |knotFraction segment v * (values (lastKnot segment) : ℝ)| := abs_add_le _ _
    _ = (1 - knotFraction segment v) * |(values (firstKnot segment) : ℝ)| +
        knotFraction segment v * |(values (lastKnot segment) : ℝ)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg one, abs_of_nonneg fraction.1]
    _ ≤ (1 - knotFraction segment v) * bound + knotFraction segment v * bound :=
      add_le_add (mul_le_mul_of_nonneg_left (bounded _) one)
        (mul_le_mul_of_nonneg_left (bounded _) fraction.1)
    _ = bound := by ring

theorem bandWidth_positive (segment : Segment) (epsilon v : ℝ) (positive : 0 < epsilon)
    (inside : v ∈ Icc (knotCoordinate (firstKnot segment) : ℝ) (knotCoordinate (lastKnot segment))) :
    0 < bandWidth segment epsilon v := by
  have fraction := knotFraction_mem segment v inside
  have first : (Source.lower (firstKnot segment) : ℝ) < Source.upper (firstKnot segment) := by
    exact_mod_cast (Incidence.curveBrackets_preserved (firstKnot segment)).1
  have last : (Source.lower (lastKnot segment) : ℝ) < Source.upper (lastKnot segment) := by
    exact_mod_cast (Incidence.curveBrackets_preserved (lastKnot segment)).1
  dsimp [bandWidth, interpolate]
  nlinarith [mul_nonneg (by linarith [fraction.2] : 0 ≤ 1 - knotFraction segment v) (sub_nonneg.mpr first.le),
    mul_nonneg fraction.1 (sub_nonneg.mpr last.le)]

theorem bandWidth_refinement (segment : Segment) (epsilon v : ℝ) :
    bandWidth segment (epsilon / 2) v = bandWidth segment epsilon v - epsilon := by
  simp only [bandWidth]
  ring

theorem bandSeed_contDiff (segment : Segment) (epsilon : ℝ) (order : WithTop ℕ∞) :
    ContDiff ℝ order (bandSeed segment epsilon) := by
  unfold bandSeed bandU bandWidth interpolate knotFraction
  fun_prop

private theorem blend_abs_le (l u alpha bound : ℝ)
    (left : |l| ≤ bound) (right : |u| ≤ bound) (ha : alpha ∈ Icc (0 : ℝ) 1) :
    |(1 - alpha) * l + alpha * u| ≤ bound := by
  have nonneg : 0 ≤ 1 - alpha := by linarith [ha.2]
  calc
    |(1 - alpha) * l + alpha * u| ≤ |(1 - alpha) * l| + |alpha * u| := abs_add_le _ _
    _ = (1 - alpha) * |l| + alpha * |u| := by
      rw [abs_mul, abs_mul, abs_of_nonneg nonneg, abs_of_nonneg ha.1]
    _ ≤ (1 - alpha) * bound + alpha * bound :=
      add_le_add (mul_le_mul_of_nonneg_left left nonneg) (mul_le_mul_of_nonneg_left right ha.1)
    _ = bound := by ring

theorem bandU_source_bound (segment : Segment) (run : Data.RunIndex) (parameters : Point)
    (alpha : parameters 0 ∈ Icc (0 : ℝ) 1)
    (inside : parameters 1 ∈ Icc (knotCoordinate (firstKnot segment) : ℝ) (knotCoordinate (lastKnot segment))) :
    |bandU segment (Source.epsilon run) parameters| ≤ 1 / 4000 := by
  have lowerBound : ∀ knot, |(Source.lower knot : ℝ)| ≤ 1 / 8000 := by
    intro knot
    have h : ((|Source.lower knot| : ℚ) : ℝ) ≤ ((1 / 8000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (source_knot_geometry.2.1 knot).2.1
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have upperBound : ∀ knot, |(Source.upper knot : ℝ)| ≤ 1 / 8000 := by
    intro knot
    have h : ((|Source.upper knot| : ℚ) : ℝ) ≤ ((1 / 8000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (source_knot_geometry.2.1 knot).2.2
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have lo := interpolate_abs_le Source.lower (1 / 8000) lowerBound segment (parameters 1) inside
  have hi := interpolate_abs_le Source.upper (1 / 8000) upperBound segment (parameters 1) inside
  have eps : |(Source.epsilon run : ℝ)| ≤ 1 / 8000 := by
    have h : ((|Source.epsilon run| : ℚ) : ℝ) ≤ ((1 / 8000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (source_knot_geometry.2.2.2.1 run)
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have left : |interpolate Source.lower segment (parameters 1) - (Source.epsilon run : ℝ)| ≤ 1 / 4000 := by
    linarith [abs_sub (interpolate Source.lower segment (parameters 1)) (Source.epsilon run)]
  have right : |interpolate Source.upper segment (parameters 1) + (Source.epsilon run : ℝ)| ≤ 1 / 4000 := by
    linarith [abs_add_le (interpolate Source.upper segment (parameters 1)) (Source.epsilon run)]
  convert blend_abs_le _ _ (parameters 0) (1 / 4000) left right alpha using 1
  congr 1
  dsimp [bandU, bandWidth]
  ring

theorem bandSeed_source_neighbourhood (segment : Segment) (run : Data.RunIndex) (parameters : Point)
    (alpha : parameters 0 ∈ Icc (0 : ℝ) 1)
    (inside : parameters 1 ∈ Icc (knotCoordinate (firstKnot segment) : ℝ) (knotCoordinate (lastKnot segment))) :
    bandSeed segment (Source.epsilon run) parameters ∈
      closedBall centre ((SourceFiniteData.boxRadius : ℝ) / 2) := by
  have ubound := bandU_source_bound segment run parameters alpha inside
  have vbound : |parameters 1| ≤ 1 / 24 := by
    have hlo : |(knotCoordinate (firstKnot segment) : ℝ)| ≤ 1 / 24 := by
      have h : ((|knotCoordinate (firstKnot segment)| : ℚ) : ℝ) ≤ ((1 / 24 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (source_knot_geometry.2.1 (firstKnot segment)).1
      simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
    have hhi : |(knotCoordinate (lastKnot segment) : ℝ)| ≤ 1 / 24 := by
      have h : ((|knotCoordinate (lastKnot segment)| : ℚ) : ℝ) ≤ ((1 / 24 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (source_knot_geometry.2.1 (lastKnot segment)).1
      simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
    exact abs_le.mpr ⟨(abs_le.mp hlo).1.trans inside.1, inside.2.trans (abs_le.mp hhi).2⟩
  rw [mem_closedBall, dist_eq_norm]
  have coordinate (axis : Fin 3) :
      |(bandSeed segment (Source.epsilon run) parameters - centre) axis| ≤ 63 / 2000 := by
    have b0 : |(Source.basis axis 0 : ℝ)| ≤ 1 := by exact_mod_cast (source_knot_geometry.2.2.1 axis).1
    have b1 : |(Source.basis axis 1 : ℝ)| ≤ 3 / 4 := by
      have h : ((|Source.basis axis 1| : ℚ) : ℝ) ≤ ((3 / 4 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (source_knot_geometry.2.2.1 axis).2
      simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] using h
    have h0 := mul_le_mul ubound b0 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4000)
    have h1 := mul_le_mul vbound b1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 24)
    simp only [bandSeed, basisVector, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have expansion (c u v b d : ℝ) : c + u * b + v * d - c = u * b + v * d := by ring
    rw [expansion]
    rw [← abs_mul] at h0 h1
    linarith [abs_add_le (bandU segment (Source.epsilon run) parameters * (Source.basis axis 0 : ℝ))
      (parameters 1 * (Source.basis axis 1 : ℝ))]
  have normBound : ‖bandSeed segment (Source.epsilon run) parameters - centre‖ ≤ (63 : ℝ) / 2000 := by
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun axis => by simpa only [Real.norm_eq_abs] using coordinate axis)
  apply normBound.trans
  have h : ((63 / 2000 : ℚ) : ℝ) ≤ ((SourceFiniteData.boxRadius / 2 : ℚ) : ℝ) :=
    Rat.cast_le.mpr source_knot_geometry.2.2.2.2.le
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousSeed
