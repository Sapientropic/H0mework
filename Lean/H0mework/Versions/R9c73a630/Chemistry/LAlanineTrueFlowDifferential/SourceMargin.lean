import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeHull.Consumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open SourceGaussianModel SourceFiniteData SourceFiniteChecks SourceJetIncidence
open SourceSignedEvaluator ContinuousGradient TrueTubeHullSource
open Set Metric
noncomputable section

theorem source_margin : ∀ i : Fin 3,
    boxCentre i - boxRadius + 1 / 100 < (box i).1 ∧
      (box i).2 < boxCentre i + boxRadius - 1 / 100 := by decide +kernel

theorem source_margin_real (i : Fin 3) :
    sourceCentre i - sourceRadius + 1 / 100 < ((box i).1 : ℝ) ∧
      ((box i).2 : ℝ) < sourceCentre i + sourceRadius - 1 / 100 := by
  dsimp only [sourceCentre, sourceRadius]
  constructor
  · simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt.mpr (source_margin i).1 : ((boxCentre i - boxRadius + 1 / 100 : ℚ) : ℝ) < ((box i).1 : ℝ))
  · simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt.mpr (source_margin i).2 : ((box i).2 : ℝ) < ((boxCentre i + boxRadius - 1 / 100 : ℚ) : ℝ))

theorem nearby_hull_inside_cube (x y : Point) (inside : InRectangle box x)
    (nearby : dist y x < (1 / 100 : ℝ)) : y ∈ sourceCube := by
  change ∀ i, |y i - sourceCentre i| ≤ sourceRadius
  intro i
  have delta : |y i - x i| < (1 / 100 : ℝ) := by
    have pointwise := norm_le_pi_norm (y - x) i
    rw [dist_eq_norm] at nearby
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using pointwise.trans_lt nearby
  have lo := (source_margin_real i).1
  have hi := (source_margin_real i).2
  have row := inside i
  have displacement := abs_lt.mp delta
  apply abs_le.mpr
  constructor <;> linarith [row.1, row.2, displacement.1, displacement.2]

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
