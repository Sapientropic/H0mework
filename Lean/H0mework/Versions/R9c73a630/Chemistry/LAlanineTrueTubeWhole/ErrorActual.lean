import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ErrorSupport
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ActualFullFlow

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeError

open SourceGaussianModel TrueTubeSource TrueTubeActual TrueTubeWholeActual TrueTubeError Set
noncomputable section

theorem directional_error (d : Direction) (p : BandPoint) (t : ℝ)
    (time : t ∈ Icc (0 : ℝ) (1 / 2)) :
    dist (signedFinite d p t) (wholeDirectionalFlow d (bandInitial d p) t) ≤
      min (gronwallBound 0 TrueTubeHull.lipschitzConstant wholeDefectBound t) (hullDiameter : ℝ) :=
  le_min (compare_directional_from_local actual_step d p t time)
    (common_hull_distance _ _
      (finite_inside_common p _ (signed_time_inside d t time))
      (directional_inside_common d (bandInitial d p) (actual_step d) t time))

theorem full_error (p : BandPoint) (s : ℝ) (time : s ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    dist (finiteTrajectory (zeroTimeParameters p.val) s) (fullFlow p s) ≤
      min (gronwallBound 0 TrueTubeHull.lipschitzConstant wholeDefectBound |s|) (hullDiameter : ℝ) :=
  full_error_from_local actual_step p s time

theorem two_half_errors (p : BandPoint) (t : ℝ) (time : t ∈ Icc (0 : ℝ) (1 / 2)) :
    dist (finiteTrajectory (zeroTimeParameters p.val) (-t)) (negativeFlow p t) ≤
      min (gronwallBound 0 TrueTubeHull.lipschitzConstant wholeDefectBound t) (hullDiameter : ℝ) ∧
    dist (finiteTrajectory (zeroTimeParameters p.val) t) (positiveFlow p t) ≤
      min (gronwallBound 0 TrueTubeHull.lipschitzConstant wholeDefectBound t) (hullDiameter : ℝ) := by
  constructor
  · simpa only [signedFinite, TrueTubeChecks.directions.1, Rat.cast_neg, Rat.cast_one,
      neg_one_mul, negativeFlow] using directional_error 0 p t time
  · simpa only [signedFinite, TrueTubeChecks.directions.2, Rat.cast_one, one_mul, positiveFlow] using
      directional_error 1 p t time

theorem zero_error (p : BandPoint) :
    dist (finiteTrajectory (zeroTimeParameters p.val) 0) (fullFlow p 0) = 0 := by
  rw [finiteTrajectory_same_initial, fullFlow_starts, dist_self]

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeError
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
