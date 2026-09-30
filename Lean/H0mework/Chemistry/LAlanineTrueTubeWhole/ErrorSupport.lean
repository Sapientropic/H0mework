import H0mework.Chemistry.LAlanineTrueTubeWhole.ErrorComparison
import H0mework.Chemistry.LAlanineTrueTubeWhole.ActualFullConsumer
import H0mework.Chemistry.LAlanineTrueTubeHull.Consumers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeError

open SourceGaussianModel SourceSignedEvaluator ContinuousGradient ContinuousParameterMap
open TrueTubeSource TrueTubeTrace TrueTubeActual TrueTubeWholeActual TrueTubeContinuation
open TrueTubeWholeChecks TrueTubeError WholeCellPartition Set
noncomputable section

attribute [local irreducible] parameterMap parameterJacobian sourceGradient windowCurve

def comparisonRegion : Set Point :=
  Icc (lowerPoint TrueTubeHullSource.box) (upperPoint TrueTubeHullSource.box)

def hullWidth (i : Fin 3) : ℚ := (TrueTubeHullSource.box i).2 - (TrueTubeHullSource.box i).1
def hullDiameter : ℚ := max (hullWidth 0) (max (hullWidth 1) (hullWidth 2))

theorem hullDiameter_nonnegative : 0 ≤ hullDiameter := by decide +kernel

theorem hullWidth_le (i : Fin 3) : hullWidth i ≤ hullDiameter := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem common_hull_distance (x y : Point) (hx : x ∈ comparisonRegion) (hy : y ∈ comparisonRegion) :
    dist x y ≤ (hullDiameter : ℝ) := by
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr hullDiameter_nonnegative)).mpr
  intro i
  have widthBound : ((TrueTubeHullSource.box i).2 : ℝ) - ((TrueTubeHullSource.box i).1 : ℝ) ≤
      (hullDiameter : ℝ) := by
    have widthQ := hullWidth_le i
    unfold hullWidth at widthQ
    exact_mod_cast widthQ
  have xlo := hx.1 i
  have xhi := hx.2 i
  have ylo := hy.1 i
  have yhi := hy.2 i
  change ((TrueTubeHullSource.box i).1 : ℝ) ≤ x i at xlo
  change x i ≤ ((TrueTubeHullSource.box i).2 : ℝ) at xhi
  change ((TrueTubeHullSource.box i).1 : ℝ) ≤ y i at ylo
  change y i ≤ ((TrueTubeHullSource.box i).2 : ℝ) at yhi
  rw [Real.norm_eq_abs, Pi.sub_apply]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem finite_inside_common (p : BandPoint) (s : ℝ) (time : s ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    finiteTrajectory (zeroTimeParameters p.val) s ∈ comparisonRegion := by
  have inside := zero_line_mem_full p s time
  have unionInside : parameterLine (zeroTimeParameters p.val) s ∈ ⋃ q, quarterDomain q := by
    rwa [← fullDomain_eq_iUnion_quarters]
  obtain ⟨q, hq⟩ := mem_iUnion.mp unionInside
  exact (inRectangle_iff _ _).mp (TrueTubeHullSource.whole_contains (WholeCellReplay.finalField q) _
    (WholeCellReplay.generated_target_in_final_field WholeCellMatrix.all_actual_fields q _ hq))

theorem directional_inside_common (d : Direction) (initial : InitialAt d)
    (localLaws : ∀ i, LocalStepLaw d i) (t : ℝ) (time : t ∈ Icc (0 : ℝ) (1 / 2)) :
    wholeDirectionalFlow d initial t ∈ comparisonRegion := by
  obtain ⟨i, hi⟩ := sixteen_intervals_cover t time
  have localTime : t - stepOffset i ∈ Icc 0 (stepSize : ℝ) := by
    constructor <;> linarith [hi.1, hi.2]
  have bounded := window_all_tubes d initial.val initial.property localLaws i (t - stepOffset i) localTime
  rw [sub_add_cancel] at bounded
  exact (inRectangle_iff _ _).mp (TrueTubeHull.actual_tube_contains d i _ bounded)

theorem compare_directional_from_local (localLaws : ∀ d i, LocalStepLaw d i)
    (d : Direction) (p : BandPoint) :
    ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      dist (signedFinite d p t) (wholeDirectionalFlow d (bandInitial d p) t) ≤
        gronwallBound 0 TrueTubeHull.lipschitzConstant wholeDefectBound t := by
  have unit : |(sign d : ℝ)| = 1 := by exact_mod_cast (TrueTubeChecks.direction_units d).1
  exact compare_signed d p comparisonRegion TrueTubeHull.lipschitzConstant
    (TrueTubeHull.common_signed_lipschitz (sign d) unit)
    (fun t ht => finite_inside_common p _ (signed_time_inside d t (Ico_subset_Icc_self ht)))
    (wholeDirectionalFlow d (bandInitial d p))
    (window_is_original_flow d (bandInitial d p).val (bandInitial d p).property (localLaws d))
    (fun t ht => directional_inside_common d (bandInitial d p) (localLaws d) t (Ico_subset_Icc_self ht))
    (wholeDirectionalFlow_starts d (bandInitial d p))

theorem compare_full_from_local (localLaws : ∀ d i, LocalStepLaw d i)
    (p : BandPoint) (s : ℝ) (time : s ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    dist (finiteTrajectory (zeroTimeParameters p.val) s) (fullFlow p s) ≤
      gronwallBound 0 TrueTubeHull.lipschitzConstant wholeDefectBound |s| := by
  by_cases hs : s ≤ 0
  · have negativeTime : -s ∈ Icc (0 : ℝ) (1 / 2) := ⟨neg_nonneg.mpr hs, by linarith [time.1]⟩
    have compared := compare_directional_from_local localLaws 0 p (-s) negativeTime
    rw [fullFlow, LAlanineTrueTube.Signed.full_left _ _ _ hs, abs_of_nonpos hs]
    simpa only [signedFinite, TrueTubeChecks.directions.1, Rat.cast_neg, Rat.cast_one,
      neg_one_mul, neg_neg, negativeFlow] using compared
  · have positiveTime : s ∈ Icc (0 : ℝ) (1 / 2) := ⟨(not_le.mp hs).le, time.2⟩
    have compared := compare_directional_from_local localLaws 1 p s positiveTime
    rw [fullFlow, LAlanineTrueTube.Signed.full_right (directions_same_initial p) _ positiveTime.1,
      abs_of_nonneg positiveTime.1]
    simpa only [signedFinite, TrueTubeChecks.directions.2, Rat.cast_one, one_mul, positiveFlow] using compared

theorem full_inside_common_from_local (localLaws : ∀ d i, LocalStepLaw d i)
    (p : BandPoint) (s : ℝ) (time : s ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    fullFlow p s ∈ comparisonRegion :=
  LAlanineTrueTube.Signed.full_mem
    (fun t ht => directional_inside_common 0 (bandInitial 0 p) (localLaws 0) t ht)
    (fun t ht => directional_inside_common 1 (bandInitial 1 p) (localLaws 1) t ht) time

theorem full_error_from_local (localLaws : ∀ d i, LocalStepLaw d i)
    (p : BandPoint) (s : ℝ) (time : s ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    dist (finiteTrajectory (zeroTimeParameters p.val) s) (fullFlow p s) ≤
      min (gronwallBound 0 TrueTubeHull.lipschitzConstant wholeDefectBound |s|) (hullDiameter : ℝ) :=
  le_min (compare_full_from_local localLaws p s time)
    (common_hull_distance _ _ (finite_inside_common p s time) (full_inside_common_from_local localLaws p s time))

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeError
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
