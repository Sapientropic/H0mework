import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ContinuationExtension
import Mathlib.Analysis.ODE.Transform

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeContinuation

open SourceGaussianModel TrueTubeSource TrueTubeTrace ContinuousGradient Set
open scoped Pointwise
noncomputable section

theorem original_curve_is_extended (d : Direction) (curve : ℝ → Point) (a b : ℝ)
    (evolves : IsIntegralCurveOn curve (fun _ => signedGradient (sign d)) (Icc a b))
    (inside : ∀ t ∈ Icc a b, curve t ∈ sourceCube) :
    IsIntegralCurveOn curve (fun _ => globalField d) (Icc a b) := by
  intro t ht
  change HasDerivWithinAt curve (globalField d (curve t)) (Icc a b) t
  rw [globalField_eq_original d _ (inside t ht)]
  exact evolves t ht

theorem same_extended_curve (d : Direction) (a b : ℝ) (left right : ℝ → Point)
    (leftODE : IsIntegralCurveOn left (fun _ => globalField d) (Icc a b))
    (rightODE : IsIntegralCurveOn right (fun _ => globalField d) (Icc a b))
    (starts : left a = right a) : EqOn left right (Icc a b) := by
  apply ODE_solution_unique (fun _ => globalField_lipschitz d)
    leftODE.continuousOn _ rightODE.continuousOn _ starts
  · intro t ht
    exact (leftODE t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact (rightODE t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

theorem window_shift (d : Direction) (curve : ℝ → Point)
    (evolves : IsIntegralCurveOn curve (fun _ => globalField d) (Icc (0 : ℝ) (1 / 2)))
    (offset length : ℝ) (offset_nonneg : 0 ≤ offset) (end_inside : offset + length ≤ 1 / 2) :
    IsIntegralCurveOn (fun t => curve (t + offset)) (fun _ => globalField d) (Icc 0 length) := by
  have shifted := evolves.comp_add offset
  apply shifted.mono
  intro t ht
  rw [mem_vadd_set_iff_neg_vadd_mem]
  change 0 ≤ -(-offset) + t ∧ -(-offset) + t ≤ 1 / 2
  constructor <;> linarith [ht.1, ht.2]

theorem local_source_matches_window (d : Direction) (curve localCurve : ℝ → Point)
    (evolves : IsIntegralCurveOn curve (fun _ => globalField d) (Icc (0 : ℝ) (1 / 2)))
    (offset length : ℝ) (offset_nonneg : 0 ≤ offset) (end_inside : offset + length ≤ 1 / 2)
    (localODE : IsIntegralCurveOn localCurve (fun _ => signedGradient (sign d)) (Icc 0 length))
    (localInside : ∀ t ∈ Icc 0 length, localCurve t ∈ sourceCube)
    (starts : localCurve 0 = curve offset) :
    EqOn localCurve (fun t => curve (t + offset)) (Icc 0 length) := by
  apply same_extended_curve d 0 length localCurve (fun t => curve (t + offset))
    (original_curve_is_extended d localCurve 0 length localODE localInside)
    (window_shift d curve evolves offset length offset_nonneg end_inside)
  simpa only [zero_add] using starts

end
end LAlanine40K2025.BasinRefinement.TrueTubeContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
