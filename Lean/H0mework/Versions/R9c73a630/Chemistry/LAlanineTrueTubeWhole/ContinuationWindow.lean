import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ContinuationUniqueness

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeContinuation

open SourceGaussianModel TrueTubeSource TrueTubeTrace ContinuousGradient Set
noncomputable section

/-- A proof-side common curve. Its original-field interpretation is paid by the actual step chain. -/
def windowCurve (d : Direction) (initial : Point) : ℝ → Point :=
  Classical.choose (exists_global_window d initial)

theorem windowCurve_starts (d : Direction) (initial : Point) : windowCurve d initial 0 = initial :=
  (Classical.choose_spec (exists_global_window d initial)).1

theorem windowCurve_extended (d : Direction) (initial : Point) :
    IsIntegralCurveOn (windowCurve d initial) (fun _ => globalField d) (Icc (0 : ℝ) (1 / 2)) :=
  (Classical.choose_spec (exists_global_window d initial)).2

theorem windowCurve_continuous (d : Direction) (initial : Point) :
    ContinuousOn (windowCurve d initial) (Icc (0 : ℝ) (1 / 2)) :=
  (windowCurve_extended d initial).continuousOn

theorem windowCurve_local_identification (d : Direction) (initial : Point) (localCurve : ℝ → Point)
    (offset length : ℝ) (offset_nonneg : 0 ≤ offset) (end_inside : offset + length ≤ 1 / 2)
    (localODE : IsIntegralCurveOn localCurve (fun _ => signedGradient (sign d)) (Icc 0 length))
    (localInside : ∀ t ∈ Icc 0 length, localCurve t ∈ sourceCube)
    (starts : localCurve 0 = windowCurve d initial offset) :
    EqOn localCurve (fun t => windowCurve d initial (t + offset)) (Icc 0 length) :=
  local_source_matches_window d (windowCurve d initial) localCurve (windowCurve_extended d initial)
    offset length offset_nonneg end_inside localODE localInside starts

theorem windowCurve_original_at (d : Direction) (initial : Point) (t : ℝ)
    (time : t ∈ Icc (0 : ℝ) (1 / 2)) (inside : windowCurve d initial t ∈ sourceCube) :
    HasDerivWithinAt (windowCurve d initial) (signedGradient (sign d) (windowCurve d initial t))
      (Icc (0 : ℝ) (1 / 2)) t := by
  have derivative := windowCurve_extended d initial t time
  change HasDerivWithinAt (windowCurve d initial) (globalField d (windowCurve d initial t)) _ t at derivative
  rwa [globalField_eq_original d _ inside] at derivative

end
end LAlanine40K2025.BasinRefinement.TrueTubeContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
