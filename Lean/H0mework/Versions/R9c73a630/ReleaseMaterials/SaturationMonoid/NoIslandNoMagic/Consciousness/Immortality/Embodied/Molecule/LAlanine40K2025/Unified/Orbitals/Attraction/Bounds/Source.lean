import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds.High
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Axis
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceGaussianModel SourceFiniteData GlobalSource
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceSignedEvaluator
noncomputable section

/-- The low branch avoids the large-argument cancellation of the positive
    recurrence; the high branch uses the half-line moment and a small tail. -/
def boysRationalInterval (n : ℕ) (T : ℚ) : Pair :=
  if T ≤ 30 then boysLowInterval n 128 T else boysHighInterval n T

theorem boys_rational_interval_contains (n : ℕ) (T : ℚ) (hT : 0 ≤ T) :
    Holds (boysRationalInterval n T) (boys n (T:ℝ)) := by
  unfold boysRationalInterval
  split_ifs with low
  · exact boys_low_interval_contains n 128 T hT (low.trans (by norm_num))
  · exact boys_high_interval_contains n T (by linarith)

def gaussianGeometryKey (s : Term) : ℚ × (Fin 3 → ℚ) :=
  (s.exponent,s.centre)

theorem boys_argument_same_geometry (s s' t t' : Term) (C : Fin 3 → ℚ)
    (hs : gaussianGeometryKey s = gaussianGeometryKey s')
    (ht : gaussianGeometryKey t = gaussianGeometryKey t') :
    boysArgument s t C = boysArgument s' t' C := by
  have hse := congrArg Prod.fst hs
  have hsc := congrArg Prod.snd hs
  have hte := congrArg Prod.fst ht
  have htc := congrArg Prod.snd ht
  simp only [gaussianGeometryKey] at hse hsc hte htc
  simp only [boysArgument,pairAxisCentre,pairExponent,hse,hsc,hte,htc]

def sourceBoysInterval (n : ℕ) (s t : Term) (a : Fin 13) : Pair :=
  boysRationalInterval n
    (boysArgument s t (Nuclear.nuclearPositionQ a))

theorem source_boys_argument_nonnegative (i j : Basis)
    (s : Term) (hs : s ∈ sourceTerms i)
    (t : Term) (ht : t ∈ sourceTerms j) (a : Fin 13) :
    0 ≤ boysArgument s t (Nuclear.nuclearPositionQ a) := by
  unfold boysArgument
  apply mul_nonneg
  · exact (add_pos (source_exponents_positive i s hs)
      (source_exponents_positive j t ht)).le
  · apply Finset.sum_nonneg
    intro k _
    exact sq_nonneg _

theorem source_boys_interval_contains (i j : Basis)
    (s : Term) (hs : s ∈ sourceTerms i)
    (t : Term) (ht : t ∈ sourceTerms j)
    (a : Fin 13) (n : ℕ) :
    Holds (sourceBoysInterval n s t a)
      (boys n (boysArgument s t (Nuclear.nuclearPositionQ a) : ℝ)) :=
  boys_rational_interval_contains n _
    (source_boys_argument_nonnegative i j s hs t ht a)

theorem source_boys_interval_reuses_geometry (n : ℕ) (s s' t t' : Term)
    (a : Fin 13) (hs : gaussianGeometryKey s = gaussianGeometryKey s')
    (ht : gaussianGeometryKey t = gaussianGeometryKey t') :
    sourceBoysInterval n s t a = sourceBoysInterval n s' t' a := by
  simp only [sourceBoysInterval]
  rw [boys_argument_same_geometry s s' t t' _ hs ht]

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
