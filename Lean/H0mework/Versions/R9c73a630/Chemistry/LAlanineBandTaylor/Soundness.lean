import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandTaylor.Intervals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor

open SourceGaussianModel SourceSignedEvaluator Set
noncomputable section

/-- Independently bounded source derivatives produce the interval; no reported field is assumed. -/
theorem enclosure_contains (n : Fin 3) (m : MultiIndex) (c v : Point)
    (A : MultiIndex → Pair) (B : MultiIndex → ℚ) (d : Fin 3 → Pair) (r : Fin 3 → ℚ)
    (center : ∀ k ≤ n.val, ∀ a ∈ increments k,
      Holds (A (shift m a)) (densityJet (shift m a) c))
    (hull : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a ∈ increments (n.val+1),
      |densityJet (shift m a) (segment c v t)| ≤ (B (shift m a) : ℝ))
    (delta : ∀ i, Holds (d i) (v i)) (radius : ∀ i, |v i| ≤ (r i : ℝ)) :
    Holds (enclosure n.val A B m d r) (densityJet m (c+v)) := by
  have hp := polynomialPair_holds n A (fun j => densityJet j c) m d v center delta
  have he := remainderPair_holds n B m r
  have hr := densityJet_remainder n m c v (fun i => (r i : ℝ))
    (fun j => (B j : ℝ)) radius hull
  have lower := (abs_le.mp (hr.trans he.2)).1
  have upper := (abs_le.mp (hr.trans he.2)).2
  constructor
  · change (((polynomialPair n.val A m d).1 - (remainderPair n.val B m r).2 : ℚ) : ℝ) ≤ _
    simp only [Rat.cast_sub]
    linarith [hp.1]
  · change _ ≤ (((polynomialPair n.val A m d).2 + (remainderPair n.val B m r).2 : ℚ) : ℝ)
    simp only [Rat.cast_add]
    linarith [hp.2]

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Taylor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
