import H0mework.Chemistry.LAlanineBandGeometry.Interpolation
import H0mework.Chemistry.LAlanineTrueFlowGeometry.SeedAlgebra

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGeometry

open SourceGaussianModel ContinuousSeed TrueFlowGeometry Set
noncomputable section

theorem source_epsilon_positive : (0 : ℝ) < (Geometry.Source.epsilon 0 : ℝ) := by
  exact_mod_cast (show 0 < Geometry.Source.epsilon 0 from by decide +kernel)

/-- Source chart labels may coincide at seams; the independent alpha/v coordinates cannot collapse. -/
theorem seed_coordinates_of_eq (s t : Segment) (p q : Point)
    (hp : p 1 ∈ Icc (knotCoordinate (firstKnot s) : ℝ) (knotCoordinate (lastKnot s)))
    (hq : q 1 ∈ Icc (knotCoordinate (firstKnot t) : ℝ) (knotCoordinate (lastKnot t)))
    (same : bandSeed s (Geometry.Source.epsilon 0) p = bandSeed t (Geometry.Source.epsilon 0) q) :
    p 0 = q 0 ∧ p 1 = q 1 := by
  have difference :
      (bandU s (Geometry.Source.epsilon 0) p - bandU t (Geometry.Source.epsilon 0) q) •
          basisVector 0 + (p 1 - q 1) • basisVector 1 = 0 := by
    have expansion :
        (bandU s (Geometry.Source.epsilon 0) p - bandU t (Geometry.Source.epsilon 0) q) •
            basisVector 0 + (p 1 - q 1) • basisVector 1 =
          bandSeed s (Geometry.Source.epsilon 0) p - bandSeed t (Geometry.Source.epsilon 0) q := by
      ext i
      simp only [bandSeed, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [same, sub_self] at expansion
    exact expansion
  have coefficients := seed_basis_coefficients _ _ difference
  have hv : p 1 = q 1 := sub_eq_zero.mp coefficients.2
  have hq' : p 1 ∈ Icc (knotCoordinate (firstKnot t) : ℝ) (knotCoordinate (lastKnot t)) := hv ▸ hq
  have lower := interpolate_overlap Geometry.Source.lower s t (p 1) hp hq'
  have upper := interpolate_overlap Geometry.Source.upper s t (p 1) hp hq'
  have hwidth : 0 < bandWidth s (Geometry.Source.epsilon 0) (p 1) :=
    bandWidth_positive s _ _ source_epsilon_positive hp
  have product : (p 0 - q 0) * bandWidth s (Geometry.Source.epsilon 0) (p 1) = 0 := by
    have hu := coefficients.1
    simp only [bandU, bandWidth, ← hv, ← lower, ← upper] at hu ⊢
    linear_combination hu
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right hwidth.ne'), hv⟩

theorem seed_eq_of_coordinates (s t : Segment) (p q : Point)
    (hp : p 1 ∈ Icc (knotCoordinate (firstKnot s) : ℝ) (knotCoordinate (lastKnot s)))
    (hq : q 1 ∈ Icc (knotCoordinate (firstKnot t) : ℝ) (knotCoordinate (lastKnot t)))
    (coordinates : p 0 = q 0 ∧ p 1 = q 1) :
    bandSeed s (Geometry.Source.epsilon 0) p = bandSeed t (Geometry.Source.epsilon 0) q := by
  have hq' : p 1 ∈ Icc (knotCoordinate (firstKnot t) : ℝ) (knotCoordinate (lastKnot t)) := coordinates.2 ▸ hq
  have lower := interpolate_overlap Geometry.Source.lower s t (p 1) hp hq'
  have upper := interpolate_overlap Geometry.Source.upper s t (p 1) hp hq'
  simp only [bandSeed, bandU, bandWidth, ← coordinates.1, ← coordinates.2, ← lower, ← upper]

theorem seed_eq_iff_coordinates (s t : Segment) (p q : Point)
    (hp : p 1 ∈ Icc (knotCoordinate (firstKnot s) : ℝ) (knotCoordinate (lastKnot s)))
    (hq : q 1 ∈ Icc (knotCoordinate (firstKnot t) : ℝ) (knotCoordinate (lastKnot t))) :
    bandSeed s (Geometry.Source.epsilon 0) p = bandSeed t (Geometry.Source.epsilon 0) q ↔
      p 0 = q 0 ∧ p 1 = q 1 :=
  ⟨seed_coordinates_of_eq s t p q hp hq, seed_eq_of_coordinates s t p q hp hq⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
