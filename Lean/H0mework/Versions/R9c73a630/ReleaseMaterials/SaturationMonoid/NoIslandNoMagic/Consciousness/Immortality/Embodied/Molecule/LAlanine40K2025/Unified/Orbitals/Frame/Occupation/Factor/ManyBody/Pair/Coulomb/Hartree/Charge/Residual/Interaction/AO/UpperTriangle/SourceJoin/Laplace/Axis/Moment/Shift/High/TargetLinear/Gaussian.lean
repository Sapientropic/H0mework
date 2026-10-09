import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Polynomial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
open MeasureTheory
noncomputable section

theorem gaussian_fifth_zero (b : ℝ) :
    (∫ x : ℝ, x^5 * Real.exp (-b*x^2)) = 0 := by
  let f : ℝ → ℝ := fun x => x^5 * Real.exp (-b*x^2)
  have h := Measure.integral_comp_mul_left f (-1 : ℝ)
  have hsame : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := by
    simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using h
  have hodd : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    dsimp [f]
    have hs : (-x)^2 = x^2 := by ring
    rw [hs]
    ring
  simp_rw [hodd,integral_neg] at hsame
  change -(∫ x : ℝ, x^5 * Real.exp (-b*x^2)) = _ at hsame
  linarith

def rawMoment5 (n : ℕ) (b : ℝ) : ℝ :=
  if n < 5 then High.rawMoment n b else 0

theorem raw_moment_five (n : ℕ) (b : ℝ)
    (hn : n < 6) (hb : 0 < b) :
    (∫ x : ℝ, x^n * Real.exp (-b*x^2)) = rawMoment5 n b := by
  by_cases h : n < 5
  · simp only [rawMoment5, if_pos h]
    exact High.raw_moment_integral n b h hb
  · have hn5 : n = 5 := by omega
    subst n
    simp only [rawMoment5, show ¬ 5 < 5 by omega, ↓reduceIte]
    exact gaussian_fifth_zero b

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetLinear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
