import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Integrals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Metric
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient MeasureTheory
open scoped BigOperators
noncomputable section

/-- The entire original spatial density has one charge contraction, with no basin coverage premise. -/
theorem actual_charge_overlap : (∫ x : Point, sourceDensity x) =
    ∑ b : Basis, ∑ c : Basis, (densityMatrix b c : ℝ)*overlap b c := by
  have each (b c : Basis) : Integrable (fun x =>
      (densityMatrix b c : ℝ) * (ao b x * ao c x)) :=
    (source_product_integrable b c zeroJet zeroJet).const_mul _
  simp only [sourceDensity,SourceGaussianModel.density,bilinear]
  simp_rw [mul_assoc]
  change (∫ x : Point, ∑ b : Basis, ∑ c : Basis, (densityMatrix b c : ℝ)*(ao b x*ao c x)) = _
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => each b c))]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_finsetSum _ (fun c _ => each b c)]
  simp only [integral_const_mul,overlap,ao]

theorem actual_charge_error (S : Basis → Basis → ℚ) (error : ℝ)
    (bounded : ∀ b c, |overlap b c-(S b c : ℝ)| ≤ error) :
    |(∫ x : Point, sourceDensity x)-(∑ b : Basis, ∑ c : Basis, densityMatrix b c*S b c : ℚ)| ≤
      error*(∑ b : Basis, ∑ c : Basis, |densityMatrix b c| : ℚ) := by
  rw [actual_charge_overlap]
  simp only [Rat.cast_sum,Rat.cast_mul,Rat.cast_abs]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib,← mul_sub]
  calc
    _ ≤ ∑ b : Basis, ∑ c : Basis, |(densityMatrix b c : ℝ)*(overlap b c-(S b c : ℝ))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ b : Basis, ∑ c : Basis, |(densityMatrix b c : ℝ)| * error := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro c _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (bounded b c) (abs_nonneg _)
    _ = _ := by simp only [Finset.sum_mul,mul_comm error]

end
end LAlanine40K2025.UnifiedOrbitals.Metric
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
