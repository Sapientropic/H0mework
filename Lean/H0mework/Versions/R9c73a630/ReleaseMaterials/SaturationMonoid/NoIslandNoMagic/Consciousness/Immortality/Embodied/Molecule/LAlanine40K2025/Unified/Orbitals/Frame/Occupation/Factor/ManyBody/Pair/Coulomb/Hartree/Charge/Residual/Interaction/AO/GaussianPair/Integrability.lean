import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement SourceGaussianModel ContinuousGradient GlobalSource SourceCoulomb MeasureTheory
noncomputable section

def pairBound (left right : Term) : ℝ :=
  (termBound left zeroJet : ℝ) * (termBound right zeroJet : ℝ)

theorem pair_shape_bound (left right : Term)
    (leftPositive : 0 < left.exponent) (rightPositive : 0 < right.exponent)
    (x : Point) :
    ‖pairShape left right x‖ ≤ pairBound left right := by
  have positive : (left.exponent : ℝ) + (right.exponent : ℝ) ≠ 0 :=
    ne_of_gt (add_pos (by exact_mod_cast leftPositive) (by exact_mod_cast rightPositive))
  rw [← value_pair left right x positive, norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  exact mul_le_mul (term_uniform_bound left leftPositive zeroJet x)
    (term_uniform_bound right rightPositive zeroJet x)
    (abs_nonneg _) (by positivity)

theorem pair_shape_integrable (left right : Term)
    (leftPositive : 0 < left.exponent) (rightPositive : 0 < right.exponent) :
    Integrable (pairShape left right) := by
  have bounded (x : Point) : ‖value right zeroJet x‖ ≤ (termBound right zeroJet : ℝ) := by
    simpa only [Real.norm_eq_abs] using term_uniform_bound right rightPositive zeroJet x
  have swapped : Integrable (fun x : Point =>
      value right zeroJet x * value left zeroJet x) :=
    (term_integrable left leftPositive zeroJet).bdd_mul
      (value_contDiff right zeroJet 0).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall bounded)
  have original : Integrable (fun x : Point =>
      value left zeroJet x * value right zeroJet x) := by
    convert swapped using 1
    funext x
    exact mul_comm _ _
  have positive : (left.exponent : ℝ) + (right.exponent : ℝ) ≠ 0 :=
    ne_of_gt (add_pos (by exact_mod_cast leftPositive) (by exact_mod_cast rightPositive))
  convert original using 1
  funext x
  exact (value_pair left right x positive).symm

theorem pair_kernel_integrable (left right nextLeft nextRight : Term)
    (leftPositive : 0 < left.exponent) (rightPositive : 0 < right.exponent)
    (nextLeftPositive : 0 < nextLeft.exponent) (nextRightPositive : 0 < nextRight.exponent) :
    Integrable (fun z : Point × Point =>
      pairShape left right z.1 * pairShape nextLeft nextRight z.2 * kernel (z.2 - z.1)) :=
  SourceCoulomb.pair_integrable _ _
    (pair_shape_integrable left right leftPositive rightPositive)
    (pair_shape_integrable nextLeft nextRight nextLeftPositive nextRightPositive)
    (pairBound nextLeft nextRight)
    (pair_shape_bound nextLeft nextRight nextLeftPositive nextRightPositive)

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
