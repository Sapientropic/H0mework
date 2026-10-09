import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.Weighted

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators
noncomputable section

theorem total_within_recorded_of_uniform_budget (ε : ℝ) (nonnegative : 0 ≤ ε)
    (row : ∀ a : Fin 4851,
      |aoIntegral (targetLeft a.val) (targetRight a.val) -
        (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤ ε) :
    |totalIntegral - recordedAttractionSum| ≤ 200 * ε := by
  rw [totalIntegral,precise_pair_expansion,precise_target_row_sum,
    recordedAttractionSum,← Finset.sum_sub_distrib]
  calc
    _ = |∑ a : Fin 4851, (sourceCoefficientAt a : ℝ) *
        (aoIntegral (targetLeft a.val) (targetRight a.val) -
          (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ))| := by
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ) *
        (aoIntegral (targetLeft a.val) (targetRight a.val) -
          (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ)| *
        |aoIntegral (targetLeft a.val) (targetRight a.val) -
          (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul]
    _ ≤ ∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ)| * ε := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (row a) (abs_nonneg _)
    _ = (Kinetic.kineticRowWeight : ℝ) * ε := by
      rw [← Finset.sum_mul]
      unfold Kinetic.kineticRowWeight
      rw [Rat.cast_sum]
      simp only [Kinetic.weightTermFin,Rat.cast_abs]
    _ ≤ 200 * ε := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Kinetic.kinetic_row_weight_bound) nonnegative

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
