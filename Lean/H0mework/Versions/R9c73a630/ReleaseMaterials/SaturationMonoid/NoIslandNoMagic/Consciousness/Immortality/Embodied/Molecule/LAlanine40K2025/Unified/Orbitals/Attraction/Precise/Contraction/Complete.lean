import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.Complete
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.UniformLedger

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators
noncomputable section

def completeErrorBudget : ℝ :=
  ∑ a : Fin 4851,
    |(sourceCoefficientAt a : ℝ)| * Rows.fullAddressError a

theorem complete_attraction_within_budget :
    |totalIntegral - recordedAttractionSum| ≤ completeErrorBudget := by
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
    _ ≤ completeErrorBudget := by
      rw [completeErrorBudget]
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (Rows.full_address_error a) (abs_nonneg _)

theorem complete_attraction_within_independent :
    |totalIntegral - independentElectronNuclear| ≤ (1/10^9 : ℝ) := by
  have row (a : Fin 4851) :
      |aoIntegral (targetLeft a.val) (targetRight a.val) -
        (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤
          (4/10^12 : ℝ) :=
    (Rows.full_address_error a).trans (Rows.full_address_error_le_four a)
  have bound := total_within_independent_of_uniform_budget
    (4/10^12 : ℝ) (by norm_num) row
  convert bound using 1; norm_num

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
