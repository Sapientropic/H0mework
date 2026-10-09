import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.MixedPaid
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.Weighted

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators
noncomputable section

def mixedActualAttraction : ℝ :=
  ∑ a ∈ Rows.mixedPaidAddresses,
    (sourceCoefficientAt a : ℝ) * aoIntegral (targetLeft a.val) (targetRight a.val)

def mixedRecordedAttraction : ℝ :=
  ∑ a ∈ Rows.mixedPaidAddresses,
    (sourceCoefficientAt a : ℝ) *
      (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)

def mixedErrorBudget : ℝ :=
  ∑ a ∈ Rows.mixedPaidAddresses,
    |(sourceCoefficientAt a : ℝ)| * (Rows.mixedErrorQ a : ℝ)

theorem mixed_attraction_within_budget :
    |mixedActualAttraction - mixedRecordedAttraction| ≤ mixedErrorBudget := by
  rw [mixedActualAttraction,mixedRecordedAttraction,← Finset.sum_sub_distrib]
  calc
    _ = |∑ a ∈ Rows.mixedPaidAddresses,
        (sourceCoefficientAt a : ℝ) *
          (aoIntegral (targetLeft a.val) (targetRight a.val) -
            (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ))| := by
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ a ∈ Rows.mixedPaidAddresses,
        |(sourceCoefficientAt a : ℝ) *
          (aoIntegral (targetLeft a.val) (targetRight a.val) -
            (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ Rows.mixedPaidAddresses,
        |(sourceCoefficientAt a : ℝ)| *
          |aoIntegral (targetLeft a.val) (targetRight a.val) -
            (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul]
    _ ≤ mixedErrorBudget := by
      rw [mixedErrorBudget]
      apply Finset.sum_le_sum
      intro a membership
      exact mul_le_mul_of_nonneg_left
        (Rows.mixed_paid_address_error a membership) (abs_nonneg _)

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
