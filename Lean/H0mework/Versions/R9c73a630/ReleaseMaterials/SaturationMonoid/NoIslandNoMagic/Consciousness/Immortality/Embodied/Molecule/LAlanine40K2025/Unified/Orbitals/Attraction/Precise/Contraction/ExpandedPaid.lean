import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.ExpandedPaid
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.Weighted

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators
noncomputable section

def expandedPaidActualAttraction : ℝ :=
  ∑ a ∈ Rows.expandedPaidAddresses,
    (sourceCoefficientAt a : ℝ) * aoIntegral (targetLeft a.val) (targetRight a.val)

def expandedPaidRecordedAttraction : ℝ :=
  ∑ a ∈ Rows.expandedPaidAddresses,
    (sourceCoefficientAt a : ℝ) *
      (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)

theorem expanded_paid_attraction_within_report :
    |expandedPaidActualAttraction - expandedPaidRecordedAttraction| ≤ (200/10^12 : ℝ) := by
  rw [expandedPaidActualAttraction,expandedPaidRecordedAttraction,← Finset.sum_sub_distrib]
  have estimate :
      |∑ a ∈ Rows.expandedPaidAddresses,
        ((sourceCoefficientAt a : ℝ) * aoIntegral (targetLeft a.val) (targetRight a.val) -
          (sourceCoefficientAt a : ℝ) *
            (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ))| ≤
        (∑ a ∈ Rows.expandedPaidAddresses, |(sourceCoefficientAt a : ℝ)|) / 10^12 := by
    calc
      _ = |∑ a ∈ Rows.expandedPaidAddresses,
          (sourceCoefficientAt a : ℝ) *
            (aoIntegral (targetLeft a.val) (targetRight a.val) -
              (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ))| := by
        apply congrArg abs
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ ∑ a ∈ Rows.expandedPaidAddresses,
          |(sourceCoefficientAt a : ℝ) *
            (aoIntegral (targetLeft a.val) (targetRight a.val) -
              (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a ∈ Rows.expandedPaidAddresses,
          |(sourceCoefficientAt a : ℝ)| *
            |aoIntegral (targetLeft a.val) (targetRight a.val) -
              (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| := by
        apply Finset.sum_congr rfl
        intro a _
        rw [abs_mul]
      _ ≤ ∑ a ∈ Rows.expandedPaidAddresses,
          |(sourceCoefficientAt a : ℝ)| * (1/10^12 : ℝ) := by
        apply Finset.sum_le_sum
        intro a membership
        exact mul_le_mul_of_nonneg_left
          (Rows.expanded_paid_address_error a membership) (abs_nonneg _)
      _ = (∑ a ∈ Rows.expandedPaidAddresses, |(sourceCoefficientAt a : ℝ)|) / 10^12 := by
        rw [← Finset.sum_mul]
        ring
  have subset :
      (∑ a ∈ Rows.expandedPaidAddresses, |(sourceCoefficientAt a : ℝ)|) ≤
        ∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ)| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro a _ _
    exact abs_nonneg _
  have weight :
      (∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ)|) ≤ 200 := by
    have h : (Kinetic.kineticRowWeight : ℝ) ≤ 200 := by
      exact_mod_cast Kinetic.kinetic_row_weight_bound
    convert h using 1
    unfold Kinetic.kineticRowWeight
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Kinetic.weightTermFin,Rat.cast_abs]
  nlinarith

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
