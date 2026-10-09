import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.Target
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Total

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators
noncomputable section

def recordedAttractionSum : ℝ :=
  ∑ a : Fin 4851, (sourceCoefficientAt a : ℝ) *
    (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)

/-- This is a consumer of the complete upper-triangle certificate, not a
    premise for generating any AO field or individual row. -/
theorem total_within_recorded_of_upper
    (row : ∀ a : Fin 4851,
      |aoIntegral (targetLeft a.val) (targetRight a.val) -
        (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤
          (1/10^12 : ℝ)) :
    |totalIntegral - recordedAttractionSum| ≤ (200/10^12 : ℝ) := by
  rw [totalIntegral,precise_pair_expansion,precise_target_row_sum,
    recordedAttractionSum,← Finset.sum_sub_distrib]
  have estimate :
      |∑ a : Fin 4851,
        ((sourceCoefficientAt a : ℝ) *
          aoIntegral (targetLeft a.val) (targetRight a.val) -
          (sourceCoefficientAt a : ℝ) *
            (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ))| ≤
        (Kinetic.kineticRowWeight : ℝ) / 10^12 := by
    calc
      _ = |∑ a : Fin 4851, (sourceCoefficientAt a : ℝ) *
          (aoIntegral (targetLeft a.val) (targetRight a.val) -
            (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ))| := by
        apply congrArg abs
        apply Finset.sum_congr rfl
        intro a _
        rw [← mul_sub]
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
      _ ≤ ∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ)| *
          (1/10^12 : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (row a) (abs_nonneg _)
      _ = (∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ)|) *
          (1/10^12 : ℝ) := (Finset.sum_mul _ _ _).symm
      _ = (Kinetic.kineticRowWeight : ℝ) / 10^12 := by
        unfold Kinetic.kineticRowWeight
        rw [Rat.cast_sum]
        simp only [Kinetic.weightTermFin,Rat.cast_abs]
        ring
  have weight : (Kinetic.kineticRowWeight : ℝ) ≤ 200 := by
    exact_mod_cast Kinetic.kinetic_row_weight_bound
  nlinarith

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
