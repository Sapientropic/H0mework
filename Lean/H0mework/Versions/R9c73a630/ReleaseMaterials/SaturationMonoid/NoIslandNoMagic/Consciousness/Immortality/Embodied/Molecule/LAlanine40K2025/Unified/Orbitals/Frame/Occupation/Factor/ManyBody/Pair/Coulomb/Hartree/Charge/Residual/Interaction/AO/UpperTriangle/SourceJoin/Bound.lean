import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Reindex

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def reportWeightedJ (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (reportCoefficientAt address : ℝ) *
      electronRepulsion (targetLeft address.val) (targetRight address.val) i j

def quartetErrorWeight (i j : Basis) : ℝ :=
  ∑ address : Fin 4851,
    (1 / 10^12 : ℝ) *
      |electronRepulsion (targetLeft address.val) (targetRight address.val) i j|

theorem report_weighted_J_error (i j : Basis) :
    |UpperTriangle.sourceJUpper i j - reportWeightedJ i j| ≤
      quartetErrorWeight i j := by
  rw [sourceJ_target_row_sum]
  unfold reportWeightedJ quartetErrorWeight
  calc
    |(∑ address : Fin 4851,
        (sourceCoefficientAt address : ℝ) *
          electronRepulsion (targetLeft address.val) (targetRight address.val) i j) -
      ∑ address : Fin 4851,
        (reportCoefficientAt address : ℝ) *
          electronRepulsion (targetLeft address.val) (targetRight address.val) i j| =
      |∑ address : Fin 4851,
        ((sourceCoefficientAt address : ℝ) - (reportCoefficientAt address : ℝ)) *
          electronRepulsion (targetLeft address.val) (targetRight address.val) i j| := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro address _
        ring
    _ ≤ ∑ address : Fin 4851,
        |((sourceCoefficientAt address : ℝ) - (reportCoefficientAt address : ℝ)) *
          electronRepulsion (targetLeft address.val) (targetRight address.val) i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ address : Fin 4851,
        (1 / 10^12 : ℝ) *
          |electronRepulsion (targetLeft address.val) (targetRight address.val) i j| := by
      apply Finset.sum_le_sum
      intro address _
      rw [abs_mul]
      have bound :
          |(sourceCoefficientAt address : ℝ) - (reportCoefficientAt address : ℝ)| ≤
            (1 / 10^12 : ℝ) := by
        have rational := source_coefficient_report_bound address
        have casted := (Rat.cast_mono (K := ℝ)) (le_of_lt rational)
        simpa using casted
      exact mul_le_mul_of_nonneg_right bound (abs_nonneg _)

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
